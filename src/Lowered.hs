{-# language BangPatterns #-}
{-# language LambdaCase #-}
{-# language OverloadedStrings #-}
module Lowered
  ( compileFunction
  , ex1Args
  , ex1Ret
  , ex1Body
  ) where

import Data.Text.Short (ShortText)
import Data.Word (Word32)
import LLVM.AST (Named((:=)))
import GHC.Exts (fromString)

import qualified Control.Monad.Trans.State.Strict as State
import qualified Data.List as List
import qualified Data.Text.Short as TS
import qualified LLVM.AST as AST
import qualified LLVM.AST.Constant as Constant
import qualified LLVM.AST.Global as AST
import qualified LLVM.AST.Type as AST
import qualified LLVM.AST.IntegerPredicate as AST
import qualified LLVM.AST.Constant as C
import qualified LLVM.AST.Float as F

data Expr
  = Val Value
  | Let !ShortText !Assignment Expr

data Assignment
  = Application !Function [Value]
  | CaseInt
      !Value -- scrutinee
      !WordWidth -- word width of scrutinee
      !Expr -- default
      [AlternativeInt] -- alternatives

data AlternativeInt = AlternativeInt !Int !Expr

data Value
  = Var !ShortText
  | Lit Literal

data Literal
  = Integer !Int !WordWidth
  | Boolean !Bool
  | String !ShortText

data Function
  = UserFunction !ShortText
  | BuiltinFunction PrimFunc

data PrimFunc
  = Add !WordWidth
  | Multiply !WordWidth

data WordWidth = W8 | W16 | W32 | W64
data FloatWidth = F32 | F64
data Rep = Word WordWidth | Float FloatWidth | Boxed
data Kind = Base Rep | TupleK [Kind] | Sum [Kind]

flattenKind :: Kind -> [Rep]
flattenKind = \case
  Base r -> [r]
  TupleK xs -> xs >>= flattenKind
  Sum xs -> xs >>= flattenKind

compileFunction :: [(ShortText,Rep)] -> Expr -> [Rep] -> AST.Definition
compileFunction args e retKind =
  AST.GlobalDefinition AST.functionDefaults
    { AST.name        = "exampleFunction"
    , AST.parameters  = (params, False)
    , AST.returnType  = case retKind of
        [r] -> repToLlvmType r
        _ -> error "compileFunction: sorry, implement this"
    , AST.basicBlocks = case retKind of
        [r] -> List.reverse (compileBody e r)
        _ -> error "compileFunction: sorry, implement this"
    }
  where
  params = makeParameters args

compileBody :: Expr -> Rep -> [AST.BasicBlock]
compileBody e0 retKind = go e0 Nothing "start" [] []
  where
  go :: Expr
     -> Maybe ShortText -- Just if jumping to local block
     -> ShortText -- name of current block
     -> [AST.Named AST.Instruction] -- instruction accumulator
     -> [AST.BasicBlock] -- block accumulator
     -> [AST.BasicBlock]
  go (Val v) !mbranch !bname !instrs !blocks = case v of
    Lit x -> 
      let terminator = case mbranch of
            Nothing -> AST.Do (AST.Ret (Just (litToOperand x)) [])
            Just branch -> AST.Do (AST.Br (AST.Name (TS.toShortByteString branch)) [])
          instrs' = case mbranch of
            Nothing -> instrs
            Just branch -> instrs
              -- (AST.Name (TS.toShortByteString branch) := litToOperand x) : instrs
       in AST.BasicBlock
            (AST.Name (TS.toShortByteString bname))
            (List.reverse instrs')
            terminator
            :
            blocks
    Var x ->
      let instr = case mbranch of
            Nothing -> AST.Do (AST.Ret (Just (AST.LocalReference (repToLlvmType retKind) (AST.Name (TS.toShortByteString x)))) [])
            Just branch -> AST.Do (AST.Br (AST.Name (TS.toShortByteString branch)) [])
       in AST.BasicBlock
            (AST.Name (TS.toShortByteString bname))
            (List.reverse instrs)
            instr
            :
            blocks
  go (Let v asgn e) !mbranch !bname !instrs !blocks = case asgn of
    CaseInt val w def alts ->
      let switchInstr = AST.Switch
            (intValueToOperand val w)
            (AST.Name "case.default")
            (map
              (\(AlternativeInt pat arm) ->
                ( Constant.Int (wordWidthToNumber w) (fromIntegral pat)
                , AST.Name (fromString ("case." ++ show pat))
                )
              )
              alts
            )
            []
          block = AST.BasicBlock
            (AST.Name (TS.toShortByteString bname))
            (List.reverse instrs)
            (AST.Do switchInstr)
          bname' = bname <> "+"
          armBlocks = alts >>=
            (\(AlternativeInt pat arm) -> go arm (Just bname') (fromString ("case." ++ show pat)) [] [])
       in go e mbranch bname' [] (armBlocks ++ (block : blocks))
    Application func args ->
      let instr = case func of
            UserFunction{} -> error "write user function code"
            BuiltinFunction p -> case p of
              Add w -> case args of
                [a,b] -> AST.Add False False (intValueToOperand a w) (intValueToOperand b w) []
                _ -> error "panic: add must have exactly two arguments"
              Multiply w -> case args of
                [a,b] -> AST.Mul False False (intValueToOperand a w) (intValueToOperand b w) []
                _ -> error "panic: add must have exactly two arguments"
       in go e mbranch bname ((AST.Name (TS.toShortByteString v) := instr) : instrs) blocks

intValueToOperand :: Value -> WordWidth -> AST.Operand
intValueToOperand val w = case val of
  Var v -> AST.LocalReference ty (AST.Name (TS.toShortByteString v))
  Lit lit -> litToOperand lit
  where
  ty = wordWidthToIntegerType w

litToOperand :: Literal -> AST.Operand
litToOperand = \case
  Integer i w -> AST.ConstantOperand (Constant.Int (wordWidthToNumber w) (fromIntegral i))

makeParameters :: [(ShortText,Rep)] -> [AST.Parameter]
makeParameters atoms = map
  (\(var,atom) -> do
    AST.Parameter (repToLlvmType atom) (AST.Name (TS.toShortByteString var)) []
  )
  atoms

wordWidthToNumber :: WordWidth -> Word32
wordWidthToNumber = \case
  W8 -> 8
  W16 -> 16
  W32 -> 32
  W64 -> 64
 
wordWidthToIntegerType :: WordWidth -> AST.Type
wordWidthToIntegerType = \case
  W8 -> AST.IntegerType 8
  W16 -> AST.IntegerType 16
  W32 -> AST.IntegerType 32
  W64 -> AST.IntegerType 64

repToLlvmType :: Rep -> AST.Type
repToLlvmType = \case
  Word w -> wordWidthToIntegerType w

kindToLlvmType :: Kind -> AST.Type
kindToLlvmType = \case
  Base r -> repToLlvmType r
  _ -> error "kindToLlvmType: sorry, write this"

ex1Args :: [(ShortText,Rep)]
ex1Args = [("x",Word W32),("y",Word W32)]

ex1Ret :: [Rep]
ex1Ret = [Word W32]

ex1Body :: Expr
ex1Body =
  Let "z" (Application (BuiltinFunction (Add W32)) [Var "x",Var "y"]) $
  Let "w" (Application (BuiltinFunction (Multiply W32)) [Var "y",Var "z"]) $
  Let "p"
    (CaseInt (Var "w") W32 (Val (Lit (Integer 500 W32)))
      [ AlternativeInt 12 (Val (Lit (Integer 200 W32)))
      , AlternativeInt 36 $
          Let "t" (Application (BuiltinFunction (Multiply W32)) [Var "z",Var "z"]) $
          Val (Var "t")
      ]
    ) $
  Let "q" (Application (BuiltinFunction (Multiply W32)) [Var "p",Lit (Integer 55 W32)]) $
  Val (Var "q")

w32 :: Kind
w32 = Base (Word W32)
