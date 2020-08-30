{-# language BangPatterns #-}
{-# language NamedFieldPuns #-}
{-# language LambdaCase #-}
{-# language OverloadedStrings #-}
module LoweredRedo
  ( compileFunction
  , ex1Args
  , ex1Ret
  , ex1Body
  ) where

import Data.Text.Short (ShortText)
import Data.Word (Word32)
import LLVM.AST (Named((:=)))
import GHC.Exts (fromString)
import Control.Monad.Trans.State.Strict (State)
import Data.List.Index (iforM_)
import Data.Foldable (foldlM)

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
  = Val !Value
  | Let !ShortText !NontrivialExpr !Expr
  | Nontrivial !NontrivialExpr

data NontrivialExpr
  = Application !Function [Value]
  | CaseInt
      !Value -- scrutinee
      !WordWidth -- word width of scrutinee
      [Rep] -- result types (as tuple)
      !Expr -- default
      [AlternativeInt] -- alternatives

data AlternativeInt = AlternativeInt !Int !Expr

data Value
  = Var !ShortText !Rep -- identifier
  | Lit Literal    -- constant

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
        [r] -> List.reverse (committedBlocks (State.execState (toBlocksRet e) emptyContext))
        _ -> error "compileFunction: sorry, implement this"
    }
  where
  params = makeParameters args

emptyContext :: Context
emptyContext = Context
  { nextIdent = 0
  , currentBlockId = "beginning"
  , committedInstructions = []
  , committedBlocks = []
  }

data Context = Context
  { nextIdent :: !Word -- next identifier
  , currentBlockId :: !ShortText -- current block name
  , committedInstructions :: ![AST.Named AST.Instruction] -- instruction accumulator
  , committedBlocks :: ![AST.BasicBlock] -- block accumulator
  }

data Result = Result
  !ShortText -- final block labels
  ![AST.Operand] -- named results in this block

data CasePattern = CasePattern
  !Int -- pattern
  !ShortText -- label to beginning of case arm

data CaseResult = CaseResult
  !ShortText -- default label
  ![CasePattern] -- needed by switch instruction
  ![Result] -- needed by landing site that case arms jump to

toBlocksRet :: Expr -> State Context ()
toBlocksRet = go
  where
  go = \case
    Val v -> do
      finish (AST.Do (AST.Ret (Just (valueToOperand v)) []))
    Let var rhs body -> case rhs of
      CaseInt scrutinee scrutineeTy resTy def alts -> do
        rhsCaseToBlocks var scrutinee scrutineeTy resTy def alts
        go body
      Application func args -> do
        let instr = case func of
              UserFunction{} -> error "write user function code"
              BuiltinFunction p -> case p of
                Add _ -> case args of
                  [a,b] -> AST.Add False False (intValueToOperand a) (intValueToOperand b) []
                  _ -> error "panic: add must have exactly two arguments"
                Multiply w -> case args of
                  [a,b] -> AST.Mul False False (intValueToOperand a) (intValueToOperand b) []
                  _ -> error "panic: add must have exactly two arguments"
        instruction (varToName var := instr)
        go body

rhsCaseToBlocks :: 
     ShortText
  -> Value -- scrutinee
  -> WordWidth -- word width of scrutinee
  -> [Rep] -- result types (as tuple)
  -> Expr -- default
  -> [AlternativeInt] -- alternatives
  -> State Context ()
rhsCaseToBlocks var scrutinee scrutineeTy resTy def alts = do
  retLabel <- label ("return.")
  rs <- caseToBlocks retLabel [] scrutinee scrutineeTy resTy def alts
  begin retLabel
  iforM_ resTy $ \i ty -> do
    -- Ahhhh! Indexing into a list is very bad.
    let xs = map (\(Result lbl ys) -> (ys !! i, varToName lbl)) rs
    -- TODO: var should be allowed to be a tuple
    instruction (varToName var := AST.Phi (repToLlvmType ty) xs [])

caseToBlocks :: 
     ShortText -- return label
  -> [Result] -- initial results
  -> Value -- scrutinee
  -> WordWidth -- word width of scrutinee
  -> [Rep] -- result types (as tuple)
  -> Expr -- default
  -> [AlternativeInt] -- alternatives
  -> State Context [Result]
caseToBlocks retLabel rs0 scrutinee scrutineeTy resTy def alts = do
  preceed
    (\(CaseResult defLabel ps rs) -> do
      finish $ AST.Do $ AST.Switch
        (valueToOperand scrutinee)
        (varToName defLabel) (map patternToTuple ps) []
      pure rs
    )
    ( do
      defLabel <- label "def."
      begin defLabel
      r0 <- toBlocks retLabel rs0 def
      (ps,rs) <- foldlM
        (\ (!ps,!rs) (AlternativeInt x e) -> do
          patLabel <- label ("pattern." <> TS.pack (show x) <> ".")
          begin patLabel
          rs' <- toBlocks retLabel rs e
          pure (CasePattern x patLabel : ps,rs')
        ) ([],r0) alts
      pure $! CaseResult defLabel ps rs
    )

-- All of the returned var lists should be of the same length.
-- The ShortTexts are the block labels.
toBlocks :: ShortText -> [Result] -> Expr -> State Context [Result]
toBlocks = go
  where
  go :: ShortText -> [Result] -> Expr -> State Context [Result]
  go !ret !acc = \case
    Val v -> do
      finish (AST.Do (AST.Br (AST.Name (TS.toShortByteString ret)) []))
      blockId <- current
      case v of
        Lit x -> pure (Result blockId [litToOperand x] : acc)
        Var x ty -> pure (Result blockId [varToOperand x ty] : acc)
    Let var rhs body -> case rhs of
      Application func args -> do
        let instr = case func of
              UserFunction{} -> error "write user function code"
              BuiltinFunction p -> case p of
                Add _ -> case args of
                  [a,b] -> AST.Add False False (intValueToOperand a) (intValueToOperand b) []
                  _ -> error "panic: add must have exactly two arguments"
                Multiply w -> case args of
                  [a,b] -> AST.Mul False False (intValueToOperand a) (intValueToOperand b) []
                  _ -> error "panic: add must have exactly two arguments"
        instruction (varToName var := instr)
        go ret acc body
      CaseInt scrutinee scrutineeTy resTy def alts -> do
        rhsCaseToBlocks var scrutinee scrutineeTy resTy def alts
        go ret acc body
    Nontrivial nt -> case nt of
      CaseInt scrutinee scrutineeTy resTy def alts -> do
        caseToBlocks ret acc scrutinee scrutineeTy resTy def alts

finish :: Named AST.Terminator -> State Context ()
finish t = do
  c@Context{committedInstructions,committedBlocks,currentBlockId} <- State.get
  let c' = c
        { committedInstructions = []
        , committedBlocks = AST.BasicBlock
            (AST.Name (TS.toShortByteString currentBlockId))
            (List.reverse committedInstructions)
            t
            :
            committedBlocks
        }
  State.put c'

begin :: ShortText -> State Context ()
begin blockId = do
  c <- State.get
  let c' = c
        { currentBlockId = blockId
        }
  State.put c'

label :: ShortText -> State Context ShortText
label prefix = do
  c@Context{nextIdent} <- State.get
  let c' = c
        { nextIdent = nextIdent + 1
        }
  State.put c'
  pure (prefix <> TS.pack (show nextIdent))

current :: State Context ShortText
current = do
  Context{currentBlockId} <- State.get
  pure currentBlockId

instruction :: AST.Named AST.Instruction -> State Context ()
instruction instr = do
  c@Context{committedInstructions} <- State.get
  let c' = c
        { committedInstructions = instr : committedInstructions
        }
  State.put c'
      
preceed ::
     (a -> State Context b)
  -> State Context a
  -> State Context b
preceed f action = do
  c0 <- State.get
  State.put c0{committedInstructions = [],committedBlocks = []}
  a <- action
  c1 <- State.get
  State.put c0{nextIdent = nextIdent c1}
  b <- f a
  State.modify $ \c -> c
    {committedInstructions = committedInstructions c ++ committedInstructions c1 
    ,committedBlocks = committedBlocks c1 ++ committedBlocks c
    }
  pure b

patternToTuple :: CasePattern -> (C.Constant, AST.Name)
patternToTuple (CasePattern pat lbl) =
  (Constant.Int 32 (fromIntegral pat), varToName lbl)

intValueToOperand :: Value -> AST.Operand
intValueToOperand val = case val of
  Var v rep -> AST.LocalReference (repToLlvmType rep) (AST.Name (TS.toShortByteString v))
  Lit lit -> litToOperand lit

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
  Let "z" (Application (BuiltinFunction (Add W32)) [Var "x" w32r,Var "y" w32r]) $
  Let "w" (Application (BuiltinFunction (Multiply W32)) [Var "y" w32r,Var "z" w32r]) $
  Let "p"
    (CaseInt (Var "w" w32r) W32 [w32r] (Val (Lit (Integer 500 W32)))
      [ AlternativeInt 12 $ Nontrivial
          (CaseInt (Var "w" w32r) W32 [w32r] (Val (Lit (Integer 630 W32)))
            [ AlternativeInt 258 (Val (Lit (Integer 998 W32)))
            , AlternativeInt 109 $
                Let "b" (Application (BuiltinFunction (Multiply W32)) [Var "z" w32r,Lit (Integer 653 W32)]) $
                Val (Var "b" w32r)
            ]
          )
      , AlternativeInt 36 $
          Let "t" (Application (BuiltinFunction (Multiply W32)) [Var "z" w32r,Var "z" w32r]) $
          Val (Var "t" w32r)
      ]
    ) $
  Let "q" (Application (BuiltinFunction (Multiply W32)) [Var "p" w32r,Lit (Integer 55 W32)]) $
  Val (Var "q" w32r)

w32 :: Kind
w32 = Base (Word W32)

w32r :: Rep
w32r = Word W32

varToOperand :: ShortText -> Rep -> AST.Operand
varToOperand v r = (AST.LocalReference (repToLlvmType r) (AST.Name (TS.toShortByteString v)))

varToName :: ShortText -> AST.Name
varToName v = AST.Name (TS.toShortByteString v)

valueToOperand :: Value -> AST.Operand
valueToOperand = \case
  Var v rep -> varToOperand v rep
  Lit x -> litToOperand x
