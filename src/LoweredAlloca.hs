{-# language BangPatterns #-}
{-# language DeriveFoldable #-}
{-# language DuplicateRecordFields #-}
{-# language NamedFieldPuns #-}
{-# language LambdaCase #-}
{-# language OverloadedStrings #-}
{-# language GADTs #-}
{-# language DataKinds #-}
{-# language KindSignatures #-}
{-# language StandaloneDeriving #-}

module LoweredAlloca
  ( compileFunction
  , ex1Args
  , ex1Ret
  , ex1Body
  , ex2Args
  , ex2Ret
  -- , ex2Body
  , ex3Body
  , ex4Body
  , ex5Body
  , allNames
  ) where

import Data.Text.Short (ShortText)
import Data.Word (Word32)
import LLVM.AST (Named((:=)))
import GHC.Exts (fromString)
import Control.Monad.Trans.State.Strict (State)
import Data.List.Index (iforM_)
import Data.Foldable (foldlM,foldl',toList)
import Data.Kind (Type)
import Data.Map.Strict (Map)
import LLVM.AST (BasicBlock(BasicBlock))

import qualified Control.Monad.Trans.State.Strict as State
import qualified Data.List as List
import qualified Data.Text.Short as TS
import qualified Data.Text.Short.Unsafe as TS
import qualified Data.Map.Strict as Map
import qualified LLVM.AST as AST
import qualified LLVM.AST.Constant as Constant
import qualified LLVM.AST.Global as AST
import qualified LLVM.AST.Type as AST
import qualified LLVM.AST.IntegerPredicate as AST
import qualified LLVM.AST.Constant as C
import qualified LLVM.AST.Float as F

data Expr
  = Unit [Value]
    -- ^ Lift a value into an expression
  | Application Function [Value]
    -- ^ Call a function
  | Allocate Constructor [Value]
    -- ^ Allocate node on heap
  | Fetch ShortText Int Rep
    -- ^ Load field of type Rep at offset n from the base pointer.
    -- Base pointer must be of type Boxed.
  | Case CaseExpr
    -- ^ Case on variable. Casing on literal is not supported.
  | Bind ShortText Expr [ShortText] Expr
    -- ^ Serves the purpose of a let binding but has a guarantee
    -- about order of evaluation. First argument is landing label.
  | Join ShortText [ShortText] Expr Expr
    -- ^ Declare a join point.
  | Jump ShortText [Value]
    -- ^ Jump to a join point.
  | Impossible
    -- ^ Compilation fails if this is used. This is needed as the
    -- default when casing on a boolean.

allNames :: Expr -> [ShortText]
allNames = \case
  Bind _ b vars e -> vars ++ allNames b ++ allNames e
  Case (CaseWord _ _ _ _ e alts) -> allNames e ++ do
    AlternativeInt _ _ c <- alts
    allNames c
  Join _ vars b e -> vars ++ allNames b ++ allNames e
  _ -> []

data Constructor
  = ConsW32
  | Nil

data CaseExpr :: Type where
  CaseWord ::
         !Value -- scrutinee
      -> !WordWidth -- word width of scrutinee
      -> ![Rep] -- result types (as tuple)
      -> !ShortText -- label of default
      -> !Expr -- default
      -> [AlternativeInt] -- alternatives
      -> CaseExpr

data AlternativeBool = AlternativeBool
  !ShortText -- Label
  !Expr

data AlternativeInt = AlternativeInt
  !ShortText -- Label
  !Int
  !Expr

data Value
  = Var !ShortText !Rep -- identifier
  | Lit Literal    -- constant

data Literal
  = Integer !Int !WordWidth
  | Boolean !Bool
  | String !ShortText
  | NilList -- the empty list element

data Function
  = Add
  | Sub
  | Lt
  | Multiply

data WordWidth = W8 | W16 | W32 | W64
data FloatWidth = F32 | F64
data Rep = Word WordWidth | Float FloatWidth | Bool | Boxed
data Kind = Base Rep | TupleK [Kind] | Sum [Kind]

flattenKind :: Kind -> [Rep]
flattenKind = \case
  Base r -> [r]
  TupleK xs -> xs >>= flattenKind
  Sum xs -> xs >>= flattenKind

compileFunction :: [(ShortText,Rep)] -> Expr -> [Rep] -> AST.Module
compileFunction args e retKind = AST.Module
  { moduleName = TS.toShortByteString "exampleModule"
  , moduleSourceFileName = TS.toShortByteString "exampleModule.src"
  , moduleDataLayout = Nothing
  , moduleTargetTriple = Nothing
  , moduleDefinitions =
    [ listW32TypeDef
    , funcDef
    ]
  }
  where
  params = makeParameters args
  listW32TypeDef = AST.TypeDefinition
    listW32Name
    (Just $ AST.StructureType
      { isPacked = False
      , elementTypes =
        [ AST.IntegerType 32 -- tag identifying constructor
        , AST.IntegerType 32 -- element, 32-bit word
        , typePtrListW32
        ]
      }
    )
  funcDef = AST.GlobalDefinition AST.functionDefaults
    { AST.name        = "exampleFunction"
    , AST.parameters  = (params, False)
    , AST.returnType  = case retKind of
        [r] -> repToLlvmType r
        _ -> error "compileFunction: sorry, implement this"
    , AST.basicBlocks =
        let fragments = compile "beginning" [] [] Returning e
         in flattenWithPhiNodes (resultsToMap fragments) [] fragments
    }

typePtrListW32 :: AST.Type
typePtrListW32 = AST.ptr (AST.NamedTypeReference listW32Name)

listW32Name :: AST.Name
listW32Name = AST.Name (TS.toShortByteString "list-w32-cons")

resultsToMap :: Tree Fragment -> Map ShortText [Endpoint]
resultsToMap = foldl'
  (\m frag -> case frag of
    BranchMetadata (Results to from args) -> Map.alter
      (\x -> case x of
        Nothing -> Just [Endpoint from args]
        Just xs -> Just (Endpoint from args : xs)
      ) to m
    Block{} -> m
  ) Map.empty

flattenWithPhiNodes ::
     Map ShortText [Endpoint]
  -> [AST.BasicBlock]
  -> Tree Fragment
  -> [AST.BasicBlock]
flattenWithPhiNodes m !acc = \case
  Bin a b -> flattenWithPhiNodes m (flattenWithPhiNodes m acc b) a
  Leaf (Block (PendingBlock argNames (AST.BasicBlock rawName@(AST.Name name) instructions terminator))) -> case Map.lookup (TS.fromShortByteStringUnsafe name) m of
    Nothing -> AST.BasicBlock rawName (List.reverse instructions) terminator : acc
    Just endpoints -> case endpoints of
      Endpoint _ args0 : _ ->
        let len = length args0
         in if length argNames == len
              then
                let phis = foldl'
                      (\accs (Endpoint from args) -> zipConsExact (map (\val -> (valueToOperand val,AST.Name (TS.toShortByteString from))) args) accs)
                      (replicate len [])
                      endpoints
                    phiNodes = zipWithExact (\argName x -> AST.Name (TS.toShortByteString argName) := (AST.Phi (AST.IntegerType 32) x [])) argNames phis
                 in AST.BasicBlock rawName (phiNodes ++ List.reverse instructions) terminator : acc
              else error "flattenWithPhiNodes: length mismatch"
      [] -> AST.BasicBlock rawName (List.reverse instructions) terminator : acc
  Leaf (BranchMetadata{}) -> acc

zipExactStore ::
     [Value]
  -> [ShortText]
  -> [Named AST.Instruction]
  -> [Named AST.Instruction]
zipExactStore [] [] !instrs = instrs
zipExactStore (val : vals) (var : vars) !instrs =
  let instr = AST.Store
        { volatile = False 
          -- TODO: address type is bad
        , address = AST.LocalReference typePtrListW32 (heapPointerList 1)
        , value = valueToOperand val
        , maybeAtomicity = Nothing
        , alignment = 8
        , metadata = []
        }
   in zipExactStore vals vars (AST.Do instr : instrs)
zipExactStore _ _ !_ = error "zipExactStore: must match"


zipWithExact :: (a -> b -> c) -> [a] -> [b] -> [c]
zipWithExact f [] [] = []
zipWithExact f (a : as) (b : bs) = f a b : zipWithExact f as bs

zipConsExact ::
     [a] -- of length n
  -> [[a]] -- outer list length n, inner list any length
  -> [[a]]
zipConsExact [] [] = []
zipConsExact (a : as) (acc : accs) = (a : acc) : zipConsExact as accs
zipConsExact _ _ = error "zipConsExact: must match"

flattenTree :: Tree a -> [a] -> [a]
flattenTree t acc = case t of
  Leaf x -> x : acc
  Bin a b -> flattenTree a (flattenTree b acc)

data Tree a
  = Bin (Tree a) (Tree a)
  | Leaf a
  deriving (Foldable)

data PendingBlock = PendingBlock [ShortText] AST.BasicBlock

data Results = Results
  !ShortText -- join point
  !ShortText -- where we jumped from
  [Value] -- arguments

data Endpoint = Endpoint
  !ShortText -- where we jumped from
  [Value] -- arguments

data Context
  = Returning
  | Branching
      !ShortText -- label
      [ShortText] -- names of alloca pointers to assign results to

data Fragment
  = Block PendingBlock
  | BranchMetadata Results

node ::
     ShortText
  -> [AST.Named AST.Instruction]
  -> AST.Terminator
  -> Tree BasicBlock
node label instrs t = Leaf
  (AST.BasicBlock
    (AST.Name (TS.toShortByteString label))
    instrs
    (AST.Do t)
  )

-- Resulting instructions are deliberately backwards in each block.
compile ::
     ShortText -- Pending label, reader-like
  -> [AST.Named AST.Instruction] -- Pending instructions, writer-like
  -> Context -- Which LLVM instruction will the terminator be: ret or br
  -> Expr -- Expression, the thing actually being compiled
  -> Tree AST.BasicBlock
compile !pendingLabel !pendingInstructions !ctx = \case
  Application{} -> error "compile: Application in bad position"
  Allocate{} -> error "compile: Allocate in bad position"
  Unit v -> case ctx of
    Returning -> case v of
      [v0] -> node
        pendingLabel pendingInstructions
        (AST.Ret (Just (valueToOperand v0)) [])
      _ -> error "compile: sorry, figure this out"
    Branching label args ->
      let instrs = zipExactStore v args pendingInstructions
       in Leaf $ BasicBlock (varToName pendingLabel) instrs
            (AST.Br (AST.Name (TS.toShortByteString label)) [])
  Join joinLabel args rhs body -> Bin
    (compile pendingLabel pendingInstructions Returning body)
    (compile joinLabel args [] ctx rhs)
  Jump label args -> Bin
    (BasicBlock pendingLabel pendingInstructions
      (AST.Br (AST.Name (TS.toShortByteString label)) [])
    )
    (Leaf (BranchMetadata (Results label pendingLabel args)))
  Case (CaseWord scrutinee scrutineeTy resTy defLabel def alts) ->
    let committedBlock = BasicBlock pendingLabel pendingInstructions
          (AST.Switch
            (valueToOperand scrutinee) (varToName defLabel) (map altToLabel alts) []
          )
        defBuilder = compile defLabel [] [] ctx def
        r = foldl'
          (\leftBuilder (AlternativeInt label pat e) ->
            let rightBuilder = compile label [] [] ctx e
             in Bin leftBuilder rightBuilder
          ) (Bin (Leaf committedBlock) defBuilder) alts
     in r
  Bind landingLabel rhs vars body -> case rhs of
    Application func args -> case vars of
      [var] -> 
        let instr = makeFunction1 var func args
         in compile pendingLabel (instr : pendingInstructions) ctx body
    Allocate ctor args -> case ctor of
      ConsW32 -> case args of
        [x,xs] ->
          let size = 3 :: Int -- size in machine words
              bump = heapPointerName 2 := AST.GetElementPtr
                { inBounds = True
                , address = heapPointerOperand 1
                , indices = [AST.ConstantOperand (Constant.Int 32 (fromIntegral size))]
                , metadata = []
                }
              castHeapPtrInstr = heapPointerList 1 := AST.BitCast
                { operand0 = heapPointerOperand 1
                , type' = typePtrListW32
                , metadata = []
                }
              computeElementAddr = listElementName 1 := AST.GetElementPtr
                { inBounds = True
                , address = AST.LocalReference typePtrListW32 (heapPointerList 1)
                , indices = [AST.ConstantOperand (Constant.Int 64 0), AST.ConstantOperand (Constant.Int 32 1)]
                , metadata = []
                }
           -- in compile pendingLabel pendingArgs (bump : assignInfo : assignElement : assignTail : pendingInstructions) ctx body
           in compile pendingLabel (bump : computeElementAddr : castHeapPtrInstr : pendingInstructions) ctx body
        _ -> error "compile: ConsW32 has wrong number of arguments"
    -- _ -> Bin
    --   (compile pendingLabel pendingInstructions (Branching landingLabel vars) rhs)
    --   (compile landingLabel [] vars ctx body)

makeFunction1 ::
     ShortText
  -> Function
  -> [Value]
  -> AST.Named AST.Instruction
makeFunction1 var func args = case func of
  Add -> case args of
    [a,b] ->
      let instr = AST.Add False False (intValueToOperand a) (intValueToOperand b) []
       in varToName var := instr
  Sub -> case args of
    [a,b] ->
      let instr = AST.Sub False False (intValueToOperand a) (intValueToOperand b) []
       in varToName var := instr
  Lt -> case args of
    [a,b] ->
      let instr = AST.ICmp AST.ULT (intValueToOperand a) (intValueToOperand b) []
       in varToName var := instr
  Multiply -> case args of
    [a,b] ->
      let instr = AST.Mul False False (intValueToOperand a) (intValueToOperand b) []
       in varToName var := instr

altToLabel :: AlternativeInt -> (C.Constant, AST.Name)
altToLabel (AlternativeInt lbl pat _) =
  (Constant.Int 32 (fromIntegral pat), varToName lbl)

valueToOperand :: Value -> AST.Operand
valueToOperand = \case
  Var v rep -> varToOperand v rep
  Lit x -> litToOperand x

varToOperand :: ShortText -> Rep -> AST.Operand
varToOperand v r = (AST.LocalReference (repToLlvmType r) (AST.Name (TS.toShortByteString v)))

listElementName :: Int -> AST.Name
listElementName n = AST.Name (TS.toShortByteString ("hp.list-w32-elem." <> TS.pack (show n)))

heapPointerList :: Int -> AST.Name
heapPointerList n = AST.Name (TS.toShortByteString ("hp.list." <> TS.pack (show n)))

heapPointerName :: Int -> AST.Name
heapPointerName n = AST.Name (TS.toShortByteString ("hp" <> TS.pack (show n)))

heapPointerOperand :: Int -> AST.Operand
heapPointerOperand n = AST.LocalReference (AST.ptr (AST.IntegerType 64)) (AST.Name (TS.toShortByteString ("hp" <> TS.pack (show n))))

repToLlvmType :: Rep -> AST.Type
repToLlvmType = \case
  Word w -> wordWidthToIntegerType w
  Bool -> AST.IntegerType 1

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

litToOperand :: Literal -> AST.Operand
litToOperand = \case
  Integer i w -> AST.ConstantOperand (Constant.Int (wordWidthToNumber w) (fromIntegral i))

makeParameters :: [(ShortText,Rep)] -> [AST.Parameter]
makeParameters atoms = map
  (\(var,atom) -> do
    AST.Parameter (repToLlvmType atom) (AST.Name (TS.toShortByteString var)) []
  )
  atoms

varToName :: ShortText -> AST.Name
varToName v = AST.Name (TS.toShortByteString v)

intValueToOperand :: Value -> AST.Operand
intValueToOperand val = case val of
  Var v rep -> AST.LocalReference (repToLlvmType rep) (AST.Name (TS.toShortByteString v))
  Lit lit -> litToOperand lit

ex1Args :: [(ShortText,Rep)]
ex1Args = [("x",Word W32),("y",Word W32)]

ex2Args :: [(ShortText,Rep)]
ex2Args = [("n",Word W32)]

ex1Ret :: [Rep]
ex1Ret = [Word W32]

ex2Ret :: [Rep]
ex2Ret = [Word W32]

w32r :: Rep
w32r = Word W32

valuesToOperand :: [Value] -> AST.Operand
valuesToOperand = \case
  [x] -> valueToOperand x
  _ -> error "valuesToOperand: write this"

ex5Body :: Expr
ex5Body =
  Bind "land.0" (Application Add [Var "x" w32r,Var "y" w32r]) ["z"] $
  Bind "land.1" (Allocate ConsW32 [Lit (Integer 507 W32), Lit NilList]) ["b"] $
  Unit [Var "x" w32r]

ex4Body :: Expr
ex4Body =
  Bind "land.0" (Application Add [Var "x" w32r,Var "y" w32r]) ["z"] $
  Bind "land.1" other ["a"] $ Unit [Var "a" w32r]
  where
  other =
    Bind "land.2" (Application Sub [Var "z" w32r,Lit (Integer 50 W32)]) ["b"] $
    Bind "land.3" (Application Sub [Var "b" w32r,Var "x" w32r]) ["c"] $
    Unit [Var "c" w32r]

ex1Body :: Expr
ex1Body =
  Bind "land.2" (Application Add [Var "x" w32r,Var "y" w32r]) ["z"] $
  Bind "land.3" (Application Multiply [Var "y" w32r,Var "z" w32r]) ["w"] $
  Bind "land.4"
    (Case $ CaseWord (Var "w" w32r) W32 [w32r] "case.alpha.default" (Unit [Lit (Integer 500 W32)])
      [ AlternativeInt "case.12" 12 (Unit [Lit (Integer 200 W32)])
      , AlternativeInt "case.36" 36 $
          Bind "land.5" (Application Multiply [Var "z" w32r,Var "z" w32r]) ["t"] $
          Unit [Var "t" w32r]
      ]
    ) ["p"] $
  Bind "land.6" (Application Multiply [Var "p" w32r,Lit (Integer 55 W32)]) ["q"] $
  Unit [Var "q" w32r]

-- ex2Body :: Expr
-- ex2Body =
--   Join "loop" ["i","c"]
--     ( Bind (Application Lt [Lit (Integer 0 W32), Var "i" w32r]) ["b"]
--     $ Case $ CaseBool "case.cond.landing" (Var "b" Bool) [w32r] 
--       ( AlternativeBool "case.false"
--       $ Unit [Var "c" w32r]
--       )
--       ( AlternativeBool "case.true"
--       $ Bind (Application Sub [Var "i" w32r, Lit (Integer 1 W32)]) ["ipred"]
--       $ Bind (Application Multiply [Var "i" w32r, Var "c" w32r]) ["cnext"]
--       $ Jump "loop" [Var "ipred" w32r, Var "cnext" w32r]
--       )
--     )
--   $ Jump "loop" [Var "n" w32r,Lit (Integer 1 W32)]
-- 
ex3Body :: Expr
ex3Body =
  Join "loop" ["i","c"]
    ( Bind "bind.0" (Application Lt [Lit (Integer 0 W32), Var "i" w32r]) ["b"]
    $ Case $ CaseWord (Var "i" w32r) W32 [w32r] "case.default"
      ( id
      $ Bind "bind.1" (Application Sub [Var "i" w32r, Lit (Integer 1 W32)]) ["ipred"]
      $ Bind "bind.2" (Application Multiply [Var "i" w32r, Var "c" w32r]) ["cnext"]
      $ Jump "loop" [Var "ipred" w32r, Var "cnext" w32r]
      )
      [ AlternativeInt "case.0" 0 (Unit [Var "c" w32r]) ]
    )
  $ Jump "loop" [Var "n" w32r,Lit (Integer 1 W32)]
  
--   Bind (Application Add [Var "x" w32r,Var "y" w32r]) ["z"] $
--   Bind (Application Multiply [Var "y" w32r,Var "z" w32r]) ["w"] $
--   Bind
--     (Case $ CaseWord "case.alpha.landing" (Var "w" w32r) W32 [w32r] "case.alpha.default" (Unit (Lit (Integer 500 W32)))
--       [ AlternativeInt "case.12" 12 (Unit (Lit (Integer 200 W32)))
--       , AlternativeInt "case.36" 36 $
--           Bind (Application Multiply [Var "z" w32r,Var "z" w32r]) ["t"] $
--           Unit (Var "t" w32r)
--       ]
--     ) ["p"] $
--   Bind (Application Multiply [Var "p" w32r,Lit (Integer 55 W32)]) ["q"] $
--   Unit (Var "q" w32r)

