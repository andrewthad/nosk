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

module LoweredGrinJoin
  ( compileFunction
  , ex1Args
  , ex1Ret
  , ex1Body
  , ex2Args
  , ex2Ret
  , ex2Body
  , ex3Body
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

-- General Ideas:
--
-- All tuples have already been desugared. When you bind to a tuple,
-- you must bind multiple identifiers. Sums have been desugared to
-- tuples and do not exist at this stage. Tuple size is tracked
-- explicitly in the type system. This adds a little cognitive overhead
-- when dealing with join points.
--
-- There is not a good way to caputure the invariant that a join point
-- declaration and its corresponding jumps all have the same number of
-- arguments. Doing this requires an arity-tracking variant of De Bruijn
-- indices. It's possible, but it would complicate the implementation
-- considerably. Rather than enforce this in the type system, we dynamically
-- check for an arity match whenever a jump is encountered. This means
-- that we must keep track of in-scope join points as a map. This is
-- precisely the kind of context I was hoping to avoid.
--
-- Perhaps instead join points could all be removed. If variables have
-- already been given unique names, it should be possible to remove
-- join point definitions while leaving all the jumps in the source.
-- Then we could compile all the non-join-point code, collecting the
-- jump information (for phi nodes in the join point declarations) as
-- we go. We would need several tiers since join points can jump to
-- other join points. Tier 9 would just be the function with no join
-- point declarations. It could have jumps to Tier 8 or Tier 7 or any
-- lower number. Tier 8 would be join points. The may jump to Tier 7
-- or to lower tiers. Tier 7 would be similar. Finally, some lowest
-- tier would be the join points that had no jumps at all. To compile
-- a join point to LLVM, you have to know everything that jumps to it.
-- So, we start at Tier 9 and work our way down to the bottom.
--
-- So, what's the strategy for doing this? Before we even start on generating
-- LLVM IR, we need to scan the entire expression for all join point
-- declarations and make a map for them. With the map in place, we can
-- start on Tier 9. As we build IR, we update the map with any jumps we
-- encounter. While updating the map, we check that the arity of the jump
-- matches the arity of the corresponding join point, failing loudly if
-- there is a mismatch. When we arrive at a join point declaration in a lower
-- tier, we remove the join point from the map.
--
-- Adding recursive join points makes this a little more complicated.
-- As envisioned above, join points in a tier could not jump to other
-- join points in the same tier. Supporting recursive join points is
-- extremely important since that's how tail recursion should be compiled.
-- How can it be done? We need to know all incoming arguments before we
-- start compiling a join point (phi nodes come first), but we in the
-- case of a recursive binding, we do not have this information.
--
-- Perhaps we could go about the whole process differently. Rather than
-- generating LLVM IR in a single pass, we could generate a data structure
-- that roughly means "a block missing phi nodes". As we generate these
-- blocks, we also generate the "A jumps to B with arguments X,Y,Z" map.
-- And then we simply synthesize the real blocks from these and the
-- incomplete per-block instructions at the end. This would unify the
-- treatment of join points and let-case-rhs. We would probably stop tracking
-- length at the type level if we did this.

data Expr
  = Unit Value
    -- ^ Lift a value into an expression
  | Application Function [Value]
    -- ^ Call a function
  | Store Constructor [Value]
    -- ^ Allocate node on heap
  | Fetch ShortText Int Rep
    -- ^ Load field of type Rep at offset n from the base pointer.
    -- Base pointer must be of type Boxed.
  | Case CaseExpr
    -- ^ Case on variable. Casing on literal is not supported.
  | Bind Expr [ShortText] Expr
    -- ^ Serves the purpose of a let binding but has a guarantee
    -- about order of evaluation.
  | Join ShortText [ShortText] Expr Expr
    -- ^ Declare a join point.
  | Jump ShortText [Value]
    -- ^ Jump to a join point.
  | Impossible
    -- ^ Compilation fails if this is used. This is needed as the
    -- default when casing on a boolean.

data CaseExpr :: Type where
  CaseWord ::
         !ShortText -- landing label 
      -> !Value -- scrutinee
      -> !WordWidth -- word width of scrutinee
      -> ![Rep] -- result types (as tuple)
      -> !ShortText -- label of default
      -> !Expr -- default
      -> [AlternativeInt] -- alternatives
      -> CaseExpr
  CaseBool ::
         !ShortText -- landing label 
      -> !Value -- scrutinee
      -> ![Rep] -- result types (as tuple)
      -> !AlternativeBool -- false alternative
      -> !AlternativeBool -- true alternative
      -> CaseExpr

data Constructor = Constructor

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

compileFunction :: [(ShortText,Rep)] -> Expr -> [Rep] -> AST.Definition
compileFunction args e retKind = 
  AST.GlobalDefinition AST.functionDefaults
    { AST.name        = "exampleFunction"
    , AST.parameters  = (params, False)
    , AST.returnType  = case retKind of
        [r] -> repToLlvmType r
        _ -> error "compileFunction: sorry, implement this"
    , AST.basicBlocks = case retBlocks "beginning" [] [] e of
        (incompleteBlocks,jumps) -> flattenWithPhiNodes (resultsToMap jumps) [] incompleteBlocks
    }
  where
  params = makeParameters args

resultsToMap :: Tree Results -> Map ShortText [Endpoint]
resultsToMap = foldl'
  (\m (Results to from args) -> Map.alter
    (\x -> case x of
      Nothing -> Just [Endpoint from args]
      Just xs -> Just (Endpoint from args : xs)
    ) to m
  ) Map.empty

flattenWithPhiNodes ::
     Map ShortText [Endpoint]
  -> [AST.BasicBlock]
  -> Tree PendingBlock
  -> [AST.BasicBlock]
flattenWithPhiNodes m !acc = \case
  Nil -> []
  Bin a b -> flattenWithPhiNodes m (flattenWithPhiNodes m acc b) a
  Leaf (PendingBlock argNames (AST.BasicBlock rawName@(AST.Name name) instructions terminator)) -> case Map.lookup (TS.fromShortByteStringUnsafe name) m of
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
  | Nil
  deriving (Foldable)

data PendingBlock = PendingBlock [ShortText] AST.BasicBlock

data Results = Results
  !ShortText -- join point
  !ShortText -- where we jumped from
  [Value] -- arguments

data Endpoint = Endpoint
  !ShortText -- where we jumped from
  [Value] -- arguments

-- Resulting instructions are deliberately backwards in each block.
retBlocks ::
     ShortText -- pending label
  -> [AST.Named AST.Instruction] -- pending instructions
  -> [ShortText] -- pending argument names for phi nodes
  -> Expr -- expression
  -> (Tree PendingBlock, Tree Results)
retBlocks !pendingLabel !pendingInstructions !pendingArgs = \case
  Unit v ->
    (Leaf $ PendingBlock pendingArgs
      (AST.BasicBlock
        (AST.Name (TS.toShortByteString pendingLabel))
        pendingInstructions
        (AST.Do (AST.Ret (Just (valueToOperand v)) []))
      )
    , Nil
    )
  Join joinLabel args rhs body ->
    let (bs1,rs1) = retBlocks pendingLabel pendingInstructions pendingArgs body
        (bs2,rs2) = retBlocks joinLabel [] args rhs
     in (Bin bs1 bs2, Bin rs1 rs2)
  Jump label args ->
    ( Leaf $ PendingBlock pendingArgs
      (AST.BasicBlock
        (AST.Name (TS.toShortByteString pendingLabel))
        pendingInstructions
        (AST.Do (AST.Br (AST.Name (TS.toShortByteString label)) []))
      )
    , Leaf (Results label pendingLabel args)
    )
  Case (CaseBool _ scrutinee resTy falseAlt trueAlt) ->
    let AlternativeBool falseLabel falseExpr = falseAlt
        AlternativeBool trueLabel trueExpr = trueAlt
        (falseBlock,falseResults) = retBlocks falseLabel [] [] falseExpr
        (trueBlock,trueResults) = retBlocks trueLabel [] [] trueExpr
        condBlock = Bin trueBlock falseBlock 
        condResults = Bin trueResults falseResults 
        committedBlock = PendingBlock pendingArgs $ AST.BasicBlock
          (AST.Name (TS.toShortByteString pendingLabel))
          pendingInstructions
          (AST.Do $ AST.CondBr
            (valueToOperand scrutinee) (varToName trueLabel) (varToName falseLabel) []
          )
     in (Bin (Leaf committedBlock) condBlock, condResults)
  Case (CaseWord _ scrutinee scrutineeTy resTy defLabel def alts) ->
    let committedBlock = PendingBlock pendingArgs $ AST.BasicBlock
          (AST.Name (TS.toShortByteString pendingLabel))
          pendingInstructions
          (AST.Do $ AST.Switch
            (valueToOperand scrutinee) (varToName defLabel) (map altToLabel alts) []
          )
        (defBlock,defResults) = retBlocks defLabel [] [] def
        (mostBlocks,mostJumps) = foldl'
          (\(accA,accB) (AlternativeInt label pat e) ->
            let (a,b) = retBlocks label [] [] e
             in (Bin accA a, Bin accB b)
          ) (Bin (Leaf committedBlock) defBlock,defResults) alts
     in (mostBlocks, mostJumps)
  Bind rhs vars body -> case rhs of
    Application func args -> case vars of
      [var] -> 
        let instr = makeFunction1 var func args
         in retBlocks pendingLabel (instr : pendingInstructions) pendingArgs body
    Case (CaseBool landingLabel scrutinee resTy falseAlt trueAlt) ->
      let AlternativeBool falseLabel falseExpr = falseAlt
          AlternativeBool trueLabel trueExpr = trueAlt
          (falseBlock,falseResults) = retBlocks falseLabel [] [] falseExpr
          (trueBlock,trueResults) = retBlocks trueLabel [] [] trueExpr
          condBlock = Bin trueBlock falseBlock 
          condResults = Bin trueResults falseResults 
          committedBlock = PendingBlock pendingArgs $ AST.BasicBlock
            (AST.Name (TS.toShortByteString pendingLabel))
            pendingInstructions
            (AST.Do $ AST.CondBr
              (valueToOperand scrutinee) (varToName trueLabel) (varToName falseLabel) []
            )
          (remainingBlocks,remainingJumps) = retBlocks landingLabel [] vars body
          followingBlocks = Bin condBlock remainingBlocks
       in (Bin (Leaf committedBlock) followingBlocks, Bin condResults remainingJumps)
    Case (CaseWord landingLabel scrutinee scrutineeTy resTy defLabel def alts) ->
      let committedBlock = PendingBlock pendingArgs $ AST.BasicBlock
            (AST.Name (TS.toShortByteString pendingLabel))
            pendingInstructions
            (AST.Do $ AST.Switch
              (valueToOperand scrutinee) (varToName defLabel) (map altToLabel alts) []
            )
          (defBlock,defResults) = retBlocks defLabel [] [] def
          (mostBlocks,mostJumps) = foldl'
            (\(accA,accB) (AlternativeInt label pat e) ->
              let (a,b) = retBlocks label [] [] e
               in (Bin accA a, Bin accB b)
            ) (Bin (Leaf committedBlock) defBlock,defResults) alts
          (remainingBlocks,remainingJumps) = retBlocks landingLabel [] vars body
       in (Bin mostBlocks remainingBlocks, Bin mostJumps remainingJumps)

makeSwitchTerminatedBlock ::
     ShortText
  -> [Named AST.Instruction]
  -> Value
  -> ShortText
  -> [AlternativeInt]
  -> AST.BasicBlock
makeSwitchTerminatedBlock pendingLabel pendingInstructions scrutinee defLabel alts = 
  AST.BasicBlock
    (AST.Name (TS.toShortByteString pendingLabel))
    (List.reverse pendingInstructions)
    (AST.Do $ AST.Switch
      (valueToOperand scrutinee) (varToName defLabel) (map altToLabel alts) []
    )

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

ex1Body :: Expr
ex1Body =
  Bind (Application Add [Var "x" w32r,Var "y" w32r]) ["z"] $
  Bind (Application Multiply [Var "y" w32r,Var "z" w32r]) ["w"] $
  Bind
    (Case $ CaseWord "case.alpha.landing" (Var "w" w32r) W32 [w32r] "case.alpha.default" (Unit (Lit (Integer 500 W32)))
      [ AlternativeInt "case.12" 12 (Unit (Lit (Integer 200 W32)))
      , AlternativeInt "case.36" 36 $
          Bind (Application Multiply [Var "z" w32r,Var "z" w32r]) ["t"] $
          Unit (Var "t" w32r)
      ]
    ) ["p"] $
  Bind (Application Multiply [Var "p" w32r,Lit (Integer 55 W32)]) ["q"] $
  Unit (Var "q" w32r)

ex2Body :: Expr
ex2Body =
  Join "loop" ["i","c"]
    ( Bind (Application Lt [Lit (Integer 0 W32), Var "i" w32r]) ["b"]
    $ Case $ CaseBool "case.cond.landing" (Var "b" Bool) [w32r] 
      ( AlternativeBool "case.false"
      $ Unit (Var "c" w32r)
      )
      ( AlternativeBool "case.true"
      $ Bind (Application Sub [Var "i" w32r, Lit (Integer 1 W32)]) ["ipred"]
      $ Bind (Application Multiply [Var "i" w32r, Var "c" w32r]) ["cnext"]
      $ Jump "loop" [Var "ipred" w32r, Var "cnext" w32r]
      )
    )
  $ Jump "loop" [Var "n" w32r,Lit (Integer 1 W32)]

ex3Body :: Expr
ex3Body =
  Join "loop" ["i","c"]
    ( Bind (Application Lt [Lit (Integer 0 W32), Var "i" w32r]) ["b"]
    $ Case $ CaseWord "case.landing" (Var "i" w32r) W32 [w32r] "case.default"
      ( id
      $ Bind (Application Sub [Var "i" w32r, Lit (Integer 1 W32)]) ["ipred"]
      $ Bind (Application Multiply [Var "i" w32r, Var "c" w32r]) ["cnext"]
      $ Jump "loop" [Var "ipred" w32r, Var "cnext" w32r]
      )
      [ AlternativeInt "case.0" 0 (Unit (Var "c" w32r)) ]
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
