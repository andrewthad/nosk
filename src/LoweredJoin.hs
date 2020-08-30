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

module LoweredJoin
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
import Data.Foldable (foldlM,foldl',toList)
import Data.Kind (Type)

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
-- And then we simply synthesize these with the per-block instructions
-- at the end. This would unify the treatment of join points and let-case-rhs.
-- We would probably stop tracking length at the type level if we did this.
data Expr :: Nat -> Type where
  Val :: Vec n Value -> Expr n
  -- Note: This LET can only bind values not functions.
  Let :: Vec m ShortText -> !(NontrivialExpr m) -> Expr n -> Expr n
  CaseIntExpr :: !(CaseExpr n) -> Expr n

data Nat = Succ Nat | Zero

data Vec :: Nat -> Type -> Type where
  VecCons :: a -> Vec n a -> Vec ('Succ n) a
  VecNil :: Vec 'Zero a

deriving instance Foldable (Vec n)

data NontrivialExpr :: Nat -> Type where
  Application :: !(Function m n) -> (Vec m Value) -> NontrivialExpr n
  CaseIntRhs :: !(CaseExpr n) -> NontrivialExpr n

data CaseExpr :: Nat -> Type where
  CaseExpr ::
         !ShortText -- landing label 
      -> !Value -- scrutinee
      -> !WordWidth -- word width of scrutinee
      -> !(Vec n Rep) -- result types (as tuple)
      -> !ShortText -- label of default
      -> !(Expr n) -- default
      -> [AlternativeInt n] -- alternatives
      -> CaseExpr n

data AlternativeInt (n :: Nat) = AlternativeInt
  !ShortText -- Label
  !Int
  !(Expr n)

data Value
  = Var !ShortText !Rep -- identifier
  | Lit Literal    -- constant

data Literal
  = Integer !Int !WordWidth
  | Boolean !Bool
  | String !ShortText

data Function :: Nat -> Nat -> Type where
  Add :: Function ('Succ ('Succ 'Zero)) ('Succ 'Zero)
  Multiply :: Function ('Succ ('Succ 'Zero)) ('Succ 'Zero)

data WordWidth = W8 | W16 | W32 | W64
data FloatWidth = F32 | F64
data Rep = Word WordWidth | Float FloatWidth | Boxed
data Kind = Base Rep | TupleK [Kind] | Sum [Kind]

flattenKind :: Kind -> [Rep]
flattenKind = \case
  Base r -> [r]
  TupleK xs -> xs >>= flattenKind
  Sum xs -> xs >>= flattenKind

compileFunction :: [(ShortText,Rep)] -> Expr n -> [Rep] -> AST.Definition
compileFunction args e retKind = 
  AST.GlobalDefinition AST.functionDefaults
    { AST.name        = "exampleFunction"
    , AST.parameters  = (params, False)
    , AST.returnType  = case retKind of
        [r] -> repToLlvmType r
        _ -> error "compileFunction: sorry, implement this"
    , AST.basicBlocks = flattenRetBlocks (retBlocks "beginning" [] e) []
    }
  where
  params = makeParameters args

flattenRetBlocks :: RetBlocks -> [AST.BasicBlock] -> [AST.BasicBlock]
flattenRetBlocks RetBlocks{self,children} acc =
  self : foldr (\r xs -> flattenRetBlocks r xs) acc children

data RetBlocks = RetBlocks
  { self :: AST.BasicBlock
  , children :: ![RetBlocks]
    -- ^ Places that self may jump to. No particular order implied.
  }

data Tree a
  = Branch [Tree a]
  | Leaf a
  deriving Foldable

-- -- | Needed to handle case statements. None of the the resulting blocks
-- -- have a ret instruction. Probably should take RHS of @let x = case ...@
-- -- rather than an arbitrary expression.
-- data BindingBlocks n = BindingBlocks
--   { self :: AST.BasicBlock
--   , children :: ![BindingBlocks n]
--   , results :: ![Result n]
--     -- ^ Places that self may jump to. No particular order implied.
--   }

data Result n = Result
  !ShortText -- final block labels
  !(Vec n AST.Operand) -- named results in this block

data CaseResult n = CaseResult
  !ShortText -- label in which branch appears
  !(Vec n Value) -- needed by landing site that case arms jump to

caseToBlocks ::
     ShortText -- return label
  -> AlternativeInt n -- pattern and arm
  -> (RetBlocks, Tree (CaseResult n))
caseToBlocks !returnLabel (AlternativeInt label i body) =
  bindBlocks label returnLabel [] body

bindBlocks ::
     ShortText -- pending label
  -> ShortText -- return label
  -> [AST.Named AST.Instruction] -- pending instructions
  -> Expr n -- expression
  -> (RetBlocks,Tree (CaseResult n))
bindBlocks !pendingLabel !returnLabel !pendingInstructions = \case
  Val v ->
    ( RetBlocks
      ( AST.BasicBlock
        (AST.Name (TS.toShortByteString pendingLabel))
        (List.reverse pendingInstructions)
        (AST.Do (AST.Br (AST.Name (TS.toShortByteString returnLabel)) []))
      ) []
    , Leaf (CaseResult pendingLabel v)
    )
  Let vars rhs body -> case rhs of
    Application func args -> 
      let instr = makeFunction vars func args
       in bindBlocks pendingLabel returnLabel (instr : pendingInstructions) body
    CaseIntRhs c@(CaseExpr landingLabel _ _ _ _ _ _) ->
      let (headBlock,caseBlocks,phis) = makeCaseBind vars pendingLabel pendingInstructions c
          (bodyBlocks,vals) = bindBlocks landingLabel returnLabel phis body
       in (RetBlocks headBlock (bodyBlocks : caseBlocks),vals)
  -- Casing here does not require building the landing block phi nodes.
  -- Since we are in the RHS of a let binding, someone else will construct
  -- those nodes.
  CaseIntExpr (CaseExpr _ scrutinee scrutineeTy resTy defLabel def alts) ->
    let xs = List.map
          (\alt -> caseToBlocks returnLabel alt)
          alts
        caseBlocks = map fst xs
        caseVals = map snd xs
        block = makeSwitchTerminatedBlock pendingLabel pendingInstructions scrutinee defLabel alts
     in (RetBlocks block caseBlocks,Branch caseVals)


-- letCaseRhs :: ShortText -> CaseExpr m -> Expr n -> [AST.Named AST.Instruction] -> RetBlocks
-- letCaseRhs pendingLabel (CaseExpr landingLabel scrutinee scrutineeTy resTy defLabel def alts) body pendingInstructions =
--   let (caseBlocks,caseVals) = List.foldl'
--         (\(!bs,!vs) alt -> caseToBlocks landingLabel alt bs vs)
--         ([],[])
--         alts
--       block = AST.BasicBlock
--         (AST.Name (TS.toShortByteString pendingLabel))
--         (List.reverse pendingInstructions)
--         (AST.Do $ AST.Switch
--           (valueToOperand scrutinee) (varToName defLabel) (map altToLabel alts) []
--         )
--       bodyBlocks = retBlocks landingLabel [] body
--    in RetBlocks block (bodyBlocks : caseBlocks)

retBlocks ::
     ShortText -- pending label
  -> [AST.Named AST.Instruction] -- pending instructions
  -> Expr n -- expression
  -> RetBlocks
retBlocks !pendingLabel !pendingInstructions = \case
  Val v -> RetBlocks
    (AST.BasicBlock
      (AST.Name (TS.toShortByteString pendingLabel))
      (List.reverse pendingInstructions)
      (AST.Do (AST.Ret (Just (valuesToOperand v)) []))
    ) []
  Let vars rhs body -> case rhs of
    CaseIntRhs c@(CaseExpr landingLabel scrutinee scrutineeTy resTy defLabel def alts) ->
      let (headBlock,caseBlocks,phis) = makeCaseBind vars pendingLabel pendingInstructions c
          bodyBlocks = retBlocks landingLabel phis body
       in RetBlocks headBlock (bodyBlocks : caseBlocks)
    Application func args ->
      let instr = makeFunction vars func args
       in retBlocks pendingLabel (instr : pendingInstructions) body

-- Returns
-- * Head block: the block that ends with a switch
-- * Case blocks: blocks for each case arm
-- * Label-to-value mapping: Used in phi nodes to map returned values
--
-- TODO: add phi nodes
makeCaseBind ::
     Vec n ShortText
  -> ShortText
  -> [AST.Named AST.Instruction]
  -> CaseExpr n
  -> (AST.BasicBlock,[RetBlocks],[AST.Named AST.Instruction])
makeCaseBind !vars !pendingLabel !pendingInstructions (CaseExpr landingLabel scrutinee scrutineeTy resTy defLabel def alts) =
  let xs = List.map
        (\alt -> caseToBlocks landingLabel alt)
        alts
      caseBlocks = map fst xs
      caseVals = map snd xs
      block = makeSwitchTerminatedBlock pendingLabel pendingInstructions scrutinee defLabel alts
      acc0 = case headTree (Branch caseVals) of
        CaseResult _ v -> initialAccumulatorMatchingLength v
      phiNodeInners = foldl'
        (\acc (CaseResult lbl vals) ->
          zipVec (\x v -> (valueToOperand v,varToName lbl) : x) acc vals
        )
        acc0 (Branch caseVals)
      phiNodes = zipVec
        (\var xs -> varToName var := AST.Phi (repToLlvmType (Word W32)) xs [])
        vars phiNodeInners
   in (block,caseBlocks,toList phiNodes)

makeSwitchTerminatedBlock ::
     ShortText
  -> [Named AST.Instruction]
  -> Value
  -> ShortText
  -> [AlternativeInt n]
  -> AST.BasicBlock
makeSwitchTerminatedBlock pendingLabel pendingInstructions scrutinee defLabel alts = 
  AST.BasicBlock
    (AST.Name (TS.toShortByteString pendingLabel))
    (List.reverse pendingInstructions)
    (AST.Do $ AST.Switch
      (valueToOperand scrutinee) (varToName defLabel) (map altToLabel alts) []
    )

zipVec :: (a -> b -> c) -> Vec n a -> Vec n b -> Vec n c
zipVec _ VecNil VecNil = VecNil
zipVec f (VecCons a as) (VecCons b bs) = VecCons (f a b) (zipVec f as bs)

headTree :: Tree a -> a
headTree (Leaf a) = a
headTree (Branch xs) = case xs of
  [] -> error "headTree failed"
  y : _ -> headTree y

initialAccumulatorMatchingLength :: Vec n a -> Vec n [(AST.Operand,AST.Name)]
initialAccumulatorMatchingLength VecNil = VecNil
initialAccumulatorMatchingLength (VecCons _ v) =
  VecCons [] (initialAccumulatorMatchingLength v)

makeFunction :: Vec n ShortText -> Function m n -> Vec m Value -> AST.Named AST.Instruction
makeFunction vars func args = case func of
  Add -> case args of
    VecCons a (VecCons b VecNil) ->
      let instr = AST.Add False False (intValueToOperand a) (intValueToOperand b) []
       in case vars of
            VecCons var VecNil -> varToName var := instr
  Multiply -> case args of
    VecCons a (VecCons b VecNil) ->
      let instr = AST.Mul False False (intValueToOperand a) (intValueToOperand b) []
       in case vars of
            VecCons var VecNil -> varToName var := instr

altToLabel :: AlternativeInt n -> (C.Constant, AST.Name)
altToLabel (AlternativeInt lbl pat _) =
  (Constant.Int 32 (fromIntegral pat), varToName lbl)

valueToOperand :: Value -> AST.Operand
valueToOperand = \case
  Var v rep -> varToOperand v rep
  Lit x -> litToOperand x

valuesToOperand :: Vec n Value -> AST.Operand
valuesToOperand = \case
  VecCons x VecNil -> valueToOperand x
  _ -> error "valuesToOperand: write this"

varToOperand :: ShortText -> Rep -> AST.Operand
varToOperand v r = (AST.LocalReference (repToLlvmType r) (AST.Name (TS.toShortByteString v)))

repToLlvmType :: Rep -> AST.Type
repToLlvmType = \case
  Word w -> wordWidthToIntegerType w

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

ex1Ret :: [Rep]
ex1Ret = [Word W32]

infixr 7 &:
(&:) :: a -> Vec n a -> Vec ('Succ n) a
(&:) = VecCons

w32r :: Rep
w32r = Word W32

ex1Body :: Expr ('Succ 'Zero)
ex1Body =
  Let ("z" &: VecNil) (Application Add (Var "x" w32r &: Var "y" w32r &: VecNil)) $
  Let ("w" &: VecNil) (Application Multiply (Var "y" w32r &: Var "z" w32r &: VecNil)) $
  Let ("p" &: VecNil)
    (CaseIntRhs $ CaseExpr "case.alpha" (Var "w" w32r) W32 (w32r &: VecNil) "case.alpha.default" (Val (Lit (Integer 500 W32) &: VecNil))
      [ AlternativeInt "case.12" 12 $ CaseIntExpr
          (CaseExpr "case.beta" (Var "w" w32r) W32 (w32r &: VecNil) "case.beta.default" (Val (Lit (Integer 630 W32) &: VecNil))
            [ AlternativeInt "case.258" 258 (Val (Lit (Integer 998 W32) &: VecNil))
            , AlternativeInt "case.109" 109 $
                Let ("b" &: VecNil) (Application Multiply (Var "z" w32r &: Lit (Integer 653 W32) &: VecNil)) $
                Val (Var "b" w32r &: VecNil)
            ]
          )
      , AlternativeInt "case.36" 36 $
          Let ("t" &: VecNil) (Application Multiply (Var "z" w32r &: Var "z" w32r &: VecNil)) $
          Val (Var "t" w32r &: VecNil)
      ]
    ) $
  Val (VecCons (Var "p" w32r) VecNil)
