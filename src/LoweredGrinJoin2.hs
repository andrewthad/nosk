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

module LoweredGrinJoin2
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
import qualified LLVM.AST.CallingConvention as CC
import qualified LLVM.AST.Global as AST
import qualified LLVM.AST.Type as AST
import qualified LLVM.AST.IntegerPredicate as AST
import qualified LLVM.AST.AddrSpace as AST
import qualified LLVM.AST.Constant as C
import qualified LLVM.AST.Float as F
import qualified LLVM.AST.FunctionAttribute as Attr
import qualified LLVM.AST.Linkage as Linkage

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
  = Unit [Value]
    -- ^ Lift a value into an expression
  | Application Function [Value]
    -- ^ Call a function
  | EnsureHeap !Int Expr
    -- ^ Ensure that the heap has a given number of bytes available.
  | Allocate Constructor [Value]
    -- ^ Allocate node on heap
  | Fetch !ShortText !Int Rep
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
    , allocateHeapBlockDef
    , ptrMaskDef
    , expectDef
    , funcDef
    ]
  }
  where
  expectDef = AST.GlobalDefinition $ AST.functionDefaults
    { AST.name = "llvm.expect.i1"
    , AST.returnType = AST.IntegerType 1
    , AST.parameters =
        ( [ AST.Parameter (AST.IntegerType 1) (AST.Name (TS.toShortByteString "val")) []
          , AST.Parameter (AST.IntegerType 1) (AST.Name (TS.toShortByteString "expected_val")) []
          ]
        , False
        )
    , AST.functionAttributes = [Right Attr.ReadNone, Right Attr.Speculatable]
    }
  ptrMaskDef = AST.GlobalDefinition $ AST.functionDefaults
    { AST.name = "llvm.ptrmask.p1i64.i64"
    , AST.returnType = ptr1 (AST.IntegerType 64)
    , AST.parameters =
        ( [ AST.Parameter (ptr1 (AST.IntegerType 64)) (AST.Name (TS.toShortByteString "ptr")) []
          , AST.Parameter (AST.IntegerType 64) (AST.Name (TS.toShortByteString "mask")) []
          ]
        , False
        )
    , AST.functionAttributes = [Right Attr.ReadNone, Right Attr.Speculatable]
    }
  allocateHeapBlockDef = AST.GlobalDefinition $ AST.functionDefaults
    { AST.name = "allocateHeapBlock"
    , AST.returnType = ptr1 (AST.IntegerType 64)
    , AST.parameters = ([hpParam],False)
    }
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
    , AST.parameters  = (hpParam : params, False)
    , AST.returnType  = case retKind of
        [r] -> repToLlvmType r
        _ -> error "compileFunction: sorry, implement this"
    , AST.basicBlocks =
        let allocHp = "hp" := AST.Alloca
              { allocatedType = ptr1 (AST.IntegerType 64)
              , numElements = Nothing
              , alignment = 8
              , metadata = []
              }
            initHp = AST.Do $ AST.Store
              { volatile = False 
                -- TODO: address type is bad
              , address = AST.LocalReference (AST.ptr (ptr1 (AST.IntegerType 64))) (varToName "hp")
              , value = AST.LocalReference (ptr1 (AST.IntegerType 64)) (varToName "hp.0")
              , maybeAtomicity = Nothing
              , alignment = 8
              , metadata = []
              }
            fragments = compile "beginning" [] [initHp,allocHp] Returning e
         in flattenWithPhiNodes (resultsToMap fragments) [] fragments
    }

typePtrListW32 :: AST.Type
typePtrListW32 = ptr1 (AST.NamedTypeReference listW32Name)

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

data Context = Returning | Branching ShortText

data Fragment
  = Block PendingBlock
  | BranchMetadata Results

pending ::
     ShortText
  -> [ShortText]
  -> [AST.Named AST.Instruction]
  -> AST.Terminator
  -> Tree Fragment
pending label args instrs t = Leaf $ Block $ PendingBlock args
  (AST.BasicBlock
    (AST.Name (TS.toShortByteString label))
    instrs
    (AST.Do t)
  )

-- Resulting instructions are deliberately backwards in each block.
compile ::
     ShortText -- Pending label, reader-like
  -> [ShortText] -- Pending argument names for phi nodes at beginning of block, reader-like
  -> [AST.Named AST.Instruction] -- Pending instructions, writer-like
  -> Context -- Which LLVM instruction will the terminator be: ret or br
  -> Expr -- Expression, the thing actually being compiled
  -> Tree Fragment
compile !pendingLabel !pendingArgs !pendingInstructions !ctx = \case
  Application{} -> error "compile: Application in bad position"
  Allocate{} -> error "compile: Allocate in bad position"
  Unit v -> case ctx of
    Returning -> case v of
      [v0] -> pending
        pendingLabel pendingArgs pendingInstructions
        (AST.Ret (Just (valueToOperand v0)) [])
      _ -> error "compile: sorry, figure this out"
    Branching label -> Bin
      (pending
        pendingLabel pendingArgs pendingInstructions
        (AST.Br (AST.Name (TS.toShortByteString label)) [])
      )
      (Leaf (BranchMetadata (Results label pendingLabel v)))
  Join joinLabel args rhs body -> Bin
    (compile pendingLabel pendingArgs pendingInstructions Returning body)
    (compile joinLabel args [] ctx rhs)
  Jump label args -> Bin
    (pending pendingLabel pendingArgs pendingInstructions
      (AST.Br (AST.Name (TS.toShortByteString label)) [])
    )
    (Leaf (BranchMetadata (Results label pendingLabel args)))
  Case (CaseWord scrutinee scrutineeTy resTy defLabel def alts) ->
    let committedBlock = pending pendingLabel pendingArgs pendingInstructions
          (AST.Switch
            (valueToOperand scrutinee) (varToName defLabel) (map altToLabel alts) []
          )
        defBuilder = compile defLabel [] [] ctx def
        r = foldl'
          (\leftBuilder (AlternativeInt label pat e) ->
            let rightBuilder = compile label [] [] ctx e
             in Bin leftBuilder rightBuilder
          ) (Bin committedBlock defBuilder) alts
     in r
  EnsureHeap n e ->
    let name = "check"
        loadHp = heapPointerName name := loadHpInstruction
        lowHp = heapPointerName "low" := ptrMask4K "hp.check"
        upperHp = heapPointerName "upper" := AST.GetElementPtr
          { inBounds = True
          , address = AST.LocalReference (ptr1 (AST.IntegerType 64)) (heapPointerName name)
          , indices = [AST.ConstantOperand (Constant.Int 64 (fromIntegral n))]
          , metadata = []
          }
        highHp = heapPointerName "high" := AST.GetElementPtr
          { inBounds = True
          , address = AST.LocalReference (ptr1 (AST.IntegerType 64)) (heapPointerName "low")
          , indices = [AST.ConstantOperand (Constant.Int 64 0xFFF)]
          , metadata = []
          }
        replenish = AST.CondBr
          { condition = AST.LocalReference (AST.IntegerType 1) (varToName "has-sufficient-space-expect")
          , trueDest = varToName (pendingLabel <> ".post-heap-check")
          , falseDest = varToName (pendingLabel <> ".allocate-heap-block")
          , metadata' = []
          }
        computeCond = varToName "has-sufficient-space" := AST.ICmp
          { iPredicate = AST.ULT
          , operand0 = AST.LocalReference (ptr1 (AST.IntegerType 64)) (heapPointerName "upper")
          , operand1 = AST.LocalReference (ptr1 (AST.IntegerType 64)) (heapPointerName "high")
          , metadata = []
          }
        expectCond = varToName "has-sufficient-space-expect" := expectBool "has-sufficient-space" True
        storeNewHp = AST.Do $ AST.Store
          { volatile = False 
          , address = AST.LocalReference (AST.ptr (ptr1 (AST.IntegerType 64))) (varToName "hp")
          , value = AST.LocalReference (ptr1 (AST.IntegerType 64)) (heapPointerName "updated")
          , maybeAtomicity = Nothing
          , alignment = 8
          , metadata = []
          }
        allocationBlock = AST.BasicBlock
          (AST.Name (TS.toShortByteString (pendingLabel <> ".allocate-heap-block")))
          [storeNewHp,heapPointerName "updated" := newHeapBlockInstruction "hp.check"]
          (AST.Do (AST.Br (AST.Name (TS.toShortByteString (pendingLabel <> ".post-heap-check"))) []))
        postHeapCheck = compile (pendingLabel <> ".post-heap-check") [] [] ctx e
     in Bin
          (Bin
            (pending pendingLabel pendingArgs (expectCond : computeCond : highHp : lowHp : upperHp : loadHp : pendingInstructions) replenish)
            (Leaf (Block (PendingBlock [] allocationBlock)))
          ) postHeapCheck
  Bind landingLabel rhs vars body -> case rhs of
    Application func args -> case vars of
      [var] -> 
        let instr = makeFunction1 var func args
         in compile pendingLabel pendingArgs (instr : pendingInstructions) ctx body
    Allocate ctor args -> case vars of
      [var] -> case ctor of
        ConsW32 -> case args of
          [x,xs] ->
            let size = 3 :: Int -- size in machine words
                storeNewHp = AST.Do $ AST.Store
                  { volatile = False 
                  , address = AST.LocalReference (AST.ptr (ptr1 (AST.IntegerType 64))) (varToName "hp")
                  , value = AST.LocalReference (ptr1 (AST.IntegerType 64)) (heapPointerName (var <> ".next"))
                  , maybeAtomicity = Nothing
                  , alignment = 8
                  , metadata = []
                  }
                storeElement = AST.Do $ AST.Store
                  { volatile = False 
                  , address = AST.LocalReference ptr1Int32 (heapPointerName (var <> ".list.elem"))
                  , value = valueToOperand x
                  , maybeAtomicity = Nothing
                  , alignment = 4
                  , metadata = []
                  }
                storeTag = AST.Do $ AST.Store
                  { volatile = False 
                  , address = AST.LocalReference ptr1Int32 (heapPointerName (var <> ".list.tag"))
                  , value = AST.ConstantOperand (Constant.Int 32 1)
                  , maybeAtomicity = Nothing
                  , alignment = 4
                  , metadata = []
                  }
                computeElementAddr = heapPointerName (var <> ".list.elem") := AST.GetElementPtr
                  { inBounds = True
                  , address = AST.LocalReference typePtrListW32 (heapPointerName (var <> ".list.base"))
                  , indices = [AST.ConstantOperand (Constant.Int 64 0), AST.ConstantOperand (Constant.Int 32 1)]
                  , metadata = []
                  }
                computeTagAddr = heapPointerName (var <> ".list.tag") := AST.GetElementPtr
                  { inBounds = True
                  , address = AST.LocalReference typePtrListW32 (heapPointerName (var <> ".list.base"))
                  , indices = [AST.ConstantOperand (Constant.Int 64 0), AST.ConstantOperand (Constant.Int 32 0)]
                  , metadata = []
                  }
                castHeapPtrInstr = heapPointerName (var <> ".list.base") := AST.BitCast
                  { operand0 = AST.LocalReference (ptr1 (AST.IntegerType 64)) (heapPointerName var)
                  , type' = typePtrListW32
                  , metadata = []
                  }
                computeNewHp = heapPointerName (var <> ".next") := AST.GetElementPtr
                  { inBounds = True
                  , address = AST.LocalReference (ptr1 (AST.IntegerType 64)) (heapPointerName var)
                    -- Note: 3 is too much. Probably 2 would be fine.
                  , indices = [AST.ConstantOperand (Constant.Int 64 3)]
                  , metadata = []
                  }
                loadHp = heapPointerName var := loadHpInstruction
             -- in compile pendingLabel pendingArgs (bump : assignInfo : assignElement : assignTail : pendingInstructions) ctx body
             in compile pendingLabel pendingArgs (storeNewHp : computeNewHp : storeElement : computeElementAddr : storeTag : computeTagAddr : castHeapPtrInstr : loadHp : pendingInstructions) ctx body
          _ -> error "compile: ConsW32 has wrong number of arguments"
      _ -> error "compile: allocate only binds to one variable"
    _ -> Bin
      (compile pendingLabel pendingArgs pendingInstructions (Branching landingLabel) rhs)
      (compile landingLabel vars [] ctx body)

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

heapPointerName :: ShortText -> AST.Name
heapPointerName t = AST.Name (TS.toShortByteString ("hp." <> t))

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

hpParam :: AST.Parameter
hpParam = AST.Parameter (ptr1 (AST.IntegerType 64)) (AST.Name (TS.toShortByteString "hp.0")) []

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
  EnsureHeap 24 $
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

ptr1 :: AST.Type -> AST.Type
ptr1 t = AST.PointerType t (AST.AddrSpace 1)

ptr1Int32 :: AST.Type
ptr1Int32 = ptr1 (AST.IntegerType 32)

loadHpInstruction :: AST.Instruction
loadHpInstruction = AST.Load
  { volatile = False
  , address = AST.LocalReference (AST.ptr (ptr1 (AST.IntegerType 64))) (varToName "hp")
  , maybeAtomicity = Nothing
  , alignment = 8
  , metadata = []
  }

newHeapBlockInstruction :: ShortText -> AST.Instruction
newHeapBlockInstruction !oldHp = AST.Call
  { tailCallKind = Nothing
  , callingConvention = CC.C
  , returnAttributes = []
  , function = Right $ AST.ConstantOperand $ Constant.GlobalReference
      (AST.FunctionType
        (ptr1 (AST.IntegerType 64))
        [ptr1 (AST.IntegerType 64)]
        False
      )
      (varToName "allocateHeapBlock")
  , arguments = [(AST.LocalReference (ptr1 (AST.IntegerType 64)) (varToName oldHp),[])]
  , functionAttributes = []
  , metadata = []
  }

ptrMask4K :: ShortText -> AST.Instruction
ptrMask4K !arg = AST.Call
  { tailCallKind = Nothing
  , callingConvention = CC.C
  , returnAttributes = []
  , function = Right $ AST.ConstantOperand $ Constant.GlobalReference
      (AST.FunctionType
        (ptr1 (AST.IntegerType 64))
        [ptr1 (AST.IntegerType 64),AST.IntegerType 64]
        False
      )
      (varToName "llvm.ptrmask.p1i64.i64")
  , arguments =
      [(AST.LocalReference (ptr1 (AST.IntegerType 64)) (varToName arg),[])
      ,(AST.ConstantOperand (Constant.Int 64 0xFFFFFFFFFFFFF000),[])
      ]
  , functionAttributes = []
  , metadata = []
  }

expectBool :: ShortText -> Bool -> AST.Instruction
expectBool !arg !expected = AST.Call
  { tailCallKind = Nothing
  , callingConvention = CC.C
  , returnAttributes = []
  , function = Right $ AST.ConstantOperand $ Constant.GlobalReference
      (AST.FunctionType
        (AST.IntegerType 1)
        [AST.IntegerType 1,AST.IntegerType 1]
        False
      )
      (varToName "llvm.expect.i1")
  , arguments =
      [(AST.LocalReference (AST.IntegerType 1) (varToName arg),[])
      ,case expected of
         True -> (AST.ConstantOperand (Constant.Int 1 1),[])
         False -> (AST.ConstantOperand (Constant.Int 1 0),[])
      ]
  , functionAttributes = []
  , metadata = []
  }
