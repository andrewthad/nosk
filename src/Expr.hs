-- Ignore this module. It is not done yet.
module Expr
  (
  ) where

data Expr
  = Var Text
  | App Expr Expr
  | Lam Var Type.Type Expr
  | Let Var Expr Expr
  | Lit Literal
  | Instantiate Text (Map Text Representation) (Map Text Type.Type)
    -- ^ Instantiate takes a top-level declaration as its argument. These are
    -- the only values that have type schemes instead of monotypes.
  | Constructor Data.Constructor (Map Text Representation) (Map Text Type.Type)
  | Tuple [Expr]
  | Case Expr [Alternative]
  deriving (Show, Eq, Ord)

data Literal
  = Integer !Int
  | Boolean !Bool
  | String !Text
  deriving (Eq,Ord,Show)

data PrimFunc
  = Add !Width
  


