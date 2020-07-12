{-# language DuplicateRecordFields #-}
{-# language NamedFieldPuns #-}
{-# language LambdaCase #-}

module Syntax
  ( decode
  , clean
  , Term(..)
  , InfixChain(..)
  , Op(..)
  , Declaration(..)
  , Pattern
  , Alternative(..)
  ) where

import Control.Applicative (liftA2)
import Data.Parser (Parser)
import Data.Primitive (SmallArray)
import Data.Text.Short (ShortText)
import Token (Token)
import Data.Int (Int64)

import qualified Data.Parser as Parser
import qualified Token as T

-- declaration
--   | declare name : typescheme as termchain0
-- typescheme
--   | forall quantified typechain0
--   | typechain0
-- quantified
--   | var quantified
--   | .
-- typechain0
--   | types0 typechain1
-- typechain1
--   | -> types0 typechain1
--   | empty
-- types0 // type application
--   | type types1
-- types1 // type application, not obviously LL(1)
--   | type types1
--   | empty
-- type
--   | ( typechain0 )
--   | constant
--   | var
--   | < typetuple0
-- typetuple0
--   | >
--   | types typetuple1
-- typetuple1
--   | >
--   | , types typetuple1
-- termchain0
--   | term termchain1
-- termchain1
--   | infixop term termchain1 // infix operator
--   | term termchain1 // function application
--   | empty
-- term
--   | lambda var arrow termchain0
--   | var
--   | int
--   | string
--   | ( term )
--   | case term of { alts0
-- alts0
--   | }
--   | alt alts1
-- alts1
--   | ; alts1
--   | } 
-- alt
--   | pattern -> term
-- pattern
--   | < tuplepat0
--   | datacon patterns
--   | var
--   | ( pattern )
-- patterns
--   | pattern patterns
--   | empty
-- tuplepat0
--   | >
--   | pattern tuplepat1
-- tuplepat1
--   | >
--   | , pattern tuplepat1

data Declaration = Declaration
  { name :: !ShortText
  , type_ :: !TypeScheme
  , definition :: !Term
  } deriving (Show)

data Term
  = Var !ShortText
  | Lam !ShortText Term
  | Infixes Term InfixChain
  | Tuple [Term]
  | Case !Term [Alternative]
  | Integer !Int64
  deriving (Show)

data Alternative = Alternative
  { pat :: !Pattern
  , arm :: !Term
  } deriving (Show)

data Pattern
  = PatternVariable !ShortText
  | PatternDeconstruction !Deconstruction
  deriving (Show)

data Deconstruction = Deconstruction
  { constructor :: Constructor
  , bindings :: [Pattern]
  } deriving (Show)

data Constructor
  = CustomConstructor !ShortText
  | TupleConstructor
  deriving (Show)

data TypeScheme = TypeScheme
  { variables :: ![ShortText]
  , type_ :: !Type
  } deriving (Show)

data Type
  = VarT !ShortText
  | AppT [Type]
  | Arr [Type]
  | Constant !ShortText
  | TupleT [Type] 
  deriving (Show)

data InfixChain
  = InfixChainTerminal
  | InfixChainCons !Op !Term !InfixChain
  deriving (Show)

data Op
  = Application
  | CustomOp !ShortText
  deriving (Show)

mapInfixChain :: (Term -> Term) -> InfixChain -> InfixChain
mapInfixChain _ InfixChainTerminal = InfixChainTerminal
mapInfixChain f (InfixChainCons op t ts) = InfixChainCons op (f t) (mapInfixChain f ts)

decode :: SmallArray Token -> Parser.Result String Declaration
decode = Parser.parseSmallArray declaration

clean :: Declaration -> Declaration
clean d@Declaration{type_,definition} = d
  { type_ = cleanTypeScheme type_
  , definition = cleanTerm definition
  }

cleanTypeScheme :: TypeScheme -> TypeScheme
cleanTypeScheme s@TypeScheme{type_} = s {type_ = cleanType type_}

cleanType :: Type -> Type
cleanType ty = case ty of
  VarT{} -> ty
  Constant{} -> ty
  AppT tys -> case tys of
    [] -> error "Empty application encountered. Fix this."
    [ty0] -> cleanType ty0
    _ -> AppT (map cleanType tys)
  Arr tys -> case tys of
    [] -> error "Empty arrow chain encountered. Fix this."
    [ty0] -> cleanType ty0
    _ -> Arr (map cleanType tys)
  TupleT{} -> ty

cleanTerm :: Term -> Term
cleanTerm t = case t of
  Var{} -> t
  Integer{} -> t
  -- App ts -> case ts of
  --   [] -> error "Empty term application encountered. Fix this."
  --   [t0] -> cleanTerm t0
  --   _ -> App (map cleanTerm ts)
  Lam v a -> Lam v (cleanTerm a)
  Case e ts -> Case (cleanTerm e) (map cleanAlternative ts)
  Tuple{} -> t -- TODO: recurse into components
  Infixes t0 ts -> Infixes (cleanTerm t0) (mapInfixChain cleanTerm ts)

cleanAlternative :: Alternative -> Alternative
cleanAlternative Alternative{pat,arm} = Alternative
  { pat
  , arm = cleanTerm arm
  }

declaration :: Parser Token String s Declaration
declaration = do
  Parser.token "declaration: expecting declare keyword" T.Declare
  Parser.any "declaration: expecting name" >>= \case
    T.IdentLower name -> do
      Parser.token "declaration: expecting colon" T.Colon
      type_ <- typeScheme
      Parser.token "declaration: expecting as keyword" T.As
      definition <- termchain0
      Parser.any "declaration: got eof when end was expected" >>= \case
        T.End -> pure ()
        token -> Parser.fail ("declaration: expected end, got " ++ show token)
      pure (Declaration{name,type_,definition})
    _ -> Parser.fail "declaration: expecting identifier" 

typeScheme :: Parser Token String s TypeScheme
typeScheme = Parser.peek "typeScheme: expected leading token" >>= \case
  T.Forall -> do
    _ <- Parser.any "typeScheme: not possible"
    variables <- quantified
    type_ <- fmap Arr typechain0
    pure (TypeScheme{variables, type_})
  _ -> do
    type_ <- fmap Arr typechain0
    pure (TypeScheme{variables=[], type_})

quantified :: Parser Token String s [ShortText]
quantified = Parser.any "quantified: expected leading token" >>= \case
  T.Period -> pure []
  T.IdentLower ident -> do
    idents <- quantified
    pure (ident : idents)

typechain0 :: Parser Token String s [Type]
typechain0 = do
  t <- types0
  ts <- typechain1
  pure (t : ts)

typechain1 :: Parser Token String s [Type]
typechain1 = Parser.peek "typechain1: expected leading token" >>= \case
  T.Arrow -> do
    _ <- Parser.any "typechain1: not possible"
    t <- types0
    ts <- typechain1
    pure (t : ts)
  _ -> pure []

typetuple0 :: Parser Token String s [Type]
typetuple0 = Parser.peek "typetuple0: expected leading token" >>= \case
  T.AngleClose -> do
    _ <- Parser.any "typetuple0: not possible"
    pure []
  _ -> do
    t <- types0
    ts <- typetuple1
    pure (t : ts)

typetuple1 :: Parser Token String s [Type]
typetuple1 = Parser.any "typetuple1: expected leading token" >>= \case
  T.AngleClose -> pure []
  T.Comma -> do
    t <- types0
    ts <- typetuple1
    pure (t : ts)
  _ -> Parser.fail "typetuple1: expected angle-close or comma"

types0 :: Parser Token String s Type
types0 = do
  t <- typeParser
  ts <- types1
  pure (AppT (t : ts))

types1 :: Parser Token String s [Type]
types1 = Parser.peek "types1: expected leading token" >>= \case
  T.ParenOpen -> liftA2 (:) typeParser types1
  T.AngleOpen -> liftA2 (:) typeParser types1
  T.IdentUpper{} -> liftA2 (:) typeParser types1
  T.IdentLower{} -> liftA2 (:) typeParser types1
  _ -> pure []

typeParser :: Parser Token String s Type
typeParser = Parser.any "typeParser: expected leading token" >>= \case
  T.AngleOpen -> fmap TupleT typetuple0
  T.ParenOpen -> do
    r <- typechain0
    Parser.any "typeParser: expecting close paren" >>= \case
      T.ParenClose -> pure (Arr r)
      _ -> Parser.fail "typeParser: expecting close paren" 
  T.IdentUpper ident -> pure $ Constant ident
  T.IdentLower ident -> pure $ VarT ident
  _ -> Parser.fail "typeParser: unexpected token"

term :: Parser Token String s Term
term = Parser.any "term: expected leading token" >>= \case
  T.ParenOpen -> do
    r <- termchain0
    Parser.any "term: expecting close paren" >>= \case
      T.ParenClose -> pure r
      _ -> Parser.fail "term: expecting close paren" 
  T.IdentLower ident -> pure $ Var ident
  T.Integer i -> pure $ Integer i
  T.Backslash -> Parser.any "term: expecting identifier after lambda" >>= \case
    T.IdentLower ident -> do
      Parser.token "term: expecting arrow after lambda" T.Arrow
      t <- termchain0
      pure (Lam ident t)
    _ -> Parser.fail "term: expecting identifier after lambda" 
  T.Case -> do
    expr <- term
    Parser.token "term: expecting of keyword" T.Of
    Parser.token "term: expecting open curly" T.CurlyOpen
    xs <- alts0
    pure (Case expr xs)
  token -> Parser.fail ("term: unexpected token: " ++ show token)

termchain0 :: Parser Token String s Term
termchain0 = do
  t <- term
  ts <- termchain1
  pure (Infixes t ts)

termchain1 :: Parser Token String s InfixChain
termchain1 = Parser.peek "termchain1: expected leading token" >>= \case
  T.Infix op -> do
    _ <- Parser.any "termchain1: not possible"
    t <- term
    ts <- termchain1
    pure (InfixChainCons (CustomOp op) t ts)
  T.IdentLower{} -> liftA2 (InfixChainCons Application) term termchain1
  T.Integer{} -> liftA2 (InfixChainCons Application) term termchain1
  T.Text{} -> liftA2 (InfixChainCons Application) term termchain1
  T.ParenOpen{} -> liftA2 (InfixChainCons Application) term termchain1
  T.Case{} -> liftA2 (InfixChainCons Application) term termchain1
  T.Backslash{} -> liftA2 (InfixChainCons Application) term termchain1
  _ -> pure InfixChainTerminal

alts0 :: Parser Token String s [Alternative]
alts0 = Parser.peek "alts0: expected leading token" >>= \case
  T.CurlyClose -> do
    _ <- Parser.any "alts0: not possible"
    pure []
  _ -> do
    t <- alt
    ts <- alts1
    pure (t : ts)

alts1 :: Parser Token String s [Alternative]
alts1 = Parser.any "alts1: expected leading token" >>= \case
  T.CurlyClose -> pure []
  T.Semicolon -> do
    t <- alt
    ts <- alts1
    pure (t : ts)
  token -> Parser.fail ("alts1: expected curly-close or semicolon, got " ++ show token)

alt :: Parser Token String s Alternative
alt = do
  pat <- patParser
  Parser.token "alt: expecting arrow after pattern" T.Arrow
  arm <- termchain0
  pure Alternative{pat,arm}

patParser :: Parser Token String s Pattern
patParser = Parser.any "patParser: expected token" >>= \case
  T.AngleOpen -> do
    pats <- tuplePat0
    pure (PatternDeconstruction (Deconstruction TupleConstructor pats))
  T.IdentUpper datacon -> do
    pats <- patterns
    pure (PatternDeconstruction (Deconstruction (CustomConstructor datacon) pats))
  T.IdentLower var -> pure (PatternVariable var)
  T.ParenOpen -> patParser <* Parser.token "patParser: expecting close paren" T.ParenClose
  _ -> Parser.fail "patParser: wrong token type"

patterns :: Parser Token String s [Pattern]
patterns = Parser.peek "patterns: expected leading token" >>= \case
  T.ParenOpen -> liftA2 (:) patParser patterns
  T.AngleOpen -> liftA2 (:) patParser patterns
  T.IdentUpper{} -> liftA2 (:) patParser patterns
  T.IdentLower{} -> liftA2 (:) patParser patterns
  _ -> pure []

tuplePat0 :: Parser Token String s [Pattern]
tuplePat0 = Parser.peek "tuplePat0: expected leading token" >>= \case
  T.AngleClose -> do
    _ <- Parser.any "tuplePat0: not possible"
    pure []
  _ -> do
    t <- patParser
    ts <- tuplePat1
    pure (t : ts)

tuplePat1 :: Parser Token String s [Pattern]
tuplePat1 = Parser.any "tuplePat1: expected leading token" >>= \case
  T.AngleClose -> pure []
  T.Comma -> do
    t <- patParser
    ts <- tuplePat1
    pure (t : ts)
  _ -> Parser.fail "tuplePat1: expected angle-close or comma"
