{-# language BangPatterns #-}
{-# language DuplicateRecordFields #-}
{-# language LambdaCase #-}
{-# language NamedFieldPuns #-}
{-# language OverloadedStrings #-}

module Associate
  ( associate
  , arithmetic
  , Term(..)
  ) where

import Control.Monad (forM)
import Data.Map (Map)
import Data.Text.Short (ShortText)
import Data.Int (Int64)

import qualified Syntax as S
import qualified Data.Map.Strict as Map

data Term
  = Var !ShortText
  | Lam !ShortText Term
  | App !Term !Term
  | Tuple [Term]
  | Case !Term [Alternative]
  | Integer !Int64
  deriving (Show)

data Alternative = Alternative
  { pat :: !S.Pattern
  , arm :: !Term
  } deriving (Show)

data Stack
  = StackTerminal !Term
  | StackCons !Term !ShortText !Stack

pair :: Term -> Term -> Term
pair a b = Tuple [a,b]

arithmetic :: Map (ShortText,ShortText) Ordering
arithmetic = Map.fromList
  [ (("+","+"),EQ)
  , (("*","*"),EQ)
  , (("*","+"),GT)
  , (("+","*"),LT)
  ]

associate ::
     Map (ShortText,ShortText) Ordering
  -> S.Term
  -> Either String Term
associate !ords = \case
  S.Var t -> Right (Var t)
  S.Integer t -> Right (Integer t)
  S.Tuple t -> Tuple <$> mapM (associate ords) t
  S.Lam v t -> Lam v <$> associate ords t
  S.Infixes hd xs -> do
    hd' <- associate ords hd
    shuntingYard ords (StackTerminal hd') xs
  S.Case t alts -> do
    t' <- associate ords t
    alts' <- forM alts $ \S.Alternative{pat,arm} -> do
      arm' <- associate ords arm
      pure Alternative{pat,arm=arm'}
    pure (Case t' alts')

-- Variant of shunting yard algorithm described at https://www.reddit.com/r/learnprogramming/comments/3cybca/how_do_i_go_about_building_an_ast_from_an_infix/ct02uam?utm_source=share&utm_medium=web2x
-- Good summary of rules at http://mathcenter.oxford.emory.edu/site/cs171/shuntingYardAlgorithm/
shuntingYard ::
     Map (ShortText,ShortText) Ordering -- ordering table
  -> Stack -- stack of operands and operators
  -> S.InfixChain -- argument symbols
  -> Either String Term
shuntingYard ords st0 = \case
  S.InfixChainTerminal -> Right (popAll ords st0)
  S.InfixChainCons opX term chain -> do
    term' <- associate ords term
    case opX of
      S.Application -> shuntingYard ords (apLast term' st0) chain
      S.CustomOp op -> popUntilGtThenPush ords st0 chain op term'

popAll :: 
     Map (ShortText,ShortText) Ordering -- ordering table
  -> Stack -- stack of operands and operators
  -> Term
popAll ords = \case
  StackTerminal t -> t
  StackCons t1 op st -> popAll ords (mergeLast op t1 st)

apLast :: Term -> Stack -> Stack
apLast t = \case
  StackTerminal t0 -> StackTerminal (App t0 t)
  StackCons t0 op0 st0 -> StackCons (App t0 t) op0 st0

mergeLast :: ShortText -> Term -> Stack -> Stack
mergeLast op t = \case
  StackTerminal t0 -> StackTerminal (App (Var op) (pair t0 t))
  StackCons t0 op0 st0 -> StackCons (App (Var op) (pair t0 t)) op0 st0

popUntilGtThenPush ::
     Map (ShortText,ShortText) Ordering -- ordering table
  -> Stack -- stack of operands and operators
  -> S.InfixChain -- constant while recursing
  -> ShortText -- operator we are comparing against, constant
  -> Term -- term to push
  -> Either String Term
popUntilGtThenPush ords st0 chain op t0 = case st0 of
  StackTerminal t -> shuntingYard ords (StackCons t0 op st0) chain
  StackCons t opTop st1 -> case Map.lookup (op,opTop) ords of
    Just GT -> shuntingYard ords (StackCons t0 op st0) chain
    Just _ -> popUntilGtThenPush ords (mergeLast opTop t st1) chain op t0
    Nothing -> Left "operators cannot be used together"
