{-# language DuplicateRecordFields #-}
{-# language NamedFieldPuns #-}

module Main where

import Data.Parser (Result(..),Slice(..))
import Associate (associate,arithmetic)
import LoweredGrinJoin2 (compileFunction,ex2Args,ex2Ret,ex3Body,ex4Body)
import LoweredGrinJoin2 (compileFunction,ex1Args,ex1Ret,ex1Body)
import LoweredGrinJoin2 (ex5Body)
import LLVM.Pretty (ppll)

import qualified Syntax
import qualified Token
import qualified Data.Bytes.Chunks as Chunks
import qualified System.IO as IO
import qualified Data.Text.Lazy.IO as T

main :: IO ()
main = do
  T.putStrLn $ ppll $ compileFunction ex1Args ex5Body ex1Ret
  -- print $ allNames ex3Body

-- main :: IO ()
-- main = do
--   c <- Chunks.hGetContents IO.stdin
--   case Token.tokenize (Chunks.concat c) of
--     Nothing -> fail "bad token stream"
--     Just ts -> do
--       print ts
--       case Syntax.decode ts of
--         Success (Slice off len r@Syntax.Declaration{definition}) -> do
--           print r
--           putStrLn "Cleaned"
--           print (Syntax.clean r)
--           case associate arithmetic definition of
--             Left err -> fail err
--             Right t -> do
--               putStrLn "After infix cleanup"
--               print t
--         Failure err -> fail err
