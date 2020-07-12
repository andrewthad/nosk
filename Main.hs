{-# language DuplicateRecordFields #-}
{-# language NamedFieldPuns #-}

module Main where

import Data.Parser (Result(..),Slice(..))
import Associate (associate,arithmetic)

import qualified Syntax
import qualified Token
import qualified Data.Bytes.Chunks as Chunks
import qualified System.IO as IO

main :: IO ()
main = do
  c <- Chunks.hGetContents IO.stdin
  case Token.tokenize (Chunks.concat c) of
    Nothing -> fail "bad token stream"
    Just ts -> do
      print ts
      case Syntax.decode ts of
        Success (Slice off len r@Syntax.Declaration{definition}) -> do
          print r
          putStrLn "Cleaned"
          print (Syntax.clean r)
          case associate arithmetic definition of
            Left err -> fail err
            Right t -> do
              putStrLn "After infix cleanup"
              print t
        Failure err -> fail err
