{-# language BangPatterns #-}
{-# language LambdaCase #-}
{-# language OverloadedStrings #-}

module Token
  ( Token(..)
  , tokenize
  ) where

import Data.Builder.ST (Builder)
import Data.Text.Short (ShortText)
import Data.Word (Word8)
import Data.Chunks (Chunks)
import Data.Bytes.Parser (Parser)
import Data.Primitive (SmallArray)
import Data.Int (Int64)
import Data.Bytes (Bytes)
import Data.Char (chr)

import qualified Data.Bytes as Bytes
import qualified Data.Bytes.Parser as P
import qualified Data.Bytes.Parser.Latin as Latin
import qualified Data.Bytes.Parser.Unsafe as Unsafe
import qualified Data.Builder.ST as Builder
import qualified Data.Chunks as Chunks
import qualified Data.Text.Short.Unsafe as TS

data Token
  = Integer !Int64
  | Text !ShortText
  | IdentLower !ShortText
  | IdentUpper !ShortText
  | Infix !ShortText
  | Backslash
  | Colon
  | Comma
  | Semicolon
  | Arrow
  | ParenOpen
  | ParenClose
  | AngleOpen
  | AngleClose
  | CurlyOpen
  | CurlyClose
  | Forall
  | Declare
  | As
  | Period
  | End
  | Case
  | Of
  deriving (Show,Eq)

tokenize :: Bytes -> Maybe (SmallArray Token)
tokenize x = case P.parseBytesMaybe parser x of
  Nothing -> Nothing
  Just r -> Just (Chunks.concat r)

parser :: Parser () s (Chunks Token)
parser = do
  b0 <- P.effect Builder.new
  step b0

step :: Builder s Token -> Parser () s (Chunks Token)
step !b0 = do
  Latin.skipWhile (\c -> c == ' ' || c == '\n' || c == '\r' || c == '\t')
  P.isEndOfInput >>= \case
    True -> P.effect (Builder.freeze b0)
    False -> Latin.any () >>= \case
      '\\' -> P.effect (Builder.push Backslash b0) >>= step
      '.' -> P.effect (Builder.push Period b0) >>= step
      ',' -> P.effect (Builder.push Comma b0) >>= step
      ':' -> P.effect (Builder.push Colon b0) >>= step
      '(' -> P.effect (Builder.push ParenOpen b0) >>= step
      ')' -> P.effect (Builder.push ParenClose b0) >>= step
      '{' -> P.effect (Builder.push CurlyOpen b0) >>= step
      '}' -> P.effect (Builder.push CurlyClose b0) >>= step
      ';' -> P.effect (Builder.push Semicolon b0) >>= step
      '<' -> P.effect (Builder.push AngleOpen b0) >>= step
      '>' -> P.effect (Builder.push AngleClose b0) >>= step
      '-' -> Latin.trySatisfy (== '>') >>= \case
        True -> P.effect (Builder.push Arrow b0) >>= step
        False -> P.effect (Builder.push (Infix "-") b0) >>= step
      '+' -> P.effect (Builder.push (Infix "+") b0) >>= step
      '*' -> P.effect (Builder.push (Infix "*") b0) >>= step
      c | c >= 'A' && c <= 'Z' -> do
            Unsafe.unconsume 1
            b <- P.takeWhile
              (\w -> let c = word8ToChar w in
                (c >= 'a' && c <= 'z') ||
                (c >= 'A' && c <= 'Z') ||
                (c >= '0' && c <= '9')
              )
            let txt = TS.fromShortByteStringUnsafe (Bytes.toShortByteString b)
            let !token = IdentUpper txt
            P.effect (Builder.push token b0) >>= step
        | c >= 'a' && c <= 'z' -> do
            Unsafe.unconsume 1
            b <- P.takeWhile
              (\w -> let c = word8ToChar w in
                (c >= 'a' && c <= 'z') ||
                (c >= 'A' && c <= 'Z') ||
                (c >= '0' && c <= '9')
              )
            let txt = TS.fromShortByteStringUnsafe (Bytes.toShortByteString b)
            let !token = case txt of
                  "declare" -> Declare
                  "forall" -> Forall
                  "as" -> As
                  "end" -> End
                  "case" -> Case
                  "of" -> Of
                  _ -> IdentLower txt
            P.effect (Builder.push token b0) >>= step
        | c >= '0' && c <= '9' -> do
            Unsafe.unconsume 1
            w <- Latin.decWord64 ()
            let !token = Integer (fromIntegral w)
            P.effect (Builder.push token b0) >>= step
        | otherwise -> P.fail ()

-- improve this
word8ToChar :: Word8 -> Char
word8ToChar = chr . fromIntegral
