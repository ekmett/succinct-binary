module Data.Binary.Succinct.Blob
  ( Blob(..)
  , runPut
  -- guts
  , metaBitCount
  , shapeBitCount
  , contentByteCount
  , inspectMeta
  , inspectShape
  , inspectContent
  , inspectBlob
  ) where

import Control.Monad (replicateM_)
import Data.Word
import Data.Bits
import Data.Bits.Coding as Bits
import Data.Bytes.Put
import Data.ByteString as Strict
import Data.ByteString.Builder as Builder
import Data.ByteString.Lazy as Lazy
import qualified Data.Vector.Storable as Storable
import HaskellWorks.Data.BalancedParens.RangeMinMax as BP
import HaskellWorks.Data.RankSelect.CsPoppy as CsPoppy
import HaskellWorks.Data.RankSelect.Base.Rank0
import Data.Vector.Storable.ByteString
import HaskellWorks.Data.BalancedParens

import Data.Binary.Succinct.Put
import Data.Binary.Succinct.Orphans ()

data Blob = Blob
  { blobMeta    :: CsPoppy
  , blobShape   :: RangeMinMax (Storable.Vector Word64)
  , blobContent :: Strict.ByteString
  } deriving Show

runPutM :: PutM a -> (a, Blob)
runPutM ma = case unPutM ma' (S 0 0 0 0) of
    Result a _ (W m s c) -> (a, Blob 
      { blobMeta = makeCsPoppy $ ws m
      , blobShape = mkRangeMinMax $ ws s
      , blobContent = bs c
      })
  where
    pad = replicateM_ 7 $ putWord8 0
    flush8 = Bits.putAligned pad
    trim8 b = Strict.take (Strict.length b .&. complement 7) b
    bs = Lazy.toStrict . Builder.toLazyByteString
    ws = byteStringToVector . trim8 . bs
    ma' = do
      result <- ma
      meta flush8
      shape flush8
      -- content pad
      return result
  
runPut :: Put -> Blob
runPut = snd . runPutM

rank1_ :: Rank1 v => v -> Int -> Word64
rank1_ s i
  | i <= 0 = 0
  | otherwise = rank1 s (fromIntegral i)

rank0_ :: Rank0 v => v -> Int -> Word64
rank0_ s i
  | i <= 0 = 0
  | otherwise = rank0 s (fromIntegral i)

access :: Rank1 v => v -> Int -> Bool
access s i = toEnum $ fromIntegral $ rank1_ s i - rank1_ s (i - 1)

-- Compute how many bits the shape index takes up
--   We use findClose on the first paren to tell us where the last meaningful paren is
shapeBitCount :: Blob -> Int
shapeBitCount (Blob _ s _) = case findClose s 1 of
  Just n -> fromIntegral n
  Nothing -> 0

-- Compute how many bytes the content takes up
contentByteCount :: Blob -> Int
contentByteCount (Blob _ _ c) = Strict.length c

-- Compute how many bits are non-garbage in our meta index
metaBitCount :: Blob -> Int
metaBitCount b = contentByteCount b + shapeBitCount b

-- Print out a string of S's and D's, corresponding to Shape or Data, from the meta index
inspectMeta :: Blob -> String
inspectMeta b@(Blob m _ _) = do
  i <- [1..(metaBitCount b)]
  case access m i of
    True -> "S"
    False -> "D"

-- Print out the balanced parentheses representation of our shape index
inspectShape :: Blob -> String
inspectShape b@(Blob _ s _) = do
  i <- [1..(shapeBitCount b)]
  case access s i of
    True  -> "("
    False -> ")"

-- Print out our raw content buffer
-- Can't figure out how to print strict bytestrings nicely...
inspectContent :: Blob -> String
inspectContent (Blob _ _ _) = undefined 

-- Print out a representation of the entire blob, interleaving shape and content
inspectBlob :: Blob -> String
inspectBlob b@(Blob m s c) = do
  i <- [1..(metaBitCount b)]
  case access m i of
    True  -> case access s (fromIntegral $ rank1_ m i) of
      True  -> "("
      False -> ")"
    False -> "{" ++ show (Strict.index c $ (fromIntegral $ rank0_ m i) - 1) ++ "}"