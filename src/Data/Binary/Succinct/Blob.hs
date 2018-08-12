module Data.Binary.Succinct.Blob
  ( Blob(..)
  , runPut
  , blob
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
import Data.Vector.Storable.ByteString

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

rank1_ :: Rank1 v => v -> Word64 -> Word64
rank1_ s i
  | i <= 0 = 0
  | otherwise = rank1 s i

access :: Rank1 v => v -> Word64 -> Bool
access s i = toEnum $ fromIntegral $ rank1_ s i - rank1_ s (i - 1)

-- currently segfaults
blob :: Blob -> String
blob (Blob m s _c) = do
  i <- [0..fromIntegral $ Storable.length (csPoppyBits m)*64-1]
  case access m i of
    True -> case access s (rank1_ m i) of
      False -> "("
      True -> ")"
    False -> "D" -- data
