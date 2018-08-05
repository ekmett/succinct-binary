module Data.Binary.Succinct.Blob
  ( Blob(..)
  , runPut
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
  { blobMeta :: CsPoppy
  , blobShape :: RangeMinMax (Storable.Vector Word64)
  , blobContent :: Storable.Vector Word64
  } deriving Show

runPutM :: PutM a -> (a, Blob)
runPutM ma = case unPutM ma' (S 0 0 0 0) of
    Result a _ (W m s c) -> (a, Blob 
      { blobMeta = makeCsPoppy $ nice m
      , blobShape = mkRangeMinMax $ nice s
      , blobContent = nice c
      })
  where
    pad = replicateM_ 7 $ putWord8 0
    flush8 = Bits.putAligned pad
    trim8 bs = Strict.take (Strict.length bs .&. complement 7) bs
    nice = byteStringToVector . trim8 . Lazy.toStrict . Builder.toLazyByteString
    ma' = do
      result <- ma
      meta flush8
      shape flush8
      content pad
      return result
  
runPut :: Put -> Blob
runPut = snd . runPutM
