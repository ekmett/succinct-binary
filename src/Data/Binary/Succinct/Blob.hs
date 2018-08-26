module Data.Binary.Succinct.Blob
  ( Blob(..)
  , blob
  -- guts
  , inspectMeta
  , inspectShape
  , inspectContent
  , inspectBlob
  ) where

import Data.Word
import Data.Bits
import Data.ByteString as Strict
import Data.ByteString.Builder as Builder
import Data.ByteString.Lazy as Lazy
import Data.Semigroup
import qualified Data.Vector.Storable as Storable
import HaskellWorks.Data.BalancedParens.RangeMinMax as BP
import HaskellWorks.Data.RankSelect.CsPoppy as CsPoppy
import HaskellWorks.Data.RankSelect.Base.Rank0
import Data.Vector.Storable.ByteString

import Data.Binary.Succinct.Put
import Data.Binary.Succinct.Orphans ()

data Blob = Blob
  { blobSize    :: Word64
  , blobMeta    :: CsPoppy
  , blobShape   :: RangeMinMax (Storable.Vector Word64)
  , blobContent :: Strict.ByteString
  } -- deriving Show

-- for debugging
instance Show Blob where
  show = inspectBlob

blob :: Put -> Blob
blob ma = case runPut ma (State 0 0 0 0) of
  Result (State i b j b') (W m s c n) -> Blob
    { blobSize = n
    , blobMeta = makeCsPoppy $ ws $ flush8 i b m
    , blobShape = mkRangeMinMax $ ws $ flush8 j b' s
    , blobContent = bs c
    }
  where
    flush :: Int -> Word8 -> Builder -> Builder
    flush 0 _ xs = xs
    flush _ b xs = xs <> word8 b

    flush8 :: Int -> Word8 -> Builder -> Builder
    flush8 r k d = flush r k d <> stimes (7 :: Int) (word8 0)

    trim8 :: Strict.ByteString -> Strict.ByteString
    trim8 b = Strict.take (Strict.length b .&. complement 7) b

    bs :: Builder -> Strict.ByteString
    bs = Lazy.toStrict . Builder.toLazyByteString

    ws :: Builder -> Storable.Vector Word64
    ws = byteStringToVector . trim8 . bs

access :: Rank1 v => v -> Word64 -> Word64
access s 1 = rank1 s 1
access s n = rank1 s n - rank1 s (n - 1)

as :: Rank1 v => a -> a -> v -> Word64 -> a
as l r s i = case access s i of
  0 -> l
  _ -> r

-- Print out a string of S's and D's, corresponding to Shape or Data, from the meta index
inspectMeta :: Blob -> String
inspectMeta (Blob n m _ _) = as 'D' 'S' m <$> [1..n]

-- Print out the balanced parentheses representation of our paren index
inspectShape :: Blob -> String
inspectShape (Blob n m s _) = as ')' '(' s <$> [1..rank1 m n]

-- Print out our raw content buffer
inspectContent :: Blob -> String
inspectContent (Blob _ _ _ c) = show c

-- Print out a representation of the entire blob, interleaving paren and content
inspectBlob :: Blob -> String
inspectBlob (Blob n m s c) = do
  i <- [1..n]
  case access m i of
    0 -> '{' : shows (Strict.index c $ fromIntegral $ rank0 m i - 1) "}"
    _ -> [as ')' '(' s $ rank1 m i]
