{-# language DeriveFunctor #-}
module Data.Binary.Succinct.Get 
  ( Get(..)
  , getPair
  , get8
  ) where

import Control.Monad (ap)
import Data.Binary.Succinct.Blob
import Data.ByteString as Strict
import Data.Maybe
import Data.Vector.Storable as Storable
import Data.Word
import HaskellWorks.Data.BalancedParens.RangeMinMax as BP
import HaskellWorks.Data.BalancedParens.BalancedParens as BP
import HaskellWorks.Data.RankSelect.Base.Rank1
import HaskellWorks.Data.RankSelect.Base.Select1

newtype Get a = Get { unGet :: Blob -> Word64 -> a }
  deriving Functor

instance Applicative Get where
  pure a = Get $ \_ _ -> a
  (<*>) = ap

instance Monad Get where
  m >>= k = Get $ \e s -> unGet (k (unGet m e s)) e s

shapely
  :: (RangeMinMax (Storable.Vector Word64) -> Word64 -> Maybe Word64)
  -> Blob
  -> Word64
  -> Word64
shapely k b@(Blob meta shape _) i
  = select1 meta
  . fromMaybe (error $ "bad shape: " <> show (b,i))
  . k shape
  . rank1 meta
  $ i

getPair :: Get a -> Get b -> Get (a, b)
getPair (Get l) (Get r) = Get $ \d i -> let
    j = shapely firstChild d i
    k = shapely nextSibling d j
  in (l d j, r d k)

get8 :: Get Word8
get8 = Get $ \(Blob meta _ content) i ->
  Strict.index content $ fromIntegral $ rank0' meta i

rank0' :: Rank1 v => v -> Word64 -> Word64 
rank0' s i = i - rank1 s i
