{-# language DeriveFunctor #-}
{-# language DefaultSignatures #-}
{-# language FlexibleContexts #-}
{-# language EmptyCase #-}
{-# language TypeOperators #-}
{-# language LambdaCase #-}
module Data.Binary.Succinct.Get 
  ( Get(..)
  , getPair
  , get8
  , Gettable(..)
  , GGettable(..)
  , Gettable1(..)
  , GGettable1(..)
  , liftGet
  ) where

import Control.Monad (ap)
import Data.Binary.Succinct.Blob
import Data.ByteString as Strict
import Data.Functor.Compose as F
import Data.Functor.Product as F
import Data.Functor.Sum as F
import Data.Int
import Data.Maybe
import Data.Proxy
import qualified Data.Serialize.Get as S
import Data.Vector.Storable as Storable
import Data.Word
import GHC.Generics as G

import HaskellWorks.Data.BalancedParens.RangeMinMax as BP
import HaskellWorks.Data.BalancedParens.BalancedParens as BP
import HaskellWorks.Data.RankSelect.Base.Rank1
import HaskellWorks.Data.RankSelect.Base.Select1

newtype Get a = Get { runGet :: Blob -> Word64 -> a }
  deriving Functor

instance Applicative Get where
  pure a = Get $ \_ _ -> a
  (<*>) = ap

instance Monad Get where
  m >>= k = Get $ \e s -> runGet (k (runGet m e s)) e s

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

liftGet :: S.Get a -> Get a
liftGet g = Get $ \(Blob meta _ content) i ->
  case S.runGet g $ Strict.drop (fromIntegral $ rank0' meta i) content of
    Left e -> error e
    Right a -> a

rank0' :: Rank1 v => v -> Word64 -> Word64 
rank0' s i = i - rank1 s i

--------------------------------------------------------------------------------
-- * GGettable
--------------------------------------------------------------------------------

class Gettable a where
  get :: Get a
  default get :: (G.Generic a, GGettable (G.Rep a)) => Get a
  get = G.to <$> gget 

instance Gettable ()
instance Gettable Word8 where
  get = get8

instance Gettable Word16 where get = liftGet S.getWord16le
instance Gettable Word32 where get = liftGet S.getWord32le
instance Gettable Word64 where get = liftGet S.getWord64le
instance Gettable Int8 where get = liftGet S.getInt8
instance Gettable Int16 where get = liftGet S.getInt16le
instance Gettable Int32 where get = liftGet S.getInt32le
instance Gettable Int64 where get = liftGet S.getInt64le

instance Gettable (Proxy a)
instance Gettable a => Gettable (Maybe a)
instance Gettable a => Gettable [a]
instance (Gettable a, Gettable b) => Gettable (a, b)
instance (Gettable a, Gettable b) => Gettable (Either a b)
instance Gettable (f (g a)) => Gettable (F.Compose f g a)
instance (Gettable (f a), Gettable (g a)) => Gettable (F.Product f g a)
instance (Gettable (f a), Gettable (g a)) => Gettable (F.Sum f g a)

--------------------------------------------------------------------------------
-- * GGettable
--------------------------------------------------------------------------------

class GGettable t where
  gget :: Get (t a)

instance GGettable U1 where
  gget = pure U1

instance Gettable c => GGettable (K1 i c) where
  gget = K1 <$> get

instance GGettable f => GGettable (M1 i c f) where
  gget = M1 <$> gget

instance (GGettable f, GGettable g) => GGettable (f :*: g) where
  gget = Get $ \d i -> let
      j = shapely firstChild d i
      k = shapely nextSibling d j
    in runGet gget d j :*: runGet gget d k

instance (GGettable f, GGettable g) => GGettable (f :+: g) where
  gget = Get $ \d i -> case runGet get8 d i of
    0 -> L1 $ runGet gget d (i+1)
    1 -> R1 $ runGet gget d (i+1)
    _ -> error "bad data"

instance (Gettable1 f, GGettable g) => GGettable (f :.: g) where
  gget = Comp1 <$> get1 gget

--------------------------------------------------------------------------------
-- * Gettable1
--------------------------------------------------------------------------------

class Gettable1 f where
  get1 :: Get a -> Get (f a)
  default get1 :: (G.Generic1 f, GGettable1 (G.Rep1 f)) => Get a -> Get (f a)
  get1 f = G.to1 <$> gget1 f

instance Gettable1 Proxy
instance Gettable1 []
instance Gettable1 Maybe
instance Gettable a => Gettable1 (Either a)
instance Gettable a => Gettable1 ((,) a)
instance (Functor f, Gettable1 f, Gettable1 g) => Gettable1 (F.Compose f g)
instance (Gettable1 f, Gettable1 g) => Gettable1 (F.Product f g)
instance (Gettable1 f, Gettable1 g) => Gettable1 (F.Sum f g)

--------------------------------------------------------------------------------
-- * GGettable1
--------------------------------------------------------------------------------

class GGettable1 t where
  gget1 :: Get a -> Get (t a)

instance GGettable1 U1 where
  gget1 _ = pure U1

instance Gettable c => GGettable1 (K1 i c) where
  gget1 _ = K1 <$> get

instance GGettable1 f => GGettable1 (M1 i c f) where
  gget1 f = M1 <$> gget1 f

instance (GGettable1 f, GGettable1 g) => GGettable1 (f :*: g) where
  gget1 f = Get $ \d i -> let
      j = shapely firstChild d i
      k = shapely nextSibling d j
    in runGet (gget1 f) d j :*: runGet (gget1 f) d k

instance (GGettable1 f, GGettable1 g) => GGettable1 (f :+: g) where
  gget1 f = Get $ \d i -> case runGet get8 d i of
    0 -> L1 $ runGet (gget1 f) d (i+1)
    1 -> R1 $ runGet (gget1 f) d (i+1)
    _ -> error "bad data"

instance (Gettable1 f, GGettable1 g) => GGettable1 (f :.: g) where
  gget1 f = Comp1 <$> get1 (gget1 f)

instance Gettable1 f => GGettable1 (Rec1 f) where
  gget1 f = Rec1 <$> get1 f

instance GGettable1 Par1 where
  gget1 f = Par1 <$> f
