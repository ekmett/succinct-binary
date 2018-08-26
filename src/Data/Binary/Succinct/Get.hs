{-# language DeriveFunctor #-}
{-# language DefaultSignatures #-}
{-# language FlexibleContexts #-}
{-# language EmptyCase #-}
{-# language GADTs #-}
{-# language PolyKinds #-}
{-# language DataKinds #-}
{-# language ScopedTypeVariables #-}
{-# language TypeApplications #-}
{-# language TypeOperators #-}
module Data.Binary.Succinct.Get where

foo :: Int
foo = 1

{-
  ( Get(..)
  , get8
  , Gettable(..)
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
import Debug.Trace
import GHC.Generics as G
import qualified Generics.SOP as SOP
import qualified Generics.SOP.GGP as SOP

import HaskellWorks.Data.BalancedParens.RangeMinMax as BP
import HaskellWorks.Data.BalancedParens.BalancedParens as BP
import HaskellWorks.Data.RankSelect.Base.Rank0
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

move :: (RangeMinMax (Storable.Vector Word64) -> Word64 -> Maybe Word64)
  -> Get a -> Get a
move f m = Get $ \d i -> runGet m d (shapely f d i)

get8 :: Get Word8
get8 = Get $ \(Blob meta _ content) i ->
  let result = Strict.index content $ fromIntegral $ rank0 meta i in
  traceShow ("get8",i,result) result

liftGet :: S.Get a -> Get a
liftGet g = Get $ \(Blob meta _ content) i ->
  case S.runGet g $ Strict.drop (fromIntegral $ rank0 meta i) content of
    Left e -> error e
    Right a -> a

--------------------------------------------------------------------------------
-- * Gettable
--------------------------------------------------------------------------------

class Gettable a where
  get :: Get a
  default get :: (G.Generic a, SOP.GTo a, SOP.All2 Gettable (SOP.GCode a))
              => Get a
  get = gget

gget :: forall a.  (G.Generic a, SOP.GTo a, SOP.All2 Gettable (SOP.GCode a))
     => Get a
gget = case SOP.shape :: SOP.Shape (SOP.GCode a) of
    SOP.ShapeCons SOP.ShapeNil -> SOP.gto . SOP.SOP . SOP.Z
                              <$> move firstChild (products SOP.shape)
    n -> do
      k <- get8
      traceShow ("read tag",k) $ SOP.gto . SOP.SOP <$> sums k n
  where
    sums :: SOP.All2 Gettable xss
         => Word8
         -> SOP.Shape xss
         -> Get (SOP.NS (SOP.NP SOP.I) xss)
    -- do we need to add a case for where the firstChild doesn't have any content
    -- when the Shape of the products is empty

    sums 0 (SOP.ShapeCons _) = SOP.Z <$> move firstChild (products SOP.shape)
    sums k (SOP.ShapeCons xs) = SOP.S <$> sums (k-1) xs
    sums _ SOP.ShapeNil = error "bad tag"

    products :: SOP.All Gettable xs => SOP.Shape xs -> Get (SOP.NP SOP.I xs)
    products SOP.ShapeNil = return SOP.Nil
    products (SOP.ShapeCons SOP.ShapeNil) = fmap (\a -> SOP.I a SOP.:* SOP.Nil) get
    products (SOP.ShapeCons xs) = do
      a <- get
      as <- move nextSibling (products xs)
      return $ SOP.I a SOP.:* as

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

-}
