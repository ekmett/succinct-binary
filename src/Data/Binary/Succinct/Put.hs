{-# language DeriveFunctor #-}
{-# language DefaultSignatures #-}
{-# language FlexibleContexts #-}
{-# language BangPatterns #-}
{-# language EmptyCase #-}
{-# language GADTs #-}
{-# language TypeOperators #-}
{-# options_ghc -funbox-strict-fields #-}
module Data.Binary.Succinct.Put {- .Internal -}
  ( Put, PutM(..)
  , meta, shape, content
  -- guts
  , S(..)
  , W(..)
  , Result(..)
  , putParens
  , put8
  , Puttable(..)
  , putN
  , putN_
  , gput
  ) where

import Control.Monad (ap, replicateM_)
import Data.Bits
import Data.Bits.Coding
import Data.Bytes.Put
import Data.ByteString as Strict
import Data.ByteString.Builder
import Data.Int
import Data.Proxy
import qualified Data.Serialize.Put as S
-- import Data.Void
import Data.Word
import qualified GHC.Generics as G
import Data.Functor.Compose as F
import Data.Functor.Product as F
import Data.Functor.Sum as F
import qualified Generics.SOP as SOP
import qualified Generics.SOP.GGP as SOP

putLSB :: MonadPut m => Bool -> Coding m ()
putLSB v = Coding $ \k i b ->
  if i == 7
  then do
    putWord8 (pushBit b i v)
    k () 0 0
  else (k () $! i + 1) $! pushBit b i v
  where
    pushBit w i False = clearBit w i
    pushBit w i True  = setBit   w i

data S = S !Int !Word8 !Int !Word8
data W = W !Builder !Builder !Builder

instance Semigroup W where
  W a b c <> W d e f = W (a <> d) (b <> e) (c <> f)

instance Monoid W where
  mempty = W mempty mempty mempty
  mappend = (<>)

data Result a = Result a {-# UNPACK #-} !S {-# UNPACK #-} !W
  deriving Functor

type Put = PutM ()

newtype PutM a = PutM { unPutM :: S -> Result a }
  deriving Functor

instance Applicative PutM where
  pure a = PutM $ \s -> Result a s mempty
  (<*>) = ap

instance Monad PutM where
  PutM m >>= f = PutM $ \s -> case m s of
    Result a s' w -> case unPutM (f a) s' of
      Result b s'' w' -> Result b s'' (w <> w')

-- your job is to properly deal with managing meta, shape and content coherently

meta :: Coding S.PutM a -> PutM a
meta m = PutM $ \(S o1 d1 o2 d2) -> case S.runPutMBuilder (runCoding m go o1 d1) of
  ((a,o1',d1'), builder) -> Result a (S o1' d1' o2 d2) (W builder mempty mempty)
  where
    go :: a -> Int -> Word8 -> S.PutM (a, Int, Word8)
    go a o1' d1' = pure (a, o1', d1')

shape :: Coding S.PutM a -> PutM a
shape m = PutM $ \(S o1 d1 o2 d2) -> case S.runPutMBuilder (runCoding m go o2 d2) of
  ((a, o2', d2'), b) -> Result a (S o1 d1 o2' d2') (W b mempty mempty)
  where
    go :: a -> Int -> Word8 -> S.PutM (a, Int, Word8)
    go a o2' d2' = pure (a, o2', d2')

-- should this log how much is put and just automatically scribble into shape?
-- PutM doesn't give us enough info to do that efficiently.
content :: S.PutM a -> PutM a
content m = PutM $ \s -> case S.runPutMBuilder m of
  (a, b) -> Result a s (W mempty mempty b)

{-
  meta
  11110000110000111100000011 poppy, compact, not succinct
     /                     \
     content              shape
  #1 #2 #2 'h' 'i'    (((()()))())
                      000010111011
-}

putParen :: Bool -> Put
putParen p = do
  meta $ putLSB True
  shape $ putLSB p

putParens :: Put -> Put
putParens p = putParen False *> p <* putParen True

put8 :: Word8 -> Put
put8 w = meta (putLSB False) *> content (putWord8 w)

putN :: Int -> S.Put -> Put
-- TODO: replace that replicateM_ !!!
putN i w = meta (replicateM_ i $ putLSB False) *> content w

putN_ :: S.Put -> Put
-- TODO: replace that replicateM_ !!!
putN_ w = meta (replicateM_ n $ putLSB False) *> content (S.putByteString bs)
  where
    bs = S.runPut w
    n = Strict.length bs

--------------------------------------------------------------------------------
-- * Puttable
--------------------------------------------------------------------------------

class Puttable a where
  put :: a -> Put
  default put :: (G.Generic a, SOP.GFrom a, SOP.All2 Puttable (SOP.GCode a)) => a -> Put
  put = gput

gput :: (G.Generic a, SOP.GFrom a, SOP.All2 Puttable (SOP.GCode a)) => a -> Put
gput xs0 = case SOP.lengthSList sop of
    1 -> case sop of
      SOP.SOP (SOP.Z xs) -> putParens (products xs)
      _ -> error "the impossible happened"
    _ -> sums 0 sop
  where
    sop = SOP.gfrom xs0

    sums :: SOP.All2 Puttable xss => Word8 -> SOP.SOP SOP.I xss -> Put
    sums !acc (SOP.SOP (SOP.Z xs)) = putParens (put8 acc *> products xs)
    sums acc (SOP.SOP (SOP.S xss)) = sums (acc + 1) (SOP.SOP xss)

    products :: SOP.All Puttable xs => SOP.NP SOP.I xs -> Put
    products SOP.Nil = pure ()
    products (SOP.I x SOP.:* xs) = putParens (put x) *> products xs

instance Puttable Word64 where
  put = putN 8 . S.putWord64le

instance Puttable Word32 where
  put = putN 4 . S.putWord32le

instance Puttable Word16 where
  put = putN 2 . S.putWord16le

instance Puttable Word8 where
  put = putN 1 . S.putWord8

instance Puttable Int64 where
  put = putN 8 . S.putInt64le

instance Puttable Int32 where
  put = putN 4 . S.putInt32le

instance Puttable Int16 where
  put = putN 2 . S.putInt16le

instance Puttable Int8 where
  put = putN 1 . S.putInt8

-- instance Puttable Void -- TODO: fix GSumFrom in Generics.SOP to allow V1
instance Puttable ()
instance Puttable (Proxy a)
instance Puttable a => Puttable (Maybe a)
instance Puttable a => Puttable [a]
instance (Puttable a, Puttable b) => Puttable (a, b)
instance (Puttable a, Puttable b) => Puttable (Either a b)
instance Puttable (f (g a)) => Puttable (Compose f g a)
instance (Puttable (f a), Puttable (g a)) => Puttable (F.Product f g a)
instance (Puttable (f a), Puttable (g a)) => Puttable (F.Sum f g a)
