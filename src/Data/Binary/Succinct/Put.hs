{-# language DeriveFunctor #-}
{-# language LambdaCase #-}
{-# language DefaultSignatures #-}
{-# language FlexibleContexts #-}
{-# language EmptyCase #-}
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
  , putPair
  , put8
  , Puttable(..)
  , GPuttable(..)
  , Puttable1(..)
  , GPuttable1(..)
  , putN
  , putN_
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
import Data.Void
import Data.Word
import qualified GHC.Generics as G
import Data.Functor.Compose as F
import Data.Functor.Product as F
import Data.Functor.Sum as F

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
meta m = PutM $ \(S o1 d1 o2 d2) -> case S.getPutM (runCoding m go o1 d1) of
  ((a,o1',d1'), builder) -> Result a (S o1' d1' o2 d2) (W builder mempty mempty)
  where
    go :: a -> Int -> Word8 -> S.PutM (a, Int, Word8)
    go a o1' d1' = pure (a, o1', d1')

shape :: Coding S.PutM a -> PutM a
shape m = PutM $ \(S o1 d1 o2 d2) -> case S.getPutM (runCoding m go o2 d2) of
  ((a, o2', d2'), b) -> Result a (S o1 d1 o2' d2') (W b mempty mempty)
  where
    go :: a -> Int -> Word8 -> S.PutM (a, Int, Word8)
    go a o2' d2' = pure (a, o2', d2')

-- should this log how much is put and just automatically scribble into shape?
-- PutM doesn't give us enough info to do that efficiently.
content :: S.PutM a -> PutM a
content m = PutM $ \s -> case S.getPutM m of
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

putPair :: (a -> Put) -> (b -> Put) -> (a, b) -> Put
putPair l r (a,b) = putParens (putParens (l a) *> putParens (r b))

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
  default put :: (G.Generic a, GPuttable (G.Rep a)) => a -> Put
  put = gput . G.from

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

instance Puttable Void
instance Puttable ()
instance Puttable (Proxy a)
instance Puttable a => Puttable (Maybe a)
instance Puttable a => Puttable [a]
instance (Puttable a, Puttable b) => Puttable (a, b)
instance (Puttable a, Puttable b) => Puttable (Either a b)
instance Puttable (f (g a)) => Puttable (Compose f g a)
instance (Puttable (f a), Puttable (g a)) => Puttable (F.Product f g a)
instance (Puttable (f a), Puttable (g a)) => Puttable (F.Sum f g a)

--------------------------------------------------------------------------------
-- * GPuttable
--------------------------------------------------------------------------------

class GPuttable t where
  gput :: t a -> Put

instance GPuttable G.U1 where
  gput _ = pure ()

instance GPuttable G.V1 where
  gput = \case

instance Puttable c => GPuttable (G.K1 i c) where
  gput = put . G.unK1

instance GPuttable f => GPuttable (G.M1 i c f) where
  gput = gput . G.unM1

instance (GPuttable f, GPuttable g) => GPuttable (f G.:*: g) where
  gput (a G.:*: b) = putParens $ putParens (gput a) *> putParens (gput b)

instance (GPuttable f, GPuttable g) => GPuttable (f G.:+: g) where
  gput (G.L1 a) = put8 0 *> gput a
  gput (G.R1 b) = put8 1 *> gput b

instance (Puttable1 f, GPuttable g) => GPuttable (f G.:.: g) where
  gput = put1 gput . G.unComp1

--------------------------------------------------------------------------------
-- * Puttable1
--------------------------------------------------------------------------------

class Puttable1 f where
  put1 :: (a -> Put) -> f a -> Put
  default put1 :: (G.Generic1 f, GPuttable1 (G.Rep1 f)) => (a -> Put) -> f a -> Put
  put1 f = gput1 f . G.from1

instance Puttable1 Proxy
instance Puttable1 Maybe
instance Puttable1 []
instance Puttable a => Puttable1 (Either a)
instance Puttable a => Puttable1 ((,) a)
instance (Functor f, Puttable1 f, Puttable1 g) => Puttable1 (Compose f g)
instance (Puttable1 f, Puttable1 g) => Puttable1 (F.Product f g)
instance (Puttable1 f, Puttable1 g) => Puttable1 (F.Sum f g)

--------------------------------------------------------------------------------
-- * GPuttable1
--------------------------------------------------------------------------------

class GPuttable1 f where 
  gput1 :: (a -> Put) -> f a -> Put

instance GPuttable1 G.U1 where
  gput1 _ _ = pure ()

instance GPuttable1 G.V1 where
  gput1 _ = \case

instance (GPuttable1 f, GPuttable1 g) => GPuttable1 (f G.:*: g) where
  gput1 f (a G.:*: b) = putParens $ putParens (gput1 f a) *> putParens (gput1 f b)

instance (GPuttable1 f, GPuttable1 g) => GPuttable1 (f G.:+: g) where
  gput1 f (G.L1 a) = put8 0 *> gput1 f a
  gput1 f (G.R1 b) = put8 1 *> gput1 f b

instance (Puttable1 f, GPuttable1 g) => GPuttable1 (f G.:.: g) where
  gput1 f = put1 (gput1 f) . G.unComp1

instance Puttable c => GPuttable1 (G.K1 i c) where
  gput1 _ = put . G.unK1

instance GPuttable1 f => GPuttable1 (G.M1 i c f) where
  gput1 f = gput1 f . G.unM1

instance Puttable1 f => GPuttable1 (G.Rec1 f) where
  gput1 f = put1 f . G.unRec1

instance GPuttable1 G.Par1 where
  gput1 f = f . G.unPar1
