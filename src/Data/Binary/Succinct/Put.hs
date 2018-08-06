{-# language DeriveFunctor #-}
{-# language LambdaCase #-}
{-# language UndecidableInstances #-}
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
  ) where

import Control.Monad (ap)
import Data.Bits
import Data.Bits.Coding
import Data.Bytes.Put
import Data.ByteString.Builder
import qualified Data.Serialize.Put as Cereal
import Data.Word
import qualified GHC.Generics as G

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

meta :: Coding Cereal.PutM a -> PutM a
meta m = PutM $ \(S o1 d1 o2 d2) -> case Cereal.getPutM (runCoding m go o1 d1) of
  ((a,o1',d1'), builder) -> Result a (S o1' d1' o2 d2) (W builder mempty mempty)
  where
    go :: a -> Int -> Word8 -> Cereal.PutM (a, Int, Word8)
    go a o1' d1' = pure (a, o1', d1')

shape :: Coding Cereal.PutM a -> PutM a
shape m = PutM $ \(S o1 d1 o2 d2) -> case Cereal.getPutM (runCoding m go o2 d2) of
  ((a, o2', d2'), b) -> Result a (S o1 d1 o2' d2') (W b mempty mempty)
  where
    go :: a -> Int -> Word8 -> Cereal.PutM (a, Int, Word8)
    go a o2' d2' = pure (a, o2', d2')

-- should this log how much is put and just automatically scribble into shape?
-- PutM doesn't give us enough info to do that efficiently.
content :: Cereal.PutM a -> PutM a
content m = PutM $ \s -> case Cereal.getPutM m of
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

class Puttable a where
  put :: a -> Put
  default put :: (G.Generic a, GPuttable (G.Rep a)) => a -> Put
  put = gput . G.from

instance Puttable ()

instance Puttable Word8 where
  put = put8

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

class Puttable1 f where
  put1 :: (a -> Put) -> f a -> Put
  default put1 :: (G.Generic1 f, GPuttable1 (G.Rep1 f)) => (a -> Put) -> f a -> Put
  put1 f = gput1 f . G.from1

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
