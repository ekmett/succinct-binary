{-# language DeriveFunctor #-}
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
  ) where

import Control.Monad (ap)
import Data.Bits
import Data.Bits.Coding
import Data.Bytes.Put
import Data.ByteString.Builder
import qualified Data.Serialize.Put as Cereal
import Data.Word

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
