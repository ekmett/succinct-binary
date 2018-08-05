{-# language DeriveFunctor #-}
{-# options_ghc -funbox-strict-fields #-}
module Data.Binary.Succinct.Put {- .Internal -}
  ( Put, PutM(..)
  , meta, shape, content
  -- guts
  , S(..)
  , W(..)
  , Result(..)
  ) where

import Control.Monad (ap)
import Data.ByteString.Builder
import qualified Data.Serialize.Put as Cereal
import Data.Bits.Coding
import Data.Word

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

-- this should be Coding Cereal.Put a -> Put a, but our APIs suck
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

content :: Cereal.PutM a -> PutM a
content m = PutM $ \s -> case Cereal.getPutM m of
  (a, b) -> Result a s (W mempty mempty b)

-- we need some kind of storable.vector word64 builder

{-
  meta
  00001111001111000011111100 -- poppy, compact, not succinct
     /              \
   shape           content
(((()()))())   #1 #2 #2 'h' 'i'
000010111011
-}
