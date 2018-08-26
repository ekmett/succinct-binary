{-# language DeriveFunctor #-}
{-# language DefaultSignatures #-}
{-# language FlexibleContexts #-}
{-# language BangPatterns #-}
{-# language EmptyCase #-}
{-# language GADTs #-}
{-# language TypeOperators #-}
{-# language RankNTypes #-}
{-# language TypeApplications #-}
{-# language ScopedTypeVariables #-}
{-# options_ghc -funbox-strict-fields #-}
module Data.Binary.Succinct.Put {- .Internal -}
  ( Put(..)
  -- guts
  , meta, metas, paren, parens, content
  , State(..)
  , W(..)
  , Result(..)
  , put8
  , Puttable(..)
  , putN
  , putN_
  , gput
  ) where

import Data.Bits
import Data.ByteString.Lazy as Lazy
import Data.ByteString.Builder as Builder
import Data.Int
import Data.Proxy
import Data.Semigroup
import Data.Void
import Data.Word
import qualified GHC.Generics as G
import Data.Functor.Compose as F
import Data.Functor.Product as F
import Data.Functor.Sum as F
import qualified Generics.SOP as SOP
import qualified Generics.SOP.GGP as SOP

import Data.Binary.Succinct.Size

data State = State !Int !Word8 !Int !Word8
data W = W !Builder !Builder !Builder !Word64

instance Semigroup W where
  W a b c m <> W d e f n = W (a <> d) (b <> e) (c <> f) (m + n)

instance Monoid W where
  mempty = W mempty mempty mempty 0
  mappend = (<>)

data Result = Result {-# UNPACK #-} !State {-# UNPACK #-} !W

newtype Put = Put { runPut :: State -> Result }

instance Semigroup Put where
  f <> g = Put $ \s -> case runPut f s of
    Result s' m -> case runPut g s' of
      Result s'' n -> Result s'' (m <> n)

instance Monoid Put where
  mempty = Put $ \s -> Result s mempty

push :: Bool -> Int -> Word8 -> (Builder, Int, Word8)
push v i b
  | i == 7    = (Builder.word8 b', 0, 0)
  | otherwise = (mempty, i + 1, b')
  where b' = if v then setBit b i else b
{-# INLINE push #-}

meta :: Bool -> Put
meta v = Put $ \(State i b j c) -> case push v i b of
  (m,i',b') -> Result (State i' b' j c) (W m mempty mempty 1)

paren :: Bool -> Put
paren v = Put $ \(State i b j c) -> case push v j c of
  (s,j',c') -> case push True i b of
    (m, i', b') -> Result (State i' b' j' c') (W m s mempty 1)

parens :: Put -> Put
parens p = paren True <> p <> paren False

-- push a run of 0s into the meta buffer
metas :: Int -> Put
metas k
  | k <= 0 = mempty
  | otherwise = Put $ \(State i b j c) -> case divMod (i + k) 8 of
    (0,r) -> Result (State r b j c) $ W mempty mempty mempty (fromIntegral k)
    (q,r) -> Result (State r 0 j c) $
      W (Builder.word8 b <> stimesMonoid (q-1) (Builder.word8 0))
        mempty
        mempty
        (fromIntegral k)

content :: Builder -> Put
content m = Put $ \s -> Result s (W mempty mempty m 0)

put8 :: Word8 -> Put
put8 x = meta False <> content (word8 x)

putN :: Int -> Builder -> Put
putN i w = metas i <> content w

putN_ :: Builder -> Put
putN_ w = putN (fromIntegral $ Lazy.length bs) (Builder.lazyByteString bs) where
  bs = Builder.toLazyByteString w

--------------------------------------------------------------------------------
-- * Puttable
--------------------------------------------------------------------------------

class Sized a => Puttable a where
  put :: a -> Put
  default put :: (G.Generic a, SOP.GFrom a, SOP.All2 Puttable (SOP.GCode a)) => a -> Put
  put = gput

gput :: (G.Generic a, SOP.GFrom a, SOP.All2 Puttable (SOP.GCode a)) => a -> Put
gput xs0 = case SOP.lengthSList sop of
    1 -> case sop of
      SOP.Z xs -> products xs
      _ -> error "the impossible happened"
    _ -> sums 0 sop
  where
    SOP.SOP sop = SOP.gfrom xs0

    sums :: SOP.All2 Puttable xss => Word8 -> SOP.NS (SOP.NP SOP.I) xss -> Put
    sums !acc (SOP.Z xs) = put8 acc <> products xs
    sums acc (SOP.S xss) = sums (acc + 1) xss

    products :: SOP.All Puttable xs => SOP.NP SOP.I xs -> Put
    products SOP.Nil = mempty
    products (SOP.I x SOP.:* xs) = products1 x xs

    -- the last field is written without parens
    products1 :: (Puttable x, SOP.All Puttable xs) => x -> SOP.NP SOP.I xs -> Put
    products1 x SOP.Nil = put x
    products1 x (SOP.I y SOP.:* ys) = putWithParens x <> products1 y ys

putWithParens :: forall a. Puttable a => a -> Put
putWithParens = case size @a of
  Variable -> parens . put
  _ -> put

instance Puttable Void where
  put = absurd

instance Puttable Word64 where
  put = putN 8 . Builder.word64LE

instance Puttable Word32 where
  put = putN 4 . Builder.word32LE

instance Puttable Word16 where
  put = putN 2 . Builder.word16LE

instance Puttable Word8 where
  put = putN 1 . Builder.word8

instance Puttable Int64 where
  put = putN 8 . Builder.int64LE

instance Puttable Int32 where
  put = putN 4 . Builder.int32LE

instance Puttable Int16 where
  put = putN 2 . Builder.int16LE

instance Puttable Int8 where
  put = putN 1 . Builder.int8

instance Puttable Char where
  put = put . (fromIntegral . fromEnum :: Char -> Word32)

instance Puttable ()
instance Puttable (Proxy a)
instance Puttable a => Puttable (Maybe a)
instance Puttable a => Puttable [a]
instance (Puttable a, Puttable b) => Puttable (a, b)
instance (Puttable a, Puttable b) => Puttable (Either a b)
instance Puttable (f (g a)) => Puttable (Compose f g a)
instance (Puttable (f a), Puttable (g a)) => Puttable (F.Product f g a)
instance (Puttable (f a), Puttable (g a)) => Puttable (F.Sum f g a)
