{-# language DeriveFunctor #-}
{-# language DefaultSignatures #-}
{-# language FlexibleContexts #-}
{-# language BangPatterns #-}
{-# language EmptyCase #-}
{-# language AllowAmbiguousTypes #-}
{-# language TypeApplications #-}
{-# language ScopedTypeVariables #-}
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

import Control.Monad (ap)
import Data.Bits
import Data.Semigroup
import Data.ByteString as Strict
import Data.ByteString.Builder as Builder
import Data.ByteString.UTF8 as UTF8
import Data.Int
import Data.Proxy
import qualified Data.Serialize.Put as S
import Data.Void
import Data.Word
import qualified GHC.Generics as G
import Data.Functor.Compose as F
import Data.Functor.Product as F
import Data.Functor.Sum as F
import qualified Generics.SOP as SOP
import qualified Generics.SOP.GGP as SOP

import Data.Binary.Succinct.Size

data S = S !Int !Word8 !Int !Word8
data W = W !Builder !Builder !Builder !Word64

instance Semigroup W where
  W a b c n <> W d e f m = W (a <> d) (b <> e) (c <> f) (n + m)

instance Monoid W where
  mempty = W mempty mempty mempty 0
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

push :: Bool -> Int -> Word8 -> (Builder, Int, Word8)
push v i b
  | i == 7    = (Builder.word8 b', 0, 0)
  | otherwise = (mempty, i + 1, b')
  where b' = if v then setBit b i else b
{-# INLINE push #-}

meta :: Bool -> PutM ()
meta v = PutM $ \(S i b j c) -> case push v i b of
  (m,i',b') -> Result () (S i' b' j c) $ W m mempty mempty 1

shape :: Bool -> PutM ()
shape v = PutM $ \(S i b j c) -> case push v j c of
  (s,j',c') -> case push True i b of
    (m, i', b') -> Result () (S i' b' j' c') $ W m s mempty 1

-- push a run of 0s into the meta buffer
metas :: Int -> PutM ()
metas k
  | k <= 0 = pure ()
  | otherwise = PutM $ \(S i b j c) -> case divMod (i + k) 8 of
    (0,r) -> Result () (S r b j c) $ W mempty mempty mempty (fromIntegral k)
    (q,r) -> Result () (S r 0 j c) $
      W (Builder.word8 b <> stimesMonoid (q-1) (Builder.word8 0))
        mempty
        mempty
        (fromIntegral k)

-- should this log how much is put and just automatically scribble into shape?
-- PutM doesn't give us enough info to do that efficiently.
content :: S.PutM a -> PutM a
content m = PutM $ \s -> case S.runPutMBuilder m of
  (a, b) -> Result a s (W mempty mempty b 0)

--  meta
--  11110000110000111100000011 poppy, compact, not succinct
--     /                     \
--     content              shape
--  #1 #2 #2 'h' 'i'    (((()()))())
--                      000010111011

putParens :: Put -> Put
putParens p = shape True *> p <* shape False

putBS :: ByteString -> Put
putBS bs = putN (Strict.length bs) (S.putByteString bs)

put8 :: Word8 -> Put
put8 w = meta False *> content (S.putWord8 w)

putN :: Int -> S.Put -> Put
putN i w = metas i *> content w

putN_ :: S.Put -> Put
putN_ w = putN (Strict.length bs) (S.putByteString bs) where
  bs = S.runPut w

--------------------------------------------------------------------------------
-- * Puttable
--------------------------------------------------------------------------------

class Sized a => Puttable a where
  put :: a -> Put
  default put :: (G.Generic a, SOP.GFrom a, SOP.All2 Puttable (SOP.GCode a)) => a -> Put
  put = gput

{-
(((a,b),c),d) -- (((a)b)c)d
((a,b),(c,d)) -- ((a)b)(c)d
(a,(b,(c,d))) -- (a)(b)(c)d

-- with b and c of known size:
(((a,b),c),d) -- (((a)b)c)d
((a,b),(c,d)) -- ((a)b)cd
(a,(b,(c,d))) -- (a)bcd
-}

gput :: (G.Generic a, SOP.GFrom a, SOP.All2 Puttable (SOP.GCode a)) => a -> Put
gput xs0 = case SOP.lengthSList sop of
    -- skip storing the data constructor when we have only one constructor
    -- TODO: skip when we only have one _possible_ constructor (skip size=Any constructors)
    1 -> case sop of
      SOP.Z xs -> products xs
      _ -> error "the impossible happened"
    _ -> sums 0 sop
  where
    SOP.SOP sop = SOP.gfrom xs0

    sums :: SOP.All2 Puttable xss => Word8 -> SOP.NS (SOP.NP SOP.I) xss -> Put
    sums !acc (SOP.Z xs) = put8 acc *> products xs
    sums acc (SOP.S xss) = sums (acc + 1) xss

    products :: SOP.All Puttable xs => SOP.NP SOP.I xs -> Put
    products SOP.Nil = pure ()
    products (SOP.I x SOP.:* xs) = products1 x xs

    -- the last field is written without parens
    -- TODO: the last variable width field should be written without parens
    products1 :: (Puttable x, SOP.All Puttable xs) => x -> SOP.NP SOP.I xs -> Put
    products1 x SOP.Nil = put x
    products1 x (SOP.I y SOP.:* ys) = putWithParens x *> products1 y ys

-- TODO: skip parens on fields from left to right when the field itself is strict all the way down
-- and can have its length calculated from its contents?
putWithParens :: forall a. Puttable a => a -> Put
putWithParens = case size @a of
  SVariable -> putParens . put
  _ -> put

-- (String,Int64,String)
-- ((a)bc)

instance Puttable Word8 where
  put = putN 1 . S.putWord8

instance Puttable Word16 where
  put = putN 2 . S.putWord16le

instance Puttable Word32 where
  put = putN 4 . S.putWord32le

instance Puttable Word64 where
  put = putN 8 . S.putWord64le

instance Puttable Int8 where
  put = putN 1 . S.putInt8

instance Puttable Int16 where
  put = putN 2 . S.putInt16le

instance Puttable Int32 where
  put = putN 4 . S.putInt32le

instance Puttable Int64 where
  put = putN 8 . S.putInt64le

instance Puttable Char where
  put = putBS . UTF8.fromString . pure

instance Puttable Bool
instance (Puttable a, Puttable b) => Puttable (Either a b)
instance Puttable a => Puttable (Maybe a)
instance Puttable Ordering
instance Puttable (Proxy a)
--instance Puttable Void
instance Puttable a => Puttable [a]
instance Puttable ()
instance (Puttable a, Puttable b) => Puttable (a, b)
instance (Puttable a, Puttable b, Puttable c) => Puttable (a, b, c)
instance (Puttable a, Puttable b, Puttable c, Puttable d) => Puttable (a, b, c, d)
instance (Puttable a, Puttable b, Puttable c, Puttable d, Puttable e) => Puttable (a, b, c, d, e)
instance (Puttable a, Puttable b, Puttable c, Puttable d, Puttable e, Puttable f) => Puttable (a, b, c, d, e, f)
instance (Puttable a, Puttable b, Puttable c, Puttable d, Puttable e, Puttable f, Puttable g) => Puttable (a, b, c, d, e, f, g)

instance Puttable (f (g a)) => Puttable (F.Compose f g a)
instance (Puttable (f a), Puttable (g a)) => Puttable (F.Product f g a)
instance (Puttable (f a), Puttable (g a)) => Puttable (F.Sum f g a)
