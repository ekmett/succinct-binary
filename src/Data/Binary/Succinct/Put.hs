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

import Control.Monad (ap, replicateM_)
import Data.Bits
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

meta :: Bool -> PutM ()
meta v = PutM $ \(S i b j c) -> 
  if i == 7
  then Result () (S 0 0 j c) (W (Builder.word8 (pushBit b i v)) mempty mempty 1)
  else Result () (S (i+1) (pushBit b i v) j c) mempty

shape :: Bool -> PutM ()
shape v = PutM $ \(S j c i b) -> 
  if i == 7
  then Result () (S j c 0 0 ) (W mempty (Builder.word8 (pushBit b i v)) mempty 0)
  else Result () (S j c (i+1) (pushBit b i v)) mempty

pushBit :: Word8 -> Int -> Bool -> Word8
pushBit w i False = clearBit w i
pushBit w i True  = setBit   w i

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

putParen :: Bool -> Put
putParen p = do
  meta True
  shape p

putParens :: Put -> Put
putParens p = putParen True *> p <* putParen False

putBS :: ByteString -> Put
putBS bs = putN (Strict.length bs) (S.putByteString bs)

put8 :: Word8 -> Put
put8 w = meta False *> content (S.putWord8 w)

putN :: Int -> S.Put -> Put
putN i w = replicateM_ i (meta False) *> content w -- TODO: more efficient bulk meta

putN_ :: S.Put -> Put
putN_ w = replicateM_ n (meta False) *> content (S.putByteString bs) where
  bs = S.runPut w
  n = Strict.length bs

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
    1 -> case sop of
      SOP.Z xs -> products xs -- skip the data constructor when we have only one constructor
                              -- TODO: skip when we only have one _possible_ constructor (skip size=Any constructors)
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
    
    products1 :: (Puttable x, SOP.All Puttable xs) => x -> SOP.NP SOP.I xs -> Put
    products1 x SOP.Nil = put x -- the last field is written without parens: TODO: the last variable width field
    products1 x (SOP.I y SOP.:* ys) = putWithParens x *> products1 y ys

putWithParens :: forall a. Puttable a => a -> Put
putWithParens = case size @a of
  Variable -> putParens . put
  _ -> put

-- (String,Int64,String)
-- ((a)bc)

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

instance Puttable Char where
  put = putBS . UTF8.fromString . pure

instance Puttable Int32 where
  put = putN 4 . S.putInt32le

instance Puttable Int16 where
  put = putN 2 . S.putInt16le

instance Puttable Int8 where
  put = putN 1 . S.putInt8

-- instance Puttable Void -- TODO: fix GSumFrom in Generics.SOP to allow V1
instance Puttable ()
instance Puttable Void
instance Puttable (Proxy a)
instance Puttable a => Puttable (Maybe a)
instance Puttable a => Puttable [a]
instance (Puttable a, Puttable b) => Puttable (a, b)
instance (Puttable a, Puttable b) => Puttable (Either a b)
instance Puttable (f (g a)) => Puttable (Compose f g a)
instance (Puttable (f a), Puttable (g a)) => Puttable (F.Product f g a)
instance (Puttable (f a), Puttable (g a)) => Puttable (F.Sum f g a)
