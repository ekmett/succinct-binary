-- {-# language StrictData #-}
{-# language RankNTypes #-}
{-# language TypeApplications #-}
{-# language AllowAmbiguousTypes #-}
{-# language KindSignatures #-}
{-# language DataKinds #-}
{-# language ScopedTypeVariables #-}
{-# language DefaultSignatures #-}
{-# language EmptyCase #-}
{-# language GADTs #-}
{-# language ConstraintKinds #-}
{-# language MultiParamTypeClasses #-}
{-# language FlexibleContexts #-}
{-# language DeriveFunctor #-}
{-# language PatternGuards #-}
-- {-# options_ghc -Wno-unticked-promoted-constructors #-} -- does this not actually work?

module Data.Binary.Succinct.Internal where

import Data.Binary.Succinct.Generics
import Data.Binary.Succinct.Orphans ()

import Control.Monad (ap)
import Data.Proxy
import Data.Profunctor
import Data.Bits
import Data.ByteString as Strict
import Data.ByteString.Builder as Builder
import Data.ByteString.Lazy as Lazy
import Data.Semigroup hiding (Any)
import qualified Data.Vector.Storable as Storable
import Data.Vector.Storable.ByteString
import Data.Void
import Data.Word
import HaskellWorks.Data.BalancedParens.RangeMinMax as BP
import HaskellWorks.Data.RankSelect.Base.Rank0
import HaskellWorks.Data.RankSelect.CsPoppy as CsPoppy
import GHC.Generics

--------------------------------------------------------------------------------
-- * Size Internals
--------------------------------------------------------------------------------

data Size = Any | Variable | Exactly !Int
  deriving (Eq,Ord,Show,Read)

-- @((\/), Any)@ is a bounded semilattice
(\/) :: Size -> Size -> Size
Any \/ x = x
x \/ Any = x
Exactly x \/ Exactly y | x == y = Exactly x -- needs type equality
_ \/ _ = Variable

-- @((/\), Exactly 0)@ is a commutative monoid
(/\) :: Size -> Size -> Size
Any /\ _ = Any
_ /\ Any = Any
Exactly x /\ Exactly y = Exactly (x + y) -- but these don't compute nicely
_ /\ _ = Variable

--------------------------------------------------------------------------------
-- * Put Internals
--------------------------------------------------------------------------------

data State = State Int Word8 Int Word8
data W = W Builder Builder Builder Word64

instance Semigroup W where
  W a b c n <> W d e f m = W (a <> d) (b <> e) (c <> f) (n + m)

instance Monoid W where
  mempty = W mempty mempty mempty 0
  mappend = (<>)

data Result = Result {-# UNPACK #-} !State {-# UNPACK #-} !W

newtype Put = Put { runPut :: State -> Result }

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
putN n x = metas n <> content x

instance Semigroup Put where
  f <> g = Put $ \s -> case runPut f s of
    Result s' m -> case runPut g s' of
      Result s'' n -> Result s'' (m <> n)

instance Monoid Put where
  mempty = Put $ \s -> Result s mempty

--------------------------------------------------------------------------------
-- * Get
--------------------------------------------------------------------------------

newtype Get a = Get { runGet :: Blob -> Word64 -> Word64 -> a }
  deriving Functor

instance Applicative Get where
  pure a = Get $ \_ _ _ -> a
  (<*>) = ap

instance Monad Get where
  m >>= k = Get $ \e i j -> runGet (k (runGet m e i j)) e i j

--------------------------------------------------------------------------------
-- * Size Annotations
--------------------------------------------------------------------------------

data SizeAnn (ty :: GenType) (g :: * -> *) where
  TypeAnn :: Size -> Maybe Word8 -> SizeAnn 'Ty g
  SumAnn :: Size -> Maybe Word8 -> Word8 -> Word8 -> SizeAnn 'Constructors g
  ConAnn :: Size -> SizeAnn 'Constructors g
  ProdAnn :: Size -> SizeAnn 'Fields g
  SelAnn :: Size -> SizeAnn 'Fields g

getConAnn :: GShape SizeAnn 'Constructors p t -> (Size, Maybe Word8, Word8)
getConAnn (S (SumAnn s dc _ k) _ _) = (s, dc, k)
getConAnn (Con (ConAnn s) _) = (s, Just 0, 1)
getConAnn _ = error "bad con ann"

getFieldAnn :: GShape SizeAnn 'Fields p t -> Size
getFieldAnn (P (ProdAnn s) _ _) = s
getFieldAnn (Sel (SelAnn s) _ _) = s
getFieldAnn _ = error "bad field ann"

instance Annotation SizeAnn Serializable where
  typeAnn _ V = TypeAnn Any Nothing
  typeAnn _ (Con (ConAnn s) _) = TypeAnn s (Just 0)
  typeAnn _ (S (SumAnn s mdc _ _) _ _) = case mdc of
    Nothing -> TypeAnn (Exactly 1 /\ s) mdc -- we have to store the tag
    Just _dc -> TypeAnn s mdc -- no tag
  typeAnn _ _ = error "bad type ann"

  sumAnn l r = SumAnn (sl \/ sr) (merge sl sr dl dr) nl (nl + nr) where
    (sl,dl,nl) = getConAnn l
    (sr,dr,nr) = getConAnn r
    merge Any _ _ (Just k) = Just (nl + k)
    merge _ Any (Just k) _ = Just k
    merge _ _ Nothing (Just k) = Just (nl + k)
    merge _ _ (Just k) Nothing = Just k
    merge _ _ _ _ = Nothing

  -- when we annotate products this becomes non-recursive
  conAnn U = ConAnn (Exactly 0)
  conAnn (Sel (SelAnn s) _ _) = ConAnn s
  conAnn (P (ProdAnn s) _ _) = ConAnn s
  conAnn _ = error "bad con ann"

  prodAnn l r = ProdAnn (getFieldAnn l /\ getFieldAnn r)
  selAnn _ (K (_ :: Proxy a)) = SelAnn (size @a)

--------------------------------------------------------------------------------
-- * Serial
--------------------------------------------------------------------------------

data Serial a b = Serial !Size (Maybe Word8) (a -> Put) (Get b)

instance Profunctor Serial where
  dimap l r (Serial s dc f g) = Serial s dc (f . l) (r <$> g)

--------------------------------------------------------------------------------
-- * Serializable
--------------------------------------------------------------------------------

class Serializable a where
  serial :: Serial a a
  default serial :: Shaped Serializable a => Serial a a
  serial = gserial

size :: forall a. Serializable a => Size
size = case serial @a of Serial s _ _ _ -> s

put :: Serializable a => a -> Put
put a = case serial of Serial _ _ p _ -> p a

get :: Serializable a => Get a
get = case serial of Serial _ _ _ g -> g

instance Serializable Void

instance Serializable ()

instance Serializable Word8 where
  serial = Serial (Exactly 1) (Just 0) put8 todo

instance Serializable Word16 where
  serial = Serial (Exactly 2) (Just 0) (putN 2 . word16LE) todo

instance Serializable Word32 where
  serial = Serial (Exactly 4) (Just 0) (putN 4 . word32LE) todo

instance Serializable Word64 where
  serial = Serial (Exactly 8) (Just 0) (putN 8 . word64LE) todo

instance (Serializable a, Serializable b) => Serializable (a, b)
instance (Serializable a, Serializable b) => Serializable (Either a b)
instance Serializable a => Serializable [a]
instance Serializable a => Serializable (Maybe a)

todo :: a
todo = error "haven't gotten to it yet"

gserial :: forall a. Shaped Serializable a => Serial a a
gserial = case shape @Serializable @a @SizeAnn of
  Shape (Type (TypeAnn s mdc) _nt cons0) -> Serial s mdc (\a -> gput cons0 (unM1 $ from a) 0) todo where

    gput :: GShape SizeAnn 'Constructors Serializable t -> t a -> Word8 -> Put
    gput V v _ = case v :: V1 a of {}
    gput (S (SumAnn _ _ _ _) l _) (L1 a) i = gput l a i
    gput (S (SumAnn _ _ k _) _ r) (R1 b) i = gput r b (i+k)
    gput (Con (ConAnn _) c) (M1 b) i = case mdc of
      Nothing -> put8 i <> gputCon c b False
      Just j
        | i == j    -> gputCon c b False
        | otherwise -> error "impossible constructor"
    gput _ _ _ = error "bad constructor ann in put"

    gputCon :: GShape SizeAnn 'Fields Serializable t -> t a -> Bool -> Put
    gputCon U U1 _ = mempty
    gputCon (P _ l r) (l1 :*: r1) v =
       gputCon l l1 (v || isVariable (getFieldAnn r)) <> gputCon r r1 v
    gputCon (Sel _ _ds fld) (M1 p) b = gputSel fld p b

    gputSel :: GShape SizeAnn 'Field Serializable t -> t a -> Bool -> Put
    gputSel (K (_ :: Proxy c)) (K1 x) b
      | b, Variable <- size @c = parens (put x)
      | otherwise = put x

isVariable :: Size -> Bool
isVariable Variable = True
isVariable _ = False

--------------------------------------------------------------------------------
-- * Blobs
--------------------------------------------------------------------------------

data Blob = Blob
  { blobSize    :: Word64
  , blobMeta    :: CsPoppy
  , blobShape   :: RangeMinMax (Storable.Vector Word64)
  , blobContent :: Strict.ByteString
  } -- deriving Show

blob :: Put -> Blob
blob ma = case runPut ma (State 0 0 0 0) of
  Result (State i b j b') (W m s c n) -> Blob
    { blobSize = n
    , blobMeta = makeCsPoppy $ ws $ flush8 i b m
    , blobShape = mkRangeMinMax $ ws $ flush8 j b' s
    , blobContent = bs c
    }
  where
    flush :: Int -> Word8 -> Builder -> Builder
    flush 0 _ xs = xs
    flush _ b xs = xs <> word8 b

    flush8 :: Int -> Word8 -> Builder -> Builder
    flush8 r k d = flush r k d <> stimes (7 :: Int) (word8 0)

    trim8 :: Strict.ByteString -> Strict.ByteString
    trim8 b = Strict.take (Strict.length b .&. complement 7) b

    bs :: Builder -> Strict.ByteString
    bs = Lazy.toStrict . Builder.toLazyByteString

    ws :: Builder -> Storable.Vector Word64
    ws = byteStringToVector . trim8 . bs

--------------------------------------------------------------------------------
-- * Debugging
--------------------------------------------------------------------------------

-- Print out a string of S's and D's, corresponding to Shape or Data, from the meta index
inspectMeta :: Blob -> String
inspectMeta (Blob n m _ _) = as 'D' 'S' m <$> [1..n]

-- Print out the balanced parentheses representation of our paren index
inspectShape :: Blob -> String
inspectShape (Blob n m s _) = as ')' '(' s <$> [1..rank1 m n]

-- Print out our raw content buffer
inspectContent :: Blob -> String
inspectContent (Blob _ _ _ c) = show c

-- Print out a representation of the entire blob, interleaving paren and content
inspectBlob :: Blob -> String
inspectBlob (Blob n m s c) = do
  i <- [1..n]
  case access m i of
    0 -> '{' : shows (Strict.index c $ fromIntegral $ rank0 m i - 1) "}"
    _ -> [as ')' '(' s $ rank1 m i]

instance Show Blob where
  show = inspectBlob

access :: Rank1 v => v -> Word64 -> Word64
access s 1 = rank1 s 1
access s n = rank1 s n - rank1 s (n - 1)

as :: Rank1 v => a -> a -> v -> Word64 -> a
as l r s i = case access s i of
  0 -> l
  _ -> r
