{-# Language AllowAmbiguousTypes #-}
{-# Language TypeApplications #-}
{-# Language ScopedTypeVariables #-}
{-# Language DefaultSignatures #-}
{-# Language FlexibleContexts #-}
{-# Language MonoLocalBinds #-}
{-# Language GADTs #-}

module Data.Binary.Succinct.Size
  ( Sized(..)
  , gsize
  , Size(..)
  , (/\)
  , (\/)
  ) where

import Data.Functor.Compose as F
import Data.Functor.Product as F
import Data.Functor.Sum as F
import Data.Int
import Data.Void
import Data.Word
import Generics.SOP
import Generics.SOP.GGP
import GHC.Generics as GHC

data Size = Any | Variable | Exactly !Int
  deriving (Eq,Ord,Show,Read)

class Sized a where
  size :: Size
  default size :: (GHC.Generic a, GFrom a, All2 Sized (GCode a)) => Size
  size = gsize @(GCode a)

-- @((\/), Any)@ is a semilattice
(\/) :: Size -> Size -> Size
Any \/ x = x
x \/ Any = x
Exactly x \/ Exactly y | x == y = Exactly x
_ \/ _ = Variable

-- @((/\), Exactly 0)@ is a commutative monoid
(/\) :: Size -> Size -> Size
Any /\ _ = Any
_ /\ Any = Any
Exactly x /\ Exactly y = Exactly (x + y)
_ /\ _ = Variable

gsize :: forall xss. All2 Sized xss => Size
gsize = sums $ hcollapse np where
  ksize :: forall x. Sized x => K Size x
  ksize = K (size @x)

  np :: NP (K Size) xss
  np = hcmap (Proxy @(All Sized)) (\xs -> K (products $ hcollapse xs)) npnp

  npnp :: NP (NP (K Size)) xss
  npnp = unPOP $ hcpure (Proxy @Sized) ksize

  sums :: [Size] -> Size
  sums [x] = x
  sums xs = Exactly 1 /\ foldr (\/) Any xs

  products :: [Size] -> Size
  products = foldr (/\) (Exactly 0)

instance Sized [a] where size = Variable
instance Sized Word8  where size = Exactly 1
instance Sized Word16 where size = Exactly 2
instance Sized Word32 where size = Exactly 4
instance Sized Word64 where size = Exactly 8
instance Sized Int8  where size = Exactly 1
instance Sized Int16 where size = Exactly 2
instance Sized Int32 where size = Exactly 4
instance Sized Int64 where size = Exactly 8
instance Sized Char where size = Exactly 4
instance Sized a => Sized (Maybe a)
instance (Sized a, Sized b) => Sized (a, b)
instance (Sized a, Sized b) => Sized (Either a b)
instance Sized (Proxy a)
instance Sized ()
instance Sized Void

instance Sized (f (g a)) => Sized (F.Compose f g a)
instance (Sized (f a), Sized (g a)) => Sized (F.Product f g a)
instance (Sized (f a), Sized (g a)) => Sized (F.Sum f g a)
