{-# Language AllowAmbiguousTypes #-}
{-# Language TypeApplications #-}
{-# Language ScopedTypeVariables #-}
{-# Language DefaultSignatures #-}
{-# Language FlexibleContexts #-}
{-# Language StandaloneDeriving #-}
{-# Language MonoLocalBinds #-}
{-# Language GADTs #-}
{-# Language DataKinds #-}
{-# Language TypeOperators #-}
{-# Language PolyKinds #-}
{-# Language TypeFamilies #-}
{-# Language UndecidableInstances #-}

module Data.Binary.Succinct.Size
  ( Sized(..)
  , Size(..)
  , gsize
  , Sing(SAny, SVariable, SExactly)
  , (/\), type (/\)
  , (\/), type (\/)
  , Pad(..)
  ) where

import Data.Functor.Compose as F
import Data.Functor.Product as F
import Data.Functor.Sum as F
import Data.Int
import Data.Proxy
import Data.Singletons
import Data.Singletons.TypeLits
import Data.Singletons.Prelude.Bool
import Data.Singletons.Prelude.Eq
import Data.Singletons.Prelude.Num
import qualified Data.Type.Equality as DTE
import Data.Void
import Data.Word
import Generics.SOP hiding (sing, Sing, SingI)
import Generics.SOP.GGP
import qualified GHC.Generics as GHC
import GHC.TypeNats (Nat)

data Size = Any | Variable | Exactly Nat -- kind

data instance Sing (s :: Size) where
  SAny :: Sing 'Any
  SVariable :: Sing 'Variable
  SExactly :: Sing n -> Sing ('Exactly n)
deriving instance Show (Sing (s :: Size))

instance SingI 'Any where sing = SAny
instance SingI 'Variable where sing = SVariable
instance KnownNat n => SingI ('Exactly n) where sing = SExactly SNat

class Sized (a :: *) where
  type SizeOf a :: Size
  type SizeOf a = GSizeOf (GCode a)
  size :: Sing (SizeOf a)
  default size :: (GHC.Generic a, GFrom a, All2 Sized (GCode a), SizeOf a ~ GSizeOf (GCode a)) => Sing (SizeOf a)
  size = gsize @(GCode a)

-- @((\/), Any)@ is a monoid
type family (\/) (a :: Size) (b :: Size) :: Size where
  'Any \/ x = x
  x \/ 'Any = x
  'Variable \/ _ = 'Variable
  _ \/ 'Variable = 'Variable
  'Exactly i \/ 'Exactly j = If (i DTE.== j) ('Exactly i) 'Variable

(\/) :: Sing a -> Sing b -> Sing (a \/ b)
SAny \/ x = x
x \/ SAny = x
SVariable \/ _ = SVariable
_ \/ SVariable = SVariable
SExactly p \/ SExactly q = sIf (p %== q) (SExactly p) SVariable
infixr 2 \/


-- @((/\), Exactly 0)@ is a monoid
type family (/\) (a :: Size) (b :: Size) :: Size where
  'Any /\ _ = 'Any
  _ /\ 'Any = 'Any
  'Variable /\ _ = 'Variable
  _ /\ 'Variable = 'Variable
  'Exactly i /\ 'Exactly j = 'Exactly (i + j)

(/\) :: Sing a -> Sing b -> Sing (a /\ b)
SAny /\ _ = SAny
_ /\ SAny = SAny
SVariable /\ SVariable = SVariable
SVariable /\ SExactly _ = SVariable
SExactly _ /\ SVariable = SVariable
SExactly p /\ SExactly q = SExactly (p %+ q)
infixr 3 /\

-- If the sum is not unary, add a byte for the tag
type family GSizeOf (xss :: [[*]]) :: Size where
  GSizeOf '[xs] = GSizeOfProduct xs
  GSizeOf '[] = 'Any
  GSizeOf (xs ': xs' ': xss) = 'Exactly 1 /\ GSizeOfSum (xs ': xs' ': xss)

type family GSizeOfSum (a :: [[*]]) :: Size where
  GSizeOfSum '[] = 'Any
  GSizeOfSum (xs ': xss) = GSizeOfProduct xs \/ GSizeOfSum xss

type family GSizeOfProduct (a :: [*]) :: Size where
  GSizeOfProduct '[] = 'Exactly 0
  GSizeOfProduct (x ': xs) = SizeOf x /\ GSizeOfProduct xs

newtype Sz a = Sz (Sing (SizeOf a))

gsize :: forall xss. All2 Sized xss => Sing (GSizeOf xss)
gsize = gsizeOf @xss $ unPOP $ hcpure (Proxy @Sized) ksize where
  ksize :: forall x. Sized x => Sz x
  ksize = Sz (size @x)

  gsizeOf :: NP (NP Sz) yss -> Sing (GSizeOf yss)
  gsizeOf (np :* Nil) = gsizeOfProduct np
  gsizeOf Nil = SAny
  gsizeOf (np :* np' :* nps) = SExactly (SNat @1) /\ gsizeOfSum (np :* np' :* nps)

  gsizeOfSum :: NP (NP Sz) yss -> Sing (GSizeOfSum yss)
  gsizeOfSum Nil = SAny
  gsizeOfSum (np :* nps) = gsizeOfProduct np \/ gsizeOfSum nps

  gsizeOfProduct :: NP Sz ys -> Sing (GSizeOfProduct ys)
  gsizeOfProduct Nil = SExactly (SNat @0)
  gsizeOfProduct (Sz sz :* szs) = sz /\ gsizeOfProduct szs

data Pad (n :: Nat) = Pad

instance KnownNat n => Sized (Pad n) where type SizeOf (Pad n) = 'Exactly n; size = sing

instance Sized Word8  where type SizeOf Word8  = 'Exactly 1; size = sing
instance Sized Word16 where type SizeOf Word16 = 'Exactly 2; size = sing
instance Sized Word32 where type SizeOf Word32 = 'Exactly 4; size = sing
instance Sized Word64 where type SizeOf Word64 = 'Exactly 8; size = sing
instance Sized Int8   where type SizeOf Int8   = 'Exactly 1; size = sing
instance Sized Int16  where type SizeOf Int16  = 'Exactly 2; size = sing
instance Sized Int32  where type SizeOf Int32  = 'Exactly 4; size = sing
instance Sized Int64  where type SizeOf Int64  = 'Exactly 8; size = sing

instance Sized [a] where type SizeOf [a] = 'Variable; size = sing
instance Sized Char where type SizeOf Char = 'Variable; size = sing

instance Sized Bool
instance (Sized a, Sized b) => Sized (Either a b)
instance Sized a => Sized (Maybe a)
instance Sized Ordering
instance Sized (Proxy a)
instance Sized Void
instance Sized ()
instance (Sized a, Sized b) => Sized (a, b)
instance (Sized a, Sized b, Sized c) => Sized (a, b, c)
instance (Sized a, Sized b, Sized c, Sized d) => Sized (a, b, c, d)
instance (Sized a, Sized b, Sized c, Sized d, Sized e) => Sized (a, b, c, d, e)
instance (Sized a, Sized b, Sized c, Sized d, Sized e, Sized f) => Sized (a, b, c, d, e, f)
instance (Sized a, Sized b, Sized c, Sized d, Sized e, Sized f, Sized g) => Sized (a, b, c, d, e, f, g)

instance Sized (f (g a)) => Sized (F.Compose f g a)
instance (Sized (f a), Sized (g a)) => Sized (F.Product f g a)
instance (Sized (f a), Sized (g a)) => Sized (F.Sum f g a)
