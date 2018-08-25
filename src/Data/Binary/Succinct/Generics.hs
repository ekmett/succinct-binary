{-# language GADTs #-}
{-# language PolyKinds #-}
{-# language DataKinds #-}
{-# language ConstraintKinds #-}
{-# language KindSignatures #-}
{-# language TypeOperators #-}
{-# language FlexibleContexts #-}
{-# language FunctionalDependencies #-}
{-# language FlexibleInstances #-}
{-# language MultiParamTypeClasses #-}
{-# language TypeApplications #-}
{-# language ScopedTypeVariables #-}
{-# language AllowAmbiguousTypes #-}
{-# language UndecidableInstances #-}
{-# language PatternSynonyms #-}

module Data.Binary.Succinct.Generics
  ( 
  -- * API
    Shape(..), Shaped, shape
  , SBool(..)
  , SDecidedStrictness(..)
  -- * Annotations
  , Annotation(..)
  , ShowAnn(..)
  , Unannotated(..)
  , GenType(..)
  -- * Implementation
  , GShape(..)
  , ReifiedBool(..)
  , GShaped(..)
  , ReifiedDecidedStrictness(..)
  ) where

import GHC.Generics
import GHC.Types
import Data.Proxy

--------------------------------------------------------------------------------
-- * Reified Bools
--------------------------------------------------------------------------------

data SBool (t :: Bool) where
  STrue :: SBool 'True
  SFalse :: SBool 'False

instance Show (SBool t) where
  showsPrec _ STrue = showString "STrue"
  showsPrec _ SFalse = showString "SFalse"

class ReifiedBool (t :: Bool) where
  reflectBool :: SBool t

instance ReifiedBool 'True where
  reflectBool = STrue

instance ReifiedBool 'False where
  reflectBool = SFalse

--------------------------------------------------------------------------------
-- * Reified Strictness
--------------------------------------------------------------------------------

data SDecidedStrictness (t :: DecidedStrictness) where
  SDecidedLazy :: SDecidedStrictness 'DecidedLazy
  SDecidedStrict :: SDecidedStrictness 'DecidedStrict
  SDecidedUnpack :: SDecidedStrictness 'DecidedUnpack

instance Show (SDecidedStrictness t) where
  showsPrec _ SDecidedLazy = showString "SDecidedLazy"
  showsPrec _ SDecidedStrict = showString "SDecidedStrict"
  showsPrec _ SDecidedUnpack = showString "SDecidedUnpack"

class ReifiedDecidedStrictness (t :: DecidedStrictness) where
  reflectDecidedStrictness :: SDecidedStrictness t

instance ReifiedDecidedStrictness 'DecidedLazy where
  reflectDecidedStrictness = SDecidedLazy

instance ReifiedDecidedStrictness 'DecidedStrict where
  reflectDecidedStrictness = SDecidedStrict

instance ReifiedDecidedStrictness 'DecidedUnpack where
  reflectDecidedStrictness = SDecidedUnpack

--------------------------------------------------------------------------------
-- * Reified Strictness
--------------------------------------------------------------------------------

data GenType = Ty | Constructors | Fields | Field

data GShape ann (ty :: GenType) p t where
  Type :: ann 'Ty t -> SBool nt -> GShape ann 'Constructors p t -> GShape ann 'Ty p (M1 D ('MetaData dc mdl pkg nt) t)
  V :: GShape ann 'Constructors p V1
  S :: ann 'Constructors (l :+: r) -> GShape ann 'Constructors p l -> GShape ann 'Constructors p r -> GShape ann 'Constructors p (l :+: r)
  Con :: ann 'Constructors t -> GShape ann 'Fields p t -> GShape ann 'Constructors p (M1 C ci t)
  P :: ann 'Fields (l :*: r) -> GShape ann 'Fields p l -> GShape ann 'Fields p r -> GShape ann 'Fields p (l :*: r)
  Sel :: ann 'Fields t -> SDecidedStrictness ds -> GShape ann 'Field p t -> GShape ann 'Fields p (M1 S ('MetaSel fn su ss ds) t)
  U :: GShape ann 'Fields p U1
  K :: p c => Proxy c -> GShape ann 'Field p (K1 i c)

--------------------------------------------------------------------------------
-- * ShowAnn
--------------------------------------------------------------------------------

class ShowAnn (ann :: GenType -> (* -> *) -> *) where
  showsPrecAnn :: Int -> ann ty t -> ShowS

instance ShowAnn ann => Show (GShape ann ty p t) where
  showsPrec d (Type a nt cs) = showParen (d > 10) $
    showString "Type " . showsPrecAnn 11 a . showChar ' ' . showsPrec 11 nt . showChar ' ' . showsPrec 11 cs
  showsPrec d (S a l r) = showParen (d > 10) $
    showString "S " . showsPrecAnn 11 a . showChar ' ' . showsPrec 11 l . showChar ' ' . showsPrec 11 r
  showsPrec d (Con a b) = showParen (d > 10) $
    showString "Con " . showsPrecAnn 11 a . showChar ' ' . showsPrec 11 b
  showsPrec _ V = showChar 'V'
  showsPrec d (P a l r) = showParen (d > 10) $
    showString "P " . showsPrecAnn 11 a . showChar ' ' . showsPrec 11 l . showChar ' ' . showsPrec 11 r
  showsPrec d (Sel a s b) = showParen (d > 10) $ showString "Sel " . showsPrecAnn 11 a . showChar ' ' . showsPrec 11 s . showChar ' ' . showsPrec 11 b
  showsPrec _ U = showChar 'U'
  showsPrec d (K Proxy) = showParen (d > 10) $ showString "K Proxy"

--------------------------------------------------------------------------------
-- * Annotations
--------------------------------------------------------------------------------

class Annotation (ann :: GenType -> (* -> *) -> *) (p :: * -> Constraint) where
  typeAnn :: SBool nt -> GShape ann 'Constructors p t -> ann 'Ty t
  conAnn :: GShape ann 'Fields p t -> ann 'Constructors t
  selAnn :: SDecidedStrictness ds -> GShape ann 'Field p t -> ann 'Fields t
  sumAnn :: GShape ann 'Constructors p l
         -> GShape ann 'Constructors p r
         -> ann 'Constructors (l :+: r)
  prodAnn :: GShape ann 'Fields p l 
          -> GShape ann 'Fields p r
          -> ann 'Fields (l :*: r)

-- getConAnn :: GShape ann 'Constructors p t -> ann 'Constructors t
-- getConAnn (S a _ _) = a
-- getConAnn (Con a _ _) = a

--------------------------------------------------------------------------------
-- * Smart Constructors
--------------------------------------------------------------------------------

-- smart constructor for ignoring annotations
pattern Type_
  :: Annotation ann p
  => ()
  => SBool nt
  -> GShape ann 'Constructors p t
  -> GShape ann 'Ty p (M1 D ('MetaData dc mdl pkg nt) t)
pattern Type_ nt cs <- Type _a nt cs where
  Type_ nt cs = Type (typeAnn nt cs) nt cs

pattern Con_
  :: Annotation ann p
  => ()
  => GShape ann 'Fields p t 
  -> GShape ann 'Constructors p (M1 C ci t)
pattern Con_ fs <- Con _a fs where
  Con_ fs = Con (conAnn fs) fs

pattern Sel_
  :: Annotation ann p
  => ()
  => SDecidedStrictness ds
  -> GShape ann 'Field p t
  -> GShape ann 'Fields p (M1 S ('MetaSel fn su ss ds) t)
pattern Sel_ ds f <- Sel _a ds f where
  Sel_ ds f = Sel (selAnn ds f) ds f

pattern S_
  :: Annotation ann p
  => ()
  => GShape ann 'Constructors p l
  -> GShape ann 'Constructors p r
  -> GShape ann 'Constructors p (l :+: r)
pattern S_ l r <- S _a l r where
  S_ l r = S (sumAnn l r) l r

pattern P_
  :: Annotation ann p
  => ()
  => GShape ann 'Fields p l
  -> GShape ann 'Fields p r
  -> GShape ann 'Fields p (l :*: r)
pattern P_ l r <- P _a l r where
  P_ l r = P (prodAnn l r) l r

instance Eq (GShape ann ty p t) where 
  _ == _ = True

instance Ord (GShape ann ty p t) where
  compare _ _ = EQ

--------------------------------------------------------------------------------
-- * Shape Reflection
--------------------------------------------------------------------------------

shape :: forall p a ann. (Shaped p a, Annotation ann p) => Shape ann p a
shape = Shape $ gshape @('Ty) @p @(Rep a)

newtype Shape ann p a = Shape { runShape :: GShape ann 'Ty p (Rep a) }
  deriving Show

instance Eq (Shape ann p a) where
  _ == _ = True

instance Ord (Shape ann p a) where
  compare _ _ = EQ

class    (Generic a, GShaped 'Ty p (Rep a)) => Shaped p a 
instance (Generic a, GShaped 'Ty p (Rep a)) => Shaped p a 

--------------------------------------------------------------------------------
-- * Generic Shape Reflection
--------------------------------------------------------------------------------

class GShaped ty p t | t -> ty where
  gshape :: Annotation ann p => GShape ann ty p t

instance (ReifiedBool nt, GShaped 'Constructors p t) => GShaped 'Ty p (M1 D ('MetaData dc md pkg nt) t) where
  gshape = Type_ reflectBool (gshape @_ @p)

instance GShaped 'Constructors p V1 where
  gshape = V

instance (GShaped 'Constructors p l, GShaped 'Constructors p r) => GShaped 'Constructors p (l :+: r) where
  gshape = S_ (gshape @'Constructors @p @l) (gshape @'Constructors @p @r)

instance GShaped 'Fields p t => GShaped 'Constructors p (M1 C ci t) where
  gshape = Con_ (gshape @_ @p)

instance (GShaped 'Fields p l, GShaped 'Fields p r) => GShaped 'Fields p (l :*: r) where
  gshape = P_ (gshape @'Fields @p @l) (gshape @'Fields @p @r)

instance (ReifiedDecidedStrictness ds, GShaped 'Field p t) => GShaped 'Fields p (M1 S ('MetaSel fn su ss ds) t) where
  gshape = Sel_ reflectDecidedStrictness (gshape @_ @p) where

instance GShaped 'Fields p U1 where
  gshape = U

instance p c => GShaped 'Field p (K1 i c) where
  gshape = K Proxy

--------------------------------------------------------------------------------
-- * Unnannotated
--------------------------------------------------------------------------------

data Unannotated (ty :: GenType) (t :: * -> *) = Unannotated

instance ShowAnn Unannotated where
  showsPrecAnn _ Unannotated = showString "Unannotated"

instance Annotation Unannotated p where
  typeAnn _ _ = Unannotated
  conAnn _ = Unannotated
  selAnn _ _ = Unannotated
  sumAnn _ _ = Unannotated
  prodAnn _ _ = Unannotated
