{-# language StandaloneDeriving #-}
{-# options_ghc -Wno-orphans #-}
module Data.Binary.Succinct.Orphans where

import HaskellWorks.Data.BalancedParens.RangeMinMax

deriving instance Show a => Show (RangeMinMax a)
