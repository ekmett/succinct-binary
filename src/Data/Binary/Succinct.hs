module Data.Binary.Succinct where

import Data.Binary.Succinct.Put
import Data.Binary.Succinct.Get

class Bitwise a where
  put :: a -> Put
  get :: Get a

instance (Bitwise a, Bitwise b) => Bitwise (a, b) where
  put = putPair put put
  get = getPair get get
