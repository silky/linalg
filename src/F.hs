-- {-# OPTIONS_GHC -Wno-unused-imports #-} -- TEMP

-- | Linear functions, providing denotational specification for L.

module F where

import Prelude hiding (id,(.))

import GHC.Generics ((:*:)(..))
import Data.Functor.Rep

import Misc
import Category

-- | Linear functions
newtype F (s :: *) a b = F (a s -> b s)

instance Category (F s) where
  type Obj (F s) = Representable 
  id = F id
  F g . F f = F (g . f)

instance Monoidal (F s) (:*:) where
  F f *** F g = F (\ (a :*: b) -> f a :*: g b)

instance Cartesian (F s) (:*:) where
  exl = F (\ (a :*: _) -> a)
  exr = F (\ (_ :*: b) -> b)
  dup = F (\ a -> a :*: a)

instance Comonoidal (F s) (:*:) where (+++) = (***)

instance Additive s => Cocartesian (F s) (:*:) where
  inl = F (\ a -> a :*: zeroV)
  inr = F (\ b -> zeroV :*: b)
  jam = F (\ (a :*: b) -> a +^ b)
