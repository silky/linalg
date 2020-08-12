{-# OPTIONS_GHC -Wall -fno-warn-orphans #-}

-- | Orphan instances

module Orphans where

import Prelude

import GHC.Generics (Par1(..),(:+:)(..),(:*:)(..),(:.:)(..))
import Data.Monoid (Ap(..))
import Data.Distributive (Distributive(..))
import Data.Functor.Rep (Representable(..))
import Control.Newtype.Generics

import Misc

-------------------------------------------------------------------------------
-- | Newtype
-------------------------------------------------------------------------------

instance Newtype (Par1 t) where
  type O (Par1 t) = t
  pack = Par1
  unpack = unPar1

instance Newtype ((a :*: b) t) where
  type O ((a :*: b) t) = a t :* b t
  pack (a,b) = a :*: b
  unpack (a :*: b) = (a,b)

instance Newtype ((a :+: b) t) where
  type O ((a :+: b) t) = a t :+ b t
  pack = either L1 R1
  unpack = eitherF Left Right

instance Newtype ((a :.: b) t) where
  type O ((a :.: b) t) = a (b t)
  pack = Comp1
  unpack = unComp1

-------------------------------------------------------------------------------
-- | Ap
-------------------------------------------------------------------------------

instance Distributive f => Distributive (Ap f) where
  distribute = Ap . distribute . fmap getAp

instance Representable f => Representable (Ap f) where
  type Rep (Ap f) = Rep f
  tabulate = Ap . tabulate
  index = index . getAp
