-- | Custom Category-Prelude

module CatPrelude (
    module Prelude
  , module Misc
  , module Category
  , module Data.Distributive
  , module Data.Functor.Rep
  , module GHC.Generics
  , module GHC.Types
  ) where

import Prelude hiding (id, sum, unzip, (*), (+), (.))

import Misc
import Category

import Data.Distributive
import Data.Functor.Rep
import GHC.Generics ((:*:)(..), (:+:)(..), (:.:)(..), Generic, Generic1, Par1(..), U1(..))
import GHC.Types (Constraint)
