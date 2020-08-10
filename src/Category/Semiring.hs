-- | Semiring as category

module Category.Semiring where

import Prelude hiding ((+),(*))
import Misc
import Category

newtype SemiringCat s a b = S s

instance Semiring s => Category (SemiringCat s) where
  id = S one
  S t . S s = S (t * s)

deriving instance Additive s => Additive (SemiringCat s a b)

-- Do we want a Semiring instance?
--
-- deriving instance Semiring s => Semiring (SemiringCat s a b)
