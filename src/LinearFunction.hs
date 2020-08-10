{-# LANGUAGE UndecidableInstances #-}  -- See below
-- {-# OPTIONS_GHC -Wno-unused-imports #-} -- TEMP

-- | Linear functions, providing denotational specification for all linear map
-- representations.

module LinearFunction where

import Prelude hiding (id,(.),(+),(*),sum)

import GHC.Generics (Par1(..),(:*:)(..),(:.:)(..))
import Data.Functor.Rep

import Misc
import Category
import Category.Isomorphism

-- | Linear functions
newtype L (s :: *) a b = L { unF :: a s -> b s }

instance Category (L s) where
  type Obj' (L s) = Representable 
  id = L id
  L g . L f = L (g . f)

instance Monoidal (L s) (:*:) where
  L f *** L g = L (\ (a :*: b) -> f a :*: g b)

instance Cartesian (L s) (:*:) where
  exl = L exlF
  exr = L exrF
  dup = L dupF

instance Comonoidal (L s) (:*:) where (+++) = (***)

instance Additive s => Cocartesian (L s) (:*:) where
  inl = L (:*: zeroV)
  inr = L (zeroV :*:)
  jam = L (uncurryF (+^))

instance Additive s => Biproduct (L s) (:*:)

instance Representable r => MonoidalR (L s) r (:.:) where
  cross :: Obj2 (L s) a b => r (L s a b) -> L s (r :.: a) (r :.: b)
  cross fs = L (Comp1 . liftR2 unF fs . unComp1)

#if 0
                   fs :: r (L s a b)
        liftR2 unF fs :: r (a s) -> r (b s)
Comp1 . liftR2 unF fs . unComp1 :: (r :.: a) s -> (r :.: b) s

cross = L . inNew (liftR2 unF)
#endif

instance Representable r => CartesianR (L s) r (:.:) where
  exs :: Obj (L s) a => r (L s (r :.: a) a)
  exs = tabulate (\ i -> L (\ (Comp1 as) -> as `index` i))
  dups :: Obj (L s) a => L s a (r :.: a)
  dups = L (Comp1 . pureRep)

instance Representable r => ComonoidalR (L s) r (:.:) where
  plus = cross

instance (Additive s, Representable r, Eq (Rep r), Foldable r)
      => CocartesianR (L s) r (:.:) where
  ins :: Obj (L s) a => r (L s a (r :.: a))
  ins = tabulate (L . oneHot)
        -- tabulate $ \ i -> L (oneHot i)
        -- tabulate $ \ i -> L (\ a -> oneHot i a)
  jams :: Obj (L s) a => L s (r :.: a) a
  jams = L (\ (Comp1 as) -> foldr (+^) zeroV as)

-- TODO: can we define ins without Eq (Rep r)?

-- Illegal nested constraint ‘Eq (Rep r)’
-- (Use UndecidableInstances to permit this)

oneHot :: (Obj (L s) a, Representable r, Eq (Rep r), Additive s)
       => Rep r -> a s -> (r :.: a) s
oneHot i a = Comp1 (tabulate (\ j -> if i == j then a else zeroV))

class Scalable l where
  scale :: Semiring s => s -> l s Par1 Par1

instance Scalable L where
  scale s = L (fmap (s *))   -- L (\ (Par1 s') -> Par1 (s * s'))

class LinearMap l where
  -- | Semantic function for all linear map representations. Correctness of
  -- every operation on every representation is specified by requiring mu to be
  -- homomorphic for (distributes over) that operation. For instance, mu must be
  -- a functor (Category homomorphism).
  mu :: (Obj2 (L s) a b, Obj2 (l s) a b) => l s a b <-> L s a b

-- TODO: maybe generalize so that LHS and RHS objects needn't match. In other
-- words, the mu functor can have non-identity object maps.

-- Note that scale, join2, fork2, join, and fork (the basic building blocks of
-- linear maps) are all linear isomorphisms. With a little help, we can combine
-- them into a single isomorphism. That help can be something that combines five
-- arrows having signatures matching those building blocks into a single arrow.

-- Trivial instance
instance LinearMap L where mu = id
