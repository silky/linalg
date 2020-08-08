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

instance Representable r => MonoidalR (L s) r where
  cross :: r (L s a b) -> L s (r :.: a) (r :.: b)
  cross fs = L (Comp1 . liftR2 unF fs . unComp1)

#if 0
                   fs :: r (L s a b)
        liftR2 unF fs :: r (a s) -> r (b s)
Comp1 . liftR2 unF fs . unComp1 :: (r :.: a) s -> (r :.: b) s

cross = L . inNew (liftR2 unF)
#endif

instance Representable r => CartesianR (L s) r where
  exs :: r (L s (r :.: a) a)
  exs = tabulate (\ i -> L (\ (Comp1 as) -> as `index` i))
  dups :: L s a (r :.: a)
  dups = L (\ a -> Comp1 (pureRep a))
         -- L (Comp1 . pureRep)

instance (Additive s, Representable r, Eq (Rep r), Foldable r)
      => BiproductR (L s) r where
  ins :: Representable a => r (L s a (r :.: a))
  ins = tabulate (L . oneHot)
        -- tabulate $ \ i -> L (oneHot i)
        -- tabulate $ \ i -> L (\ a -> oneHot i a)
  jams :: Representable a => L s (r :.: a) a
  jams = L (\ (Comp1 as) -> foldr (+^) zeroV as)

-- TODO: can we define ins without Eq (Rep r)?

-- Illegal nested constraint ‘Eq (Rep r)’
-- (Use UndecidableInstances to permit this)

oneHot :: (C2 Representable a r, Eq (Rep r), Additive s)
       => Rep r -> a s -> (r :.: a) s
oneHot i a = Comp1 (tabulate (\ j -> if i == j then a else zeroV))

class Scalable l where
  scale :: Semiring s => s -> l s Par1 Par1

instance Scalable L where
  scale s = L (fmap (s *))   -- L (\ (Par1 s') -> Par1 (s * s'))

class LinearMap l where
  -- | Semantic function for all linear map representations. Correctness of
  -- every operation on every representation is specified by requiring that mu
  -- is homomorphic for (distributes over) that operation. For instance, mu must
  -- be a functor (Category homomorphism).
  mu  :: l s a b -> L s a b
  -- | Inverse of mu
  mu' :: L s a b -> l s a b

-- Trivial instance
instance LinearMap L where
  mu  = id
  mu' = id
