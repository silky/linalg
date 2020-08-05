{-# LANGUAGE UndecidableInstances #-}  -- See below
-- {-# OPTIONS_GHC -Wno-unused-imports #-} -- TEMP

-- | Linear functions, providing denotational specification for all linear map
-- representations.

module F where

import Prelude hiding (id,(.),(+),(*),sum)

import GHC.Generics (Par1(..),(:*:)(..),(:.:)(..))
import Data.Functor.Rep

import Misc
import Category

-- | Linear functions
newtype F (s :: *) a b = F { unF :: a s -> b s }

instance Category (F s) where
  type Obj (F s) = Representable 
  id = F id
  F g . F f = F (g . f)

instance Monoidal (F s) (:*:) where
  F f *** F g = F (\ (a :*: b) -> f a :*: g b)

instance Cartesian (F s) (:*:) where
  exl = F exlF
  exr = F exrF
  dup = F dupF

instance Comonoidal (F s) (:*:) where (+++) = (***)

instance Additive s => Cocartesian (F s) (:*:) where
  inl = F (:*: zeroV)
  inr = F (zeroV :*:)
  jam = F (uncurryF (+^))

instance Additive s => Biproduct (F s) (:*:)

instance Semiring s => MonoidalR (F s) where
  cross :: Representable r => r (F s a b) -> F s (r :.: a) (r :.: b)
  cross fs = F (Comp1 . liftR2 (@@) fs . unComp1)

-- The Semiring s constraint here comes from (@@) being in the same class as
-- scale.

#if 0
                    fs :: r (F s a b)
        liftR2 (@@) fs :: r (a s) -> r (b s)
Comp1 . liftR2 (@@) fs . unComp1 :: (r :.: a) s -> (r :.: b) s

cross = F . inNew (liftR2 (@@))
#endif

instance Semiring s => CartesianR (F s) where
  exs :: Representable r => r (F s (r :.: a) a)
  exs = tabulate (\ i -> F (\ (Comp1 as) -> as `index` i))
  dups :: Representable r => F s a (r :.: a)
  dups = F (\ a -> Comp1 (pureRep a))
         -- F (Comp1 . pureRep)

instance Semiring s => BiproductR (F s) where
  ins :: (C2 Representable r a, Eq (Rep r)) => r (F s a (r :.: a))
  ins = tabulate (F . oneHot)
        -- tabulate $ \ i -> F (oneHot i)
        -- tabulate $ \ i -> F (\ a -> oneHot i a)
  jams :: (C2 Representable r a, Foldable r) => F s (r :.: a) a
  jams = F (\ (Comp1 as) -> foldr (+^) zeroV as)

-- TODO: can we define ins without Eq (Rep r)?

-- Illegal nested constraint ‘Eq (Rep r)’
-- (Use UndecidableInstances to permit this)

oneHot :: (C2 Representable r a, Eq (Rep r), Additive s)
       => Rep r -> a s -> (r :.: a) s
oneHot i a = Comp1 (tabulate (\ j -> if i == j then a else zeroV))

instance Semiring s => Linear s F (:*:) where
  scale s = F (fmap (s *))   -- F (\ (Par1 s') -> Par1 (s * s'))
  (@@) = unF
