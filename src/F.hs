{-# LANGUAGE UndecidableInstances #-}  -- See below
-- {-# OPTIONS_GHC -Wno-unused-imports #-} -- TEMP

-- | Linear functions, providing denotational specification for all linear map
-- representations.

module F where

import Prelude hiding (id,(.),sum)

import GHC.Generics ((:*:)(..),(:.:)(..))
import Data.Functor.Rep

import Misc
import Category

-- | Linear functions
newtype F (s :: *) a b = F { unF :: a s -> b s }

instance Category (F s) where
  type Obj (F s) = Representable 
  id = F id
  F g . F f = F (g . f)

infixl 9 @@
(@@) :: F s a b -> (a s -> b s)
F f @@ a = f a

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

-- class (Category k, Representable r) => MonoidalR k r where
--   cross :: r (a `k` b) -> ((r :.: a) `k` (r :.: b))

instance Representable r => MonoidalR (F s) r where
  cross :: r (F s a b) -> (F s (r :.: a) (r :.: b))
  cross fs = F (Comp1 . liftR2 (@@) fs . unComp1)

#if 0
                    fs :: r (F s a b)
        liftR2 (@@) fs :: r (a s) -> r (b s)
Comp1 . liftR2 (@@) fs . unComp1 :: (r :.: a) s -> (r :.: b) s
#endif

instance Representable r => CartesianR (F s) r where
  exs :: r (F s (r :.: a) a)
  exs = tabulate (\ i -> F (\ (Comp1 as) -> as `index` i))
  dups :: F s a (r :.: a)
  dups = F (\ a -> Comp1 (pureRep a))
         -- F (Comp1 . pureRep)

instance (Representable r, Foldable r, Eq (Rep r), Additive s)
      => BiproductR (F s) r where
  ins :: Representable a => r (F s a (r :.: a))
  ins = tabulate (F . oneHot)
        -- tabulate $ \ i -> F (oneHot i)
        -- tabulate $ \ i -> F (\ a -> oneHot i a)
  jams :: Representable a => F s (r :.: a) a
  jams = F (\ (Comp1 as) -> foldr (+^) zeroV as)

-- TODO: can we define ins without Eq (Rep r)?

-- Illegal nested constraint ‘Eq (Rep r)’
-- (Use UndecidableInstances to permit this)

oneHot :: (C2 Representable r a, Eq (Rep r), Additive s) => Rep r -> a s -> (r :.: a) s
oneHot i a = Comp1 (tabulate (\ j -> if i == j then a else zeroV))

-- Circular with ins
unjoin' :: (C2 Representable r a, Foldable r, Eq (Rep r), Additive s)
        => F s (r :.: a) c -> r (F s a c)
unjoin' f = (f .) <$> ins
