{-# OPTIONS_GHC -Wall #-}

-- | Linear algebra after Fortran

module LinAlg.L2 where

import qualified Prelude as P
import Prelude hiding ((+),sum,(*))

import GHC.Generics (Par1(..), (:.:)(..))
import Data.Distributive
import Data.Functor.Rep

type V f = (Representable f, Foldable f)
type V2 f g = (V f, V g)
type V3 f g h = (V2 f g, V h)

class Additive a where
  infixl 6 +
  zero :: a
  (+) :: a -> a -> a

class Additive a => Semiring a where
  infixl 7 *
  one :: a
  (*) :: a -> a -> a

sum :: (Foldable f, Additive a) => f a -> a
sum = foldr (+) zero

instance Additive Double where { zero = 0; (+) = (P.+) }
instance Semiring Double where { one  = 1; (*) = (P.*) }

data L :: (* -> *) -> (* -> *) -> (* -> *) where
  Scale :: s -> L Par1 Par1 s
  JoinL :: V h => h (L f g s) -> L (h :.: f) g s
  ForkL :: V h => h (L f g s) -> L f (h :.: g) s

#if 0

instance Additive s => Additive (L Par1 Par1 s) where
  zero = Scale zero
  Scale s + Scale s' = Scale (s + s') -- distributivity

instance (V h, Additive s, Additive (L f g s)) => Additive (L (h :.: f) g s) where
  zero = Join (tabulate (const zero))
  Join ms + Join ms' = JoinL (liftR2 (+) ms ms')
  -- ForkL ms + Fork ms' = ForkL (liftR2 (+) ms ms')

instance (V h, Additive s, Additive (L f g s)) => Additive (L f (h :.: g) s) where
  zero = Fork (tabulate (const zero))
  Fork ms + Fork ms' = ForkL (liftR2 (+) ms ms')
  -- JoinL ms + Join ms' = JoinL (liftR2 (+) ms ms')

-- Why doesn't GHC object to the overlap between the previous two instances?
-- Why *does* GHC object to the commented-out third clauses in each?

#else

instance Additive s => Additive (L f g s) where
  zero = undefined -- ???
  Scale s + Scale s' = Scale (s + s') -- distributivity
  JoinL ms + Join ms' = JoinL (liftR2 (+) ms ms')
  ForkL ms + Fork ms' = ForkL (liftR2 (+) ms ms')

#endif

unforkL :: Distributive h => L f (h :.: g) s -> h (L f g s)
unforkL (ForkL ms) = ms
unforkL (JoinL ms) = fmap JoinL (distribute (fmap unforkL ms))

#if 0
-- Types for Join clause:

     JoinL                        ms   :: L (k :.: f) (h :.: g) s
                                  ms   :: k (L f (h :.: g) s)
                     fmap unforkL ms   :: k (h (L f g s))
            distrib (fmap unforkL ms)  :: h (k (L f g s))
fmap JoinL (distrib (fmap unforkL ms)) :: h (L (k :.: f) g s)
#endif

unjoinL :: Distributive h => L (h :.: f) g s -> h (L f g s)
unjoinL (JoinL ms) = ms
unjoinL (ForkL ms) = fmap ForkL (distribute (fmap unjoinL ms))

pattern Fork :: V h => h (L f g s) -> L f (h :.: g) s
pattern Fork ms <- (unforkL -> ms)
 where Fork = ForkL
{-# complete Fork #-}

pattern Join :: V h => h (L f g s) -> L (h :.: f) g s
pattern Join ms <- (unjoinL -> ms)
 where Join = JoinL
{-# complete Join #-}

infixr 9 .@
(.@) :: Semiring s => L g h s -> L f g s -> L f h s
Scale a .@ Scale b = Scale (a * b)           -- Scale denotation
ForkL ms' .@ m = ForkL (fmap (.@ m) ms')     -- categorical product law
m' .@ JoinL ms = JoinL (fmap (m' .@) ms)     -- categorical coproduct law
JoinL ms' .@ Fork ms = sum (liftR2 (.@) ms' ms)   -- biproduct law
-- _ .@ _ = undefined -- TEMP

#if 0
-- ForkL clause types:

ForkL              ms  :: L g (k :.: h) s
                   ms  :: k (L g h s)
                m      :: L f g s
       fmap (.@ m) ms  :: k (L f h s)
ForkL (fmap (.@ m) ms) :: L f (k :.: h) s

-- join . fork types:

JoinL ms' :: L (k :.: g) h s
ForkL ms  :: L f (k :.: g) s
ms' :: k (L g h s)
ms  :: k (L f g s)

liftR2 (.@) ms' ms :: k (L f h s)
sum (liftR2 (.@) ms' ms) :: L f h s

#endif

-- TODO: Maybe move s back to first position in L so that L s is a (functor)
-- category. On the other hand, with s last, L f g is a (representable) functor.
-- On second thought, is L f g isn't even a regular Haskell functor in a
-- semantically sensible way?
