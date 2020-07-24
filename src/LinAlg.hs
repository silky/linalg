-- | Linear algebra after Fortran

module LinAlg where

import qualified Prelude as P
import Prelude hiding ((+),sum,(*))

import GHC.Generics (Par1(..), (:.:)(..))
import Data.Distributive
import Data.Functor.Rep

type V f = (Representable f, Foldable f)

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
  Zero :: L f g s
  Scale :: s -> L Par1 Par1 s
  JoinL :: V h => h (L f g s) -> L (h :.: f) g s
  ForkL :: V h => h (L f g s) -> L f (h :.: g) s

instance Additive s => Additive (L f g s) where
  zero = Zero
  Zero + m = m
  m + Zero = m
  Scale s + Scale s' = Scale (s + s') -- distributivity
  JoinL ms + Join ms' = JoinL (liftR2 (+) ms ms')
  ForkL ms + Fork ms' = ForkL (liftR2 (+) ms ms')

unforkL :: Representable h => L f (h :.: g) s -> h (L f g s)
unforkL Zero       = pureRep Zero
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

unjoinL :: Representable h => L (h :.: f) g s -> h (L f g s)
unjoinL Zero       = pureRep Zero
unjoinL (JoinL ms) = ms
unjoinL (ForkL ms) = fmap ForkL (distribute (fmap unjoinL ms))

pattern Fork :: V h => h (L f g s) -> L f (h :.: g) s
pattern Fork ms <- (unforkL -> ms) where Fork = ForkL
{-# complete Fork #-}

pattern Join :: V h => h (L f g s) -> L (h :.: f) g s
pattern Join ms <- (unjoinL -> ms) where Join = JoinL
{-# complete Join #-}

infixr 9 .@
(.@) :: Semiring s => L g h s -> L f g s -> L f h s
Zero      .@ _        = Zero                       -- Zero denotation
_         .@ Zero     = Zero                       -- linearity
Scale a   .@ Scale b  = Scale (a * b)              -- Scale denotation
ForkL ms' .@ m        = ForkL (fmap (.@ m) ms')    -- categorical product law
m'        .@ JoinL ms = JoinL (fmap (m' .@) ms)    -- categorical coproduct law
JoinL ms' .@ Fork ms  = sum (liftR2 (.@) ms' ms)   -- biproduct law
