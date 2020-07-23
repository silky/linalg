{-# OPTIONS_GHC -Wall #-}

-- | Linear algebra after Fortran

module LinAlg.L2 where

import GHC.Generics (Par1(..), (:.:)(..))
import Data.Distributive
-- import Data.Functor.Rep

data L :: (* -> *) -> (* -> *) -> (* -> *) where
  ScaleL :: s -> L Par1 Par1 s  -- TODO: Semiring instead of Num
  ForkL :: Functor h => h (L f g s) -> L f (h :.: g) s
  JoinL :: Functor h => h (L f g s) -> L (h :.: f) g s

unforkL :: Distributive h => L f (h :.: g) s -> h (L f g s)
unforkL (ForkL ms) = ms
unforkL (JoinL ms) = fmap JoinL (distribute (fmap unforkL ms))

-- Types for Join clause:
-- 
-- Join ms :: L (k :.: f) (h :.: g) s
-- 
--                                  ms :: k (L f (h :.: g) s)
--                     fmap unforkL ms   :: k (h (L f g s))
--            distrib (fmap unforkL ms)  :: h (k (L f g s))
-- fmap join (distrib (fmap unforkL ms)) :: h (L (k :.: f) g s)

unjoinL :: Distributive h => L (h :.: f) g s -> h (L f g s)
unjoinL (JoinL ms) = ms
unjoinL (ForkL ms) = fmap ForkL (distribute (fmap unjoinL ms))

pattern Fork :: Distributive h => h (L f g s) -> L f (h :.: g) s
pattern Fork ms <- (unforkL -> ms)
 where Fork = ForkL
{-# complete Fork #-}

pattern Join :: Distributive h => h (L f g s) -> L (h :.: f) g s
pattern Join ms <- (unjoinL -> ms)
 where Join = JoinL
{-# complete Join #-}
