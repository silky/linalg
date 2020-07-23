{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE NoStarIsType #-}  -- Optional

{-# OPTIONS_GHC -Wall #-}
{-# OPTIONS_GHC -Wno-unused-imports #-} -- TEMP

-- | Linear algebra after Fortran

module LinAlg1 where

import Data.Kind
import Control.Category

import Data.Distributive
import Data.Functor.Rep

data L :: Type -> Type -> Type where
  Scale :: Num a => a -> L a a  -- TODO: Semiring instead of Num
  Fork :: Functor g => g (L u v) -> L u (g v)
  Join :: Functor f => f (L u v) -> L (f u) v

-- For linear functions
forkF :: Functor g => g (u -> v) -> (u -> g v)
forkF hs u = fmap ($ u) hs

-- -- Denotation
-- mu :: L u v -> (u -> v)
-- mu (Scale a) = (a *)
-- mu (Fork

forkL :: Functor g => g (L u v) -> L u (g v)
forkL = Fork

joinL :: Functor f => f (L u v) -> L (f u) v
joinL = Join

unforkL :: Distributive g => L u (g v) -> g (L u v)
unforkL (Scale _) = error "oops"  -- TODO: eliminate this partiality
unforkL (Fork ms) = ms
unforkL (Join ms) = fmap joinL (distribute (fmap unforkL ms))

-- Types:
-- 
--                                  ms   :: f (L u (g v))
--                     fmap unforkL ms   :: f (g (L u v))
--            distrib (fmap unforkL ms)  :: g (f (L u v))
-- fmap join (distrib (fmap unforkL ms)) :: g (L (f u) v)

unjoinL :: Distributive f => L (f u) v -> f (L u v)
unjoinL (Scale _) = error "oops"  -- TODO: eliminate this partiality
unjoinL (Join ms) = ms
unjoinL (Fork ms) = fmap forkL (distribute (fmap unjoinL ms))

