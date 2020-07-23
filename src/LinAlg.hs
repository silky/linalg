{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE NoStarIsType #-}  -- Optional

{-# OPTIONS_GHC -Wall #-}
{-# OPTIONS_GHC -Wno-unused-imports #-} -- TEMP

-- | Linear algebra after Fortran

module LinAlg where

import Data.Kind
import Control.Category


import Data.Distributive
import Data.Functor.Rep

data L :: Type -> Type -> Type where
  Scale :: Num a => a -> L a a  -- TODO: Semiring instead of Num
  Fork :: Functor g => g (L u v) -> L u (g v)
  Join :: Functor f => f (L u v) -> L (f u) v

fork :: Functor g => g (L u v) -> L u (g v)
fork = Fork

join :: Functor f => f (L u v) -> L (f u) v
join = Join

unfork :: Distributive g => L u (g v) -> g (L u v)
unfork (Scale _) = error "oops"  -- TODO: eliminate this partiality
unfork (Fork ms) = ms
unfork (Join ms) = fmap join (distribute (fmap unfork ms))

-- Types:
-- 
--                                 ms   :: f (L u (g v))
--                     fmap unfork ms   :: f (g (L u v))
--            distrib (fmap unfork ms)  :: g (f (L u v))
-- fmap join (distrib (fmap unfork ms)) :: g (L (f u) v)

unjoin :: Distributive f => L (f u) v -> f (L u v)
unjoin (Scale _) = error "oops"  -- TODO: eliminate this partiality
unjoin (Join ms) = ms
unjoin (Fork ms) = fmap fork (distribute (fmap unjoin ms))

