-- {-# OPTIONS_GHC -Wno-unused-imports #-} -- TEMP

-- | Linear functions
--
-- 

module F where

import qualified Prelude as P
import Prelude hiding (id,(.))

import GHC.Generics ((:*:)(..))
import Data.Functor.Rep

import Misc
import Category

-- | Linear functions
newtype F (s :: *) a b = F (a s -> b s)

instance Category (F s) where
  type Obj (F s) = Representable 
  id = F id
  F g . F f = F (g . f)

instance Monoidal (F s) (:*:) where
  F f *** F g = F (\ (a :*: b) -> f a :*: g b)

instance Cartesian (F s) (:*:) where
  exl = F (\ (a :*: _) -> a)
  exr = F (\ (_ :*: b) -> b)
  dup = F (\ a -> a :*: a)

instance Additive s => Cocartesian (F s) (:*:) where
  inl = F (\ a -> a :*: zeros)
  inr = F (\ b -> zeros :*: b)
  jam = F (\ (a :*: b) -> a +^ b)

#if 0

instance Representable p => MonoidalRep (F s) p where
  -- exs = tabulate (\ i -> F (\ a -> a `index` i))
  --     = tabulate (\ i -> F (`index` i))
  --     = tabulate (\ i -> F (flip index i))
  --     = tabulate (F . flip index)

-- Error:
-- 
--   Expected kind ‘* -> * -> *’,
--     but ‘F s’ has kind ‘(* -> *) -> (* -> *) -> *’
--   In the first argument of ‘MonoidalRep’, namely ‘(F s)’
--   In the instance declaration for ‘MonoidalRep (F s) p’
-- 
-- See notes following MonoidalRep in Category.hs.

#endif
