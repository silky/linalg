-- {-# OPTIONS_GHC -Wno-unused-imports #-} -- TEMP

-- | Miscellany

module Misc where

import qualified Prelude as P
import Prelude hiding ((+),sum,(*),unzip)
import GHC.Types (Constraint)
import GHC.Generics ((:*:)(..))

import Data.Functor.Rep

-- More convenient type notation

infixl 7 :*
type (:*)  = (,)

infixl 6 :+
type (:+)  = Either


-- Constraint helpers

#if 1
-- Experiment. Smaller Core?
type C1 (con :: u -> Constraint) a = con a
type C2 (con :: u -> Constraint) a b = (con a, con b)
type C3 (con :: u -> Constraint) a b c = (con a, con b, con c)
type C4 (con :: u -> Constraint) a b c d = (con a, con b, con c, con d)
type C5 (con :: u -> Constraint) a b c d e = (con a, con b, con c, con d, con e)
type C6 (con :: u -> Constraint) a b c d e f = (con a, con b, con c, con d, con e, con f)
#else
type C1 (con :: u -> Constraint) a = con a
type C2 con a b         = (C1 con a, con b)
type C3 con a b c       = (C2 con a b, con c)
type C4 con a b c d     = (C2 con a b, C2 con c d)
type C5 con a b c d e   = (C3 con a b c, C2 con d e)
type C6 con a b c d e f = (C3 con a b c, C3 con d e f)
#endif


-- Semirings

class Additive a where
  infixl 6 +
  zero :: a
  (+) :: a -> a -> a

class Additive a => Semiring a where
  infixl 7 *
  one :: a
  (*) :: a -> a -> a

instance Additive Double where { zero = 0 ; (+) = (P.+) }
instance Semiring Double where { one  = 1 ; (*) = (P.*) }

instance Additive Bool where { zero = False ; (+) = (||) }
instance Semiring Bool where { one  = True  ; (*) = (&&) }

sum :: (Foldable f, Additive a) => f a -> a
sum = foldr (+) zero

-- To do: maybe replace `foldr` by `foldl` or `foldl'`. Does a strict left fold
-- help at all, considering that our "vectors" aren't flat?

-- Zero vector
zeroV :: (Representable a, Additive s) => a s
zeroV = pureRep zero

-- | Vector addition
infixl 6 +^
(+^) :: (Representable f, Additive s) => f s -> f s -> f s
(+^) = liftR2 (+)

-- GHC.Generics utilities

-- Natural transformation
infixl 1 -->
type a --> b = forall s. a s -> b s

exlF :: a :*: b --> a
exlF (a :*: _) = a

exrF :: a :*: b --> b
exrF (_ :*: b) = b

dupF :: a --> a :*: a
dupF a = a :*: a

curryF :: ((a :*: b) s -> c s) -> (a s -> b s -> c s)
curryF f a b = f (a :*: b)

uncurryF :: (a s -> b s -> c s) -> ((a :*: b) s -> c s)
uncurryF g (a :*: b) = g a b

-- Miscellany

unzip :: Functor f => f (a :* b) -> f a :* f b
unzip ps = (fst <$> ps, snd <$> ps)

