-- {-# OPTIONS_GHC -Wno-unused-imports #-} -- TEMP

{-# LANGUAGE AllowAmbiguousTypes #-}   -- See below

-- | Functor category classes

module Category where

import qualified Prelude as P
import Prelude hiding (id,(.))
import GHC.Types (Constraint)
import qualified Control.Arrow as A
-- import qualified Data.Tuple as T
import Data.Functor.Rep

import Misc

class    Yes1 a
instance Yes1 a

class Category (k :: u -> u -> *) where
  type Obj k :: u -> Constraint
  infixr 9 .
  id :: Obj k a => a `k` a
  (.) :: (b `k` c) -> (a `k` b) -> (a `k` c)

-- Experiment: omit Obj constraints for argument arrows.

type Obj2 k a b         = C2 (Obj k) a b
type Obj3 k a b c       = C3 (Obj k) a b c
type Obj4 k a b c d     = C4 (Obj k) a b c d
type Obj5 k a b c d e   = C5 (Obj k) a b c d e
type Obj6 k a b c d e f = C6 (Obj k) a b c d e f

class Category k => Monoidal k p | k -> p where
  infixr 3 ***
  (***) :: (a `k` c) -> (b `k` d) -> ((a `p` b) `k` (c `p` d))

-- Should we require p to be uniquely determined by k? Might help type
-- inference. We'd then need a "Comonoidal" class with "(+++)", which is
-- perhaps better.

class Monoidal k p => Cartesian k p where
  exl :: Obj2 k a b => (a `p` b) `k` a
  exr :: Obj2 k a b => (a `p` b) `k` b
  dup :: Obj  k a   => a `k` (a `p` a)

infixr 3 &&&
(&&&) :: (Cartesian k p, Obj3 k a c d)
      => (a `k` c) -> (a `k` d) -> (a `k` (c `p` d))
f &&& g = (f *** g) . dup

-- Can I instead extract the Obj constraints from f and g?

class Category k => Comonoidal k co | k -> co where
  infixr 2 +++
  (+++) :: (a `k` c) -> (b `k` d) -> ((a `co` b) `k` (c `co` d))

-- TODO: keep both Monoidal and Comonoidal or have one class with two instances
-- per category?

class Comonoidal k co => Cocartesian k co where
  inl :: Obj2 k a b => a `k` (a `co` b)
  inr :: Obj2 k a b => b `k` (a `co` b)
  jam :: Obj  k a   => (a `co` a) `k` a

infixr 2 |||
(|||) :: (Cocartesian k co, Obj3 k a b c)
      => (a `k` c) -> (b `k` c) -> ((a `co` b) `k` c)
f ||| g = jam . (f +++ g)


-- -- N-ary (representable) counterparts

class (Category k, Representable r) => MonoidalR k r where
  cross :: r (a `k` b) -> (r a `k` r b)

-- TODO: maybe "N" (for n-ary) instead of "R" (for representable) in these
-- class names. On the other hand, people will probably assume n is a number.

-- TODO: keep Representable r superclass constraint?

-- Oops! The type r (a `k` b) requires r :: * -> *, hence r a :: *, a :: *.
-- The Representable constraint does as well.
--
--   λ> :k Monoidal
--   Monoidal :: (u -> u -> *) -> (u -> u -> u) -> Constraint
--   λ> :k MonoidalR
--   MonoidalR :: (* -> * -> *) -> (* -> *) -> Constraint
--
-- For L, we have
-- 
--   cross :: (...) => c (L a b s) -> L (c :.: a) (c :.: b) s
--
-- What generalization are we after here?

class MonoidalR k r => CartesianR k r where
  exs :: r (r a `k` a)
  dups :: a `k` r a

fork :: (CartesianR k r, Obj2 k a c) => r (a `k` c) -> (a `k` r c)
fork fs = cross fs . dups

class (Category k, Representable r) => ComonoidalR k r where
  plus :: r (a `k` b) -> ((Rep r :* a) `k` (Rep r :* b))

class (Representable r, ComonoidalR k r) => CocartesianR k r where
  ins :: r (a `k` (Rep r :* a))
  jams :: (Rep r :* a) `k` a

-- Conal: I think (Repr r :*) is the right choice for n-ary sums.
-- See how it works out.

-- Couldn't match type ‘Rep r0’ with ‘Rep r’
-- Expected type: k (Rep r :* a) a
--   Actual type: k (Rep r0 :* a) a
-- NB: ‘Rep’ is a non-injective type family
-- The type variable ‘r0’ is ambiguous
-- In the ambiguity check for ‘jams’
-- To defer the ambiguity check to use sites, enable AllowAmbiguousTypes

-- -- Instances

instance Category (->) where
  type Obj (->) = Yes1
  id = P.id
  (.) = (P..)

instance Monoidal (->) (:*) where
  (***) = (A.***)

instance Cartesian (->) (:*) where
  exl = fst
  exr = snd
  dup = \ a -> (a,a)

instance Comonoidal (->) (:+) where
  (+++) = (A.+++)

instance Cocartesian (->) (:+) where
  inl = P.Left
  inr = P.Right
  jam = id A.||| id
  -- Equivalently,
  -- jam (Left  a) = a
  -- jam (Right a) = a

instance Representable p => MonoidalR (->) p where
  cross = liftR2 ($)

instance Representable p => CartesianR (->) p where
  exs = tabulate (flip index)
  dups = pureRep

instance Representable p => ComonoidalR (->) p where
  plus fs (i,a) = (i, (fs `index` i) a)

instance Representable p => CocartesianR (->) p where
  ins = tabulate (,)  -- = tabulate (\ i a -> (i, a))
  jams = snd
