-- {-# OPTIONS_GHC -Wno-unused-imports #-} -- TEMP

{-# LANGUAGE AllowAmbiguousTypes #-}   -- See below

-- | Functor category classes

module Category where

import qualified Prelude as P
import Prelude hiding (id,(.))
import GHC.Types (Constraint)
import qualified Control.Arrow as A
import GHC.Generics ((:.:)(..))
import Data.Functor.Rep

import Misc

class    Unconstrained a
instance Unconstrained a

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

-- The functional dependency requires p to be uniquely determined by k. Might
-- help type inference. Necessitates a "Comonoidal" class with "(+++)", which is
-- perhaps better than giving two Monoidal instances for a single category (eg
-- for (->)).

class Monoidal k p => Cartesian k p where
  exl :: Obj2 k a b => (a `p` b) `k` a
  exr :: Obj2 k a b => (a `p` b) `k` b
  dup :: Obj  k a   => a `k` (a `p` a)

-- Binary fork
infixr 3 &&&
(&&&) :: (Cartesian k p, Obj3 k a c d)
      => (a `k` c) -> (a `k` d) -> (a `k` (c `p` d))
f &&& g = (f *** g) . dup

-- Can I instead extract the Obj constraints from f and g?

-- Inverse of uncurry (&&&)
unfork2 :: (Cartesian k p, Obj2 k c d)
        => (a `k` (c `p` d)) -> ((a `k` c) :* (a `k` d))
unfork2 f = (exl . f , exr . f)

pattern (:&) :: (Cartesian k p, Obj3 k a c d)
             => (a `k` c) -> (a `k` d) -> (a `k` (c `p` d))
pattern f :& g <- (unfork2 -> (f,g)) where (:&) = (&&&)
-- {-# complete (:&) #-}

-- GHC error:
-- 
--   A type signature must be provided for a set of polymorphic pattern synonyms.
--   In {-# complete :& #-}
--
-- Instead, give a typed COMPLETE pragma with each cartesian category instance.

class Category k => Comonoidal k co | k -> co where
  infixr 2 +++
  (+++) :: (a `k` c) -> (b `k` d) -> ((a `co` b) `k` (c `co` d))

-- TODO: keep both Monoidal and Comonoidal or have one class with two instances
-- per category?

class Comonoidal k co => Cocartesian k co where
  inl :: Obj2 k a b => a `k` (a `co` b)
  inr :: Obj2 k a b => b `k` (a `co` b)
  jam :: Obj  k a   => (a `co` a) `k` a

-- Binary join
infixr 2 |||
(|||) :: (Cocartesian k co, Obj3 k a b c)
      => (a `k` c) -> (b `k` c) -> ((a `co` b) `k` c)
f ||| g = jam . (f +++ g)

-- Inverse of uncurry (|||)
unjoin2 :: (Cocartesian k co, Obj2 k a b) => ((a `co` b) `k` c) -> ((a `k` c) :* (b `k` c))
unjoin2 f = (f . inl , f . inr)

pattern (:|) :: (Cocartesian k co, Obj3 k a b c)
             => (a `k` c) -> (b `k` c) -> ((a `co` b) `k` c)
pattern f :| g <- (unjoin2 -> (f,g)) where (:|) = (|||)
-- {-# complete (:|) #-}  -- See (:&) above


-- -- N-ary (representable) counterparts.

-- Assumes functor categories. To do: look for a clean, poly-kinded alternative.
-- I guess we could generalize from functor composition and functor application.

class (Category k, Representable r) => MonoidalR k r where
  cross :: r (a `k` b) -> ((r :.: a) `k` (r :.: b))

class MonoidalR k r => CartesianR k r where
  exs :: r ((r :.: a) `k` a)
  dups :: a `k` (r :.: a)

fork :: (CartesianR k r, Obj2 k a c) => r (a `k` c) -> (a `k` (r :.: c))
fork fs = cross fs . dups

#if 0

class (Category k, Representable r) => ComonoidalR k r where
  plus :: r (a `k` b) -> ((Rep r :* a) `k` (Rep r :* b))

class (Representable r, ComonoidalR k r) => CocartesianR k r where
  ins :: r (a `k` (Rep r :* a))
  jams :: (Rep r :* a) `k` a

-- Conal: Is Repr r :* the right choice for n-ary coproducts? See how it works
-- out. No. For linear maps (and thus for their representations), we'll want r a
-- instead, with jams = sum and one-hot ins.

-- Couldn't match type ‘Rep r0’ with ‘Rep r’
-- Expected type: k (Rep r :* a) a
--   Actual type: k (Rep r0 :* a) a
-- NB: ‘Rep’ is a non-injective type family
-- The type variable ‘r0’ is ambiguous
-- In the ambiguity check for ‘jams’
-- To defer the ambiguity check to use sites, enable AllowAmbiguousTypes

#endif

-- Try specializing to bifunctor categories instead. Reconsider naming.
class CartesianR k r => BifunctorR k r where
  ins :: r (a `k` (r :.: a))
  jams :: (r :.: a) `k` a

-- -- Instances

instance Category (->) where
  type Obj (->) = Unconstrained
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

#if 0

-- These instances are broken now that MonoidalR etc assumes functor categories.

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

#endif
