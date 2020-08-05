-- {-# OPTIONS_GHC -Wno-unused-imports #-} -- TEMP

{-# LANGUAGE AllowAmbiguousTypes #-}   -- See below

-- | Functor category classes

module Category where

import qualified Prelude as P
import Prelude hiding (id,(.))
import GHC.Types (Constraint)
import qualified Control.Arrow as A
import GHC.Generics (Par1,(:.:)(..))
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

-- TODO: Maybe eliminate all type definitions based on Obj2 .. Obj6 in favor of
-- their definitions, which are not much longer anyway.

class Category k => Monoidal k p | k -> p where
  infixr 3 ***
  (***) :: (a `k` c) -> (b `k` d) -> ((a `p` b) `k` (c `p` d))

-- The functional dependency requires p to be uniquely determined by k. Might
-- help type inference. Necessitates a "Comonoidal" class with "(+++)", which is
-- perhaps better than giving two Monoidal instances for a single category (eg
-- for (->)).

-- TODO: make p an associated type, and see how the class and instance
-- definitions look in comparison.

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

-- TODO: How can we know that uncurry (&&&) and unfork2 form an isomorphism?

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

-- TODO: How can we know that uncurry (|||) and unjoin2 form an isomorphism?

pattern (:|) :: (Cocartesian k co, Obj3 k a b c)
             => (a `k` c) -> (b `k` c) -> ((a `co` b) `k` c)
pattern f :| g <- (unjoin2 -> (f,g)) where (:|) = (|||)
-- {-# complete (:|) #-}  -- See (:&) above

-- When products and coproducts coincide
class (Cartesian k p, Cocartesian k p) => Biproduct k p

-- TODO: perhaps merge Cartesian and Cocartesian and rename "Biproduct".
-- Ditto for the representable counterparts below.

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


-- -- N-ary (representable) counterparts.

-- Assumes functor categories. To do: look for a clean, poly-kinded alternative.
-- I guess we could generalize from functor composition and functor application.

class Category k => MonoidalR k where
  cross :: Representable r => r (a `k` b) -> ((r :.: a) `k` (r :.: b))

-- TODO: maybe wire in p = (:*:) for Monoidal, since we're doing essentially the
-- same for MonoidalR by choosing Representable r and (:.:).

class MonoidalR k => CartesianR k where
  exs :: Representable r => r ((r :.: a) `k` a)
  dups :: Representable r => a `k` (r :.: a)

fork :: (CartesianR k, Obj2 k a c, Representable r) => r (a `k` c) -> (a `k` (r :.: c))
fork fs = cross fs . dups

unfork :: (CartesianR k, Representable r) => a `k` (r :.: b) -> r (a `k` b)
unfork f = (. f) <$> exs

-- TODO: How can we know that fork and unfork form an isomorphism?

-- N-ary biproducts
class CartesianR k => BiproductR k where
  ins  :: (Representable r, Eq (Rep r), Obj k a) => r (a `k` (r :.: a))
  jams :: (Representable r, Foldable r, Obj k a) => (r :.: a) `k` a

-- TODO: Maybe replace (Representable r, Eq (Rep r), Foldable r) with an
-- associated functor constraint.

join :: (BiproductR k, Representable r, Foldable r, Obj2 k a b) => r (a `k` b) -> (r :.: a) `k` b
join fs = jams . cross fs  -- note cross == plus

unjoin :: (BiproductR k, Obj2 k a b, Representable r, Eq (Rep r))
       => (r :.: a) `k` b -> r (a `k` b)
unjoin f = (f .) <$> ins

-- TODO: Add fork & unfork to CartesianR with the current definitions as
-- defaults and giving defaults for exs and dups in terms of fork and unfork.
-- Ditto for ins/jams and join/unjoin. Use MINIMAL pragmas.

-- TODO: Abelian

class (Biproduct (l s) p, BiproductR (l s)) => Linear s l p where
  scale :: s -> l s Par1 Par1
  infixl 9 @@  -- Linear application
  (@@) :: l s a b -> a s -> b s  -- linear
