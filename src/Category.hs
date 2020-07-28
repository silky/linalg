-- {-# OPTIONS_GHC -Wno-unused-imports #-} -- TEMP

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

class Category k => Monoidal k p where
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

class Monoidal k c => Cocartesian k c where
  inl :: Obj2 k a b => a `k` (a `c` b)
  inr :: Obj2 k a b => b `k` (a `c` b)
  jam :: Obj  k a   => (a `c` a) `k` a

-- N-ary (representable) counterparts

class Representable p => MonoidalRep k p where
  exs :: p (p a `k` a)
  dups :: a `k` p a

-- TODO: keep Representable p superclass constraint?

-- Oops! The type p (p a `k` a) requires p :: * -> *, hence p a :: *, a :: *.
-- The Representable constraint does as well.
--
--   λ> :k Monoidal
--   Monoidal :: (u -> u -> *) -> (u -> u -> u) -> Constraint
--   λ> :k MonoidalRep
--   MonoidalRep :: (* -> * -> *) -> (* -> *) -> Constraint
--
-- For L, we have
-- 
--   exs :: (...) => c (L (c :.: a) a s)
--
-- What's generalization are we after here?


-- Instances

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

instance Monoidal (->) (:+) where
  (***) = (A.+++)

-- Should we instead define a Comonoidal class with (+++)?

instance Cocartesian (->) (:+) where
  inl = P.Left
  inr = P.Right
  jam = id A.||| id
  -- jam (Left  a) = a
  -- jam (Right a) = a

instance Representable p => MonoidalRep (->) p where
  exs = tabulate (flip index)
  dups = pureRep
