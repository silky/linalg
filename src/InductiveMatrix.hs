{- |
"Inductive matrices", as in "Type Your Matrices for Great Good: A Haskell
Library of Typed Matrices and Applications (Functional Pearl)" Armando Santos
and José N Oliveira (Haskell Symposium 2020) [URL?]. The main differences:

- Representable functors rather than their index types (logarithms).
- Specified via denotational homomorphisms.
-}

module InductiveMatrix where

import CatPrelude

import LinearFunction hiding (L)
import Category.Isomorphism

-------------------------------------------------------------------------------
-- | Representation and its denotation
-------------------------------------------------------------------------------

infixr 3 :&#
infixr 2 :|#

type V = Representable

-- | Compositional linear map representation.
data L :: * -> (* -> *) -> (* -> *) -> * where
  Scale :: Semiring s => s -> L s Par1 Par1
  (:|#) :: (C3 V a b c, Additive s) => L s a c -> L s b c -> L s (a :*: b) c
  (:&#) :: C3 V a c k => L s a c -> L s a k -> L s a (c :*: k)
  JoinL :: (C2 V a b, Representable r, Eq (Rep r), Foldable r, Additive s)
        => r (L s a b) -> L s (r :.: a) b
  ForkL :: C3 V a b r => r (L s a b) -> L s a (r :.: b)

instance LinearMap L where
  mu = fwd :<-> rev
   where
     fwd :: L s a b -> F.L s a b
     fwd (Scale s)  = scale s
     fwd (f :|# g)  = fwd f ||| fwd g
     fwd (f :&# g)  = fwd f &&& fwd g
     fwd (JoinL fs) = join (fwd <$> fs)
     fwd (ForkL fs) = fork (fwd <$> fs)
     rev = error "TODO: implement reverse mu on L"

-- TODO: rebuild this fwd definition by composing isomorphisms, eliminating the
-- explicit fwd/rev split. This fwd definition is already built from invertible
-- operations (including scale and fmap of an invertible operation). Dan's
-- failable patterns may be relevant. Can we do so without abstraction leak and
-- without building in a decomposition bias?

-- TODO: Generalize from F.L to all linear map representations. I guess we'll
-- need the intersection of Obj constraints. Or is there a single Obj that all
-- linear map representations can share (not just all _current_)? With careful
-- choice of primitives on all linear map representations, we can probably write
-- a single representation-polymorphic isomorphism that works for _all_ pairs of
-- representations (not just all current). On the other hand, we could instead
-- compose an isomorphism to F.L with an isomorphism from F.L to get the
-- representation-polymorphic isomorphism.

-------------------------------------------------------------------------------
-- | Instances (all deducible from denotational homomorphisms)
-------------------------------------------------------------------------------

instance Category (L s) where
  type Obj' (L s) = V
  id = undefined
  (.) = undefined
