{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE UndecidableSuperClasses #-} -- see below

{-# OPTIONS_GHC -Wno-orphans #-}

-- | Constraint entailment

module Category.Constraint where

import Data.Constraint

import CatPrelude

instance Category (:-) where
  id  = refl
  (.) = trans

-- Constraint (,) is not first class with GHC, so define a synonymous class.
class    (p,q) => p && q
instance (p,q) => p && q

-- Potential superclass cycle for ‘&&’
--   one of whose superclass constraints is headed by a type variable: ‘p’
-- Use UndecidableSuperClasses to accept this

instance Monoidal (&&) (:-) where
  p ### q = Sub (Dict \\ p \\ q)

instance Associative (&&) (:-) where
  lassoc = Sub Dict
  rassoc = Sub Dict

instance Symmetric (&&) (:-) where
  swap = Sub Dict

instance Cartesian (&&) (:-) where
  exl = Sub Dict
  exr = Sub Dict
  dup = Sub Dict

-- The Monoidal and Cartesian operations are lifted from Data.Constraint
-- equivalents but those types involve (,) instead of (&&), which would lead to
-- kind errors in instance declarations.

-- Constraint entailment could be cocartesian but isn't in GHC (presumably
-- because GHC instance search doesn't backtrac). On the other hand, entaliment
-- can probably be closed, now that GHC supports implication constraints.

infixr 1 ==>
class    (p => q) => (p ==> q)
instance (p => q) => (p ==> q)

-- Variable ‘p’ occurs more often
--   in the constraint ‘p’ than in the instance head ‘q’
-- (Use UndecidableInstances to permit this)

-- Is there a Closed instance?

-- instance Closed (==>) (:-) where
--   (^^^) :: (a :- b) -> (d :- c) -> ((c ==> a) :- (d ==> b))
--   f ^^^ g = ???
