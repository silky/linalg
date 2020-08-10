{-# LANGUAGE UndecidableInstances #-} -- see below

-- {-# OPTIONS_GHC -Wno-unused-imports #-} -- TEMP

-- | Opposite category

module Category.Opposite where

import Prelude hiding (id,(.))

import Category

newtype Op k a b = Op { unOp :: b `k` a }

instance Category k => Category (Op k) where
  type Obj' (Op k) = Obj k
  id = Op id
  Op g . Op f = Op (f . g)

instance Comonoidal k co => Monoidal (Op k) co where
  Op f *** Op g = Op (f +++ g)

instance Associative k p => Associative (Op k) p where
  lassoc = Op rassoc
  rassoc = Op lassoc

instance Symmetric k p => Symmetric (Op k) p where
  swap = Op swap

instance Cocartesian k co => Cartesian (Op k) co where
  exl = Op inl
  exr = Op inr
  dup = Op jam

instance Monoidal k p => Comonoidal (Op k) p where
  Op f +++ Op g = Op (f *** g)

instance Cartesian k p => Cocartesian (Op k) p where
  inl = Op exl
  inr = Op exr
  jam = Op dup

instance ComonoidalR k r p => MonoidalR (Op k) r p where
  cross (fmap unOp -> fs) = Op (plus fs)

instance MonoidalR k r p => ComonoidalR (Op k) r p where
  plus (fmap unOp -> fs) = Op (cross fs)

instance CocartesianR k r p => CartesianR (Op k) r p where
  exs  = Op <$> ins
  dups = Op jams

instance CartesianR k r p => CocartesianR (Op k) r p where
  ins  = Op <$> exs
  jams = Op dups

instance BiproductR k r p => BiproductR (Op k) r p


-- Illegal instance declaration for ‘Monoidal (Op k) co’
--   The coverage condition fails in class ‘Monoidal’
--     for functional dependency: ‘k -> p’
--   Reason: lhs type ‘Op k’ does not determine rhs type ‘co’
--   Un-determined variable: co
