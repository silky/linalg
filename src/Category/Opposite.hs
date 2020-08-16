{-# LANGUAGE UndecidableInstances #-} -- see below

-- {-# OPTIONS_GHC -Wno-unused-imports #-} -- TEMP

-- | Opposite category

module Category.Opposite where

import CatPrelude

newtype Op k a b = Op { unOp :: b `k` a }

instance Category k => Category (Op k) where
  type Obj' (Op k) a = Obj k a
  id = Op id
  Op g . Op f = Op (f . g)

instance Comonoidal co k => Monoidal co (Op k) where
  Op f *** Op g = Op (f +++ g)

instance Associative p k => Associative p (Op k) where
  lassoc = Op rassoc
  rassoc = Op lassoc

instance Symmetric p k => Symmetric p (Op k) where
  swap = Op swap

instance Cocartesian co k => Cartesian co (Op k) where
  exl = Op inl
  exr = Op inr
  dup = Op jam

instance Monoidal p k => Comonoidal p (Op k) where
  Op f +++ Op g = Op (f *** g)

instance Cartesian p k => Cocartesian p (Op k) where
  inl = Op exl
  inr = Op exr
  jam = Op dup

instance ComonoidalR r p k => MonoidalR r p (Op k) where
  cross (fmap unOp -> fs) = Op (plus fs)

instance MonoidalR r p k => ComonoidalR r p (Op k) where
  plus (fmap unOp -> fs) = Op (cross fs)

instance CocartesianR r p k => CartesianR r p (Op k) where
  exs  = Op <$> ins
  dups = Op jams

instance CartesianR r p k => CocartesianR r p (Op k) where
  ins  = Op <$> exs
  jams = Op dups

instance BiproductR r p k => BiproductR r p (Op k)


-- Illegal instance declaration for ‘Monoidal (Op k) co’
--   The coverage condition fails in class ‘Monoidal’
--     for functional dependency: ‘k -> p’
--   Reason: lhs type ‘Op k’ does not determine rhs type ‘co’
--   Un-determined variable: co
