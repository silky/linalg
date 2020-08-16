-- {-# OPTIONS_GHC -Wno-unused-imports #-} -- TEMP

-- | Opposite category

module Category.Opposite where

import CatPrelude

newtype Op k a b = Op { unOp :: b `k` a }

instance Category k => Category (Op k) where
  type Obj' (Op k) a = Obj k a
  id = Op id
  Op g . Op f = Op (f . g)

instance Monoidal co k => Monoidal co (Op k) where
  Op f ### Op g = Op (f ### g)

instance Associative p k => Associative p (Op k) where
  lassoc = Op rassoc
  rassoc = Op lassoc

instance Symmetric p k => Symmetric p (Op k) where
  swap = Op swap

instance Cocartesian co k => Cartesian co (Op k) where
  exl = Op inl
  exr = Op inr
  dup = Op jam

instance Cartesian p k => Cocartesian p (Op k) where
  inl = Op exl
  inr = Op exr
  jam = Op dup

instance Biproduct p k => Biproduct p (Op k)

instance Closed e k => Closed e (Op k) where
  Op f ^^^ Op g = Op (f ^^^ g)

instance MonoidalR r p k => MonoidalR r p (Op k) where
  bifunctor (fmap unOp -> fs) = Op (bifunctor fs)

instance CocartesianR r p k => CartesianR r p (Op k) where
  exs  = Op <$> ins
  dups = Op jams

instance CartesianR r p k => CocartesianR r p (Op k) where
  ins  = Op <$> exs
  jams = Op dups

instance BiproductR r p k => BiproductR r p (Op k)
