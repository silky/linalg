{-# LANGUAGE UndecidableSuperClasses #-}
{-# LANGUAGE UndecidableInstances #-}

{-# OPTIONS_GHC -Wno-unused-imports #-} -- TEMP

-- | Functor category using array representation

module Category.Array where

import GHC.TypeLits
-- import GHC.TypeLits.KnownNat
import Data.Finite
import Data.Vector.Sized

import CatPrelude
import Category.Isomorphism

type ObjVec' k a = Obj k (Vector (Card (Rep a)))

class    ObjVec' k a => ObjVec k a  
instance ObjVec' k a => ObjVec k a  

type KnownCard i = KnownNat (Card i)

class KnownCard a => HasFin a where
  type Card a :: Nat
  finI :: a <-> Finite (Card a)

type VecC a = Vector (Card (Rep a))

newtype Arr k a b = Arr (VecC a `k` VecC b)

instance Category k => Category (Arr k) where
  type Obj' (Arr k) = ObjVec k
  id = Arr id
  Arr g . Arr f = Arr (g . f)


#if 0

instance Monoidal (:*:) k => Monoidal (:*:) (Arr k) where
  Arr f *** Arr g = Arr (f *** g)

f :: VecC a `k` VecC c
g :: VecC b `k` VecC d

f *** g :: (VecC a :*: VecC b) `k` (VecC c :*: VecC d)

-- Now use combineProduct and separateProduct. Oops: only available for (->).

-- f *** g :: VecC (a :*: b) `k` VecC (c :*: d)

VecC (a :*: b)
Vector (Card (Rep (a :*: b)))
Vector (Card (Rep a + Rep b))

#endif
