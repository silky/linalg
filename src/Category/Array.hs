{-# LANGUAGE UndecidableSuperClasses #-}
{-# LANGUAGE UndecidableInstances #-}

{-# OPTIONS_GHC -Wno-unused-imports #-} -- TEMP

-- | Functor category using array representation

module Category.Array where

import GHC.TypeLits
-- import GHC.TypeLits.KnownNat
import Data.Finite
import Data.Vector.Sized (Vector)

import CatPrelude
import Category.Isomorphism

type ObjVec' k a = Obj k (Vector (Card (Rep a)))

class    ObjVec' k a => ObjVec k a  
instance ObjVec' k a => ObjVec k a  

newtype Arr k a b = Arr (VecCard a `k` VecCard b)

instance Category k => Category (Arr k) where
  type Obj' (Arr k) = ObjVec k
  id = Arr id
  Arr g . Arr f = Arr (g . f)

#if 0

instance Monoidal (:*:) k => Monoidal (:*:) (Arr k) where
  Arr f *** Arr g = Arr (f *** g)

f :: VecCard a `k` VecCard c
g :: VecCard b `k` VecCard d

f *** g :: (VecCard a :*: VecCard b) `k` (VecCard c :*: VecCard d)

need :: VecCard (a :*: b) `k` VecCard (c :*: d)

-- Bridge the gap with vecTrie. Oops: only available for (->) but not k

#endif
