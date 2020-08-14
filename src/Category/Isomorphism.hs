{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE AllowAmbiguousTypes #-} -- see below

{-# LANGUAGE NoStarIsType #-}  -- for (*) on Nat

{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}

-- {-# OPTIONS_GHC -Wno-unused-imports #-} -- TEMP

-- | Isomorphisms

module Category.Isomorphism where

import qualified GHC.Generics as G
import GHC.Exts (Coercible,coerce)
import Data.Void
import Control.Newtype.Generics

import GHC.TypeLits
import Data.Finite
import qualified Data.Finite.Internal as FI

import CatPrelude

-------------------------------------------------------------------------------
-- | Representation
-------------------------------------------------------------------------------

infix 0 :<->
-- | Isomorphism
data Iso k a b = (:<->) { isoFwd :: a `k` b, isoRev :: b `k` a }

-- | Inverse isomorphism
inv :: Iso k a b -> Iso k b a
inv (f :<-> f') = f' :<-> f

-- | Form an ivolution from a _self-inverse_ arrow.
involution :: (a `k` a) -> Iso k a a
involution f = f :<-> f

infix 0 <->
type (<->) = Iso (->)

-------------------------------------------------------------------------------
-- | As a category
-------------------------------------------------------------------------------

instance Category k => Category (Iso k) where
  type Obj' (Iso k) = Obj k
  id = id :<-> id
  (g :<-> g') . (f :<-> f') = (g . f) :<-> (f' . g')

instance Associative p k => Associative p (Iso k) where
  lassoc = lassoc :<-> rassoc
  rassoc = rassoc :<-> lassoc

instance Symmetric p k => Symmetric p (Iso k) where
  swap = swap :<-> swap

-- We cannot use the default definitions for Associative and Symmetric, because
-- Iso k is not cartesian.

instance Monoidal p k => Monoidal p (Iso k) where
  (f :<-> f') *** (g :<-> g') = (f *** g) :<-> (f' *** g')

-- Illegal instance declaration for ‘Monoidal (Iso k) p’
--   The coverage condition fails in class ‘Monoidal’
--     for functional dependency: ‘k -> p’
--   Reason: lhs type ‘Iso k’ does not determine rhs type ‘p’
--   Un-determined variable: p
--   Using UndecidableInstances might help
--
-- TODO: revisit after monkeying with the Monoidal class.

instance Comonoidal co k => Comonoidal co (Iso k) where
  (f :<-> f') +++ (g :<-> g') = (f +++ g) :<-> (f' +++ g')

#if 0
instance UnitCat k => UnitCat (Iso k) where
  lunit   = lunit   :<-> lcounit
  runit   = runit   :<-> rcounit
  lcounit = lcounit :<-> lunit
  rcounit = rcounit :<-> runit
#endif

instance Closed e k => Closed e (Iso k) where
  (p :<-> p') ^^^ (q :<-> q') = (p ^^^ q) :<-> (p' ^^^ q')

-- TODO: is there a MonoidalClosed instance? I don't think so.

-- TODO: n-ary products and coproducts

-------------------------------------------------------------------------------
-- | Utilities
-------------------------------------------------------------------------------

-- | Apply one isomorphism via another
via :: (Category k, Obj2 k a b) => Iso k b b -> Iso k a b -> Iso k a a
(g :<-> g') `via` (ab :<-> ba) = ba . g . ab :<-> ba . g' . ab

join2Iso :: (Cocartesian co k, Obj3 k a c d)
         => (c `k` a) :* (d `k` a) <-> ((c `co` d) `k` a)
join2Iso = join2 :<-> unjoin2

fork2Iso :: (Cartesian p k, Obj3 k a c d)
         => (a `k` c) :* (a `k` d) <-> (a `k` (c `p` d))
fork2Iso = fork2 :<-> unfork2

joinIso :: (CocartesianR r co k, Obj2 k a b) => r (a `k` b) <-> co r a `k` b
joinIso = join :<-> unjoin

forkIso :: (CartesianR r p k, Obj2 k a b) => r (a `k` b) <-> (a `k` p r b)
forkIso = fork :<-> unfork

curryIso :: ((a :* b) -> c) <-> (a -> (b -> c))
curryIso = curry :<-> uncurry

-- TODO: generalize curry from (->) to cartesian closed

newIso :: Newtype a => a <-> O a
newIso = unpack :<-> pack

repIso :: Representable f => f a <-> (Rep f -> a)
repIso = index :<-> tabulate

coerceIso :: (Coercible a b, Coercible b a) => a <-> b
coerceIso = coerce :<-> coerce

genericIso :: G.Generic a => (a <-> G.Rep a x)
genericIso = G.from :<-> G.to

generic1Iso :: G.Generic1 f => (f <--> G.Rep1 f)
generic1Iso = G.from1 :<-> G.to1

-- | Natural isomorphism
infix 0 <-->
type f <--> g = forall a. f a <-> g a

fmapIso :: Functor f => a <-> b -> f a <-> f b
fmapIso (f :<-> g) = (fmap f :<-> fmap g)


-------------------------------------------------------------------------------
-- | Finite
-------------------------------------------------------------------------------

-- Some operations missing from Data.Finite.
-- TODO: pull request for finite-typelits

combineZero  :: Void -> Finite 0
combineZero = absurd
{-# INLINE combineZero #-}

absurdFinite :: Finite 0 -> a
absurdFinite = error "no Finite 0"  -- Hm.

separateZero :: Finite 0 -> Void
separateZero = absurdFinite
{-# INLINE separateZero #-}

combineOne :: () -> Finite 1
combineOne () = FI.Finite 0
{-# INLINE combineOne #-}

separateOne  :: Finite 1 -> ()
separateOne = const ()
{-# INLINE separateOne #-}

-- TODO: consider reversing the sense of finU1, finPar1, finSum and finProd

finU1 :: Void <-> Finite 0
finU1 = combineZero :<-> separateZero

finPar1 :: () <-> Finite 1
finPar1 = combineOne :<-> separateOne

finSum  :: C2 KnownNat m n => Finite m :+ Finite n <-> Finite (m + n)
finSum  = combineSum :<-> separateSum
{-# INLINE finSum #-}

finProd  :: C2 KnownNat m n => Finite m :* Finite n <-> Finite (m * n)
finProd  = combineProduct :<-> separateProduct
{-# INLINE finProd #-}

#if 0
vecU1 :: Vector 0 <--> U1
vecU1 = reindex finU1

vecPar1 :: Vector 1 <--> Par1
vecPar1 = reindex finPar1

reindex :: (Representable f, Representable g) => (Rep g <-> Rep f) -> (f <--> g)
reindex h = inv repIso . dom h . repIso
{-# INLINE reindex #-}

-- dom needs Closed. Adding in a new "closed" branch.
#endif
