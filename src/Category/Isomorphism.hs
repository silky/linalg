{-# LANGUAGE UndecidableInstances #-} -- see below

-- {-# OPTIONS_GHC -Wno-unused-imports #-} -- TEMP

-- | Isomorphisms

module Category.Isomorphism where

import Prelude hiding (id,(.))
import qualified GHC.Generics as G
import GHC.Exts (Coercible,coerce)
import Data.Functor.Rep (Representable(..))
import Control.Newtype.Generics

import Misc
import Category

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

instance Associative k p => Associative (Iso k) p where
  lassoc = lassoc :<-> rassoc
  rassoc = rassoc :<-> lassoc

instance Symmetric k p => Symmetric (Iso k) p where
  swap = swap :<-> swap

-- We cannot use the default definitions for Associative and Symmetric, because
-- Iso k is not cartesian.

instance Monoidal k p => Monoidal (Iso k) p where
  (f :<-> f') *** (g :<-> g') = (f *** g) :<-> (f' *** g')

-- Illegal instance declaration for ‘Monoidal (Iso k) p’
--   The coverage condition fails in class ‘Monoidal’
--     for functional dependency: ‘k -> p’
--   Reason: lhs type ‘Iso k’ does not determine rhs type ‘p’
--   Un-determined variable: p
--   Using UndecidableInstances might help
--
-- TODO: revisit after monkeying with the Monoidal class.

instance Comonoidal k co => Comonoidal (Iso k) co where
  (f :<-> f') +++ (g :<-> g') = (f +++ g) :<-> (f' +++ g')

#if 0
instance UnitCat k => UnitCat (Iso k) where
  lunit   = lunit   :<-> lcounit
  runit   = runit   :<-> rcounit
  lcounit = lcounit :<-> lunit
  rcounit = rcounit :<-> runit
#endif

-------------------------------------------------------------------------------
-- | Utilities
-------------------------------------------------------------------------------

-- | Apply one isomorphism via another
via :: (Category k, Obj2 k a b) => Iso k b b -> Iso k a b -> Iso k a a
(g :<-> g') `via` (ab :<-> ba) = ba . g . ab :<-> ba . g' . ab

join2Iso :: (Cocartesian k co, Obj3 k a c d) 
         => (c `k` a) :* (d `k` a) <-> ((c `co` d) `k` a)
join2Iso = join2 :<-> unjoin2

fork2Iso :: (Cartesian k p, Obj3 k a c d)
         => (a `k` c) :* (a `k` d) <-> (a `k` (c `p` d))
fork2Iso = fork2 :<-> unfork2

joinIso :: (CocartesianR k r co, Obj2 k a b) => r (a `k` b) <-> co r a `k` b
joinIso = join :<-> unjoin

forkIso :: (CartesianR k r p, Obj2 k a b) => r (a `k` b) <-> (a `k` p r b)
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

fmapIso :: Functor f => (f <--> g) -> (a -> b) -> (g a -> g b)
fmapIso fg h = isoFwd fg . fmap h . isoRev fg

-- Don't pattern match fg, since we need two type instantiations.
-- For instance, the following doesn't type-check:
-- 
--   fmapIso (fg :<-> gf) h = fg . fmap h . gf

-- Is this fmapIso really the most useful and natural variant?
