{-# LANGUAGE UndecidableInstances #-} -- see below

-- | Linear algebra after Fortran

module LinAlg where

-- import qualified Prelude as P
import Prelude hiding ((+),sum,(*),unzip)

import GHC.Types (Constraint)
import GHC.Generics (Par1(..), (:*:)(..), (:.:)(..))
import qualified Control.Arrow as A
import Data.Distributive
import Data.Functor.Rep

-- Experiment
import Data.Constraint (Dict(..))

import Misc

type V f = ((Representable f, Foldable f, Eq (Rep f), ToScalar f, ToRowMajor f)
            :: Constraint)
type V2 f g = (V f, V g)
type V3 f g h = (V2 f g, V h)
type V4 f g h k = (V2 f g, V2 h k)

-- TODO: Why does V suddenly need ":: Constraint" after adding ToScalar f and
-- ToRowMajor f?

-- type V3f f g h = (V2 f g, Representable h)  -- for n-ary forks
-- type V3j f g h = (V3f f g h, Foldable h)    -- for n-ary joins

-- For the isV experiment below, I need more.
type V3f f g h = V3 f g h  -- for n-ary forks
type V3j f g h = V3 f g h  -- for n-ary joins

infixr 3 :&#
infixr 2 :|#

-- | Compositional Linear map representation. @L f g s@ denotes @f s -* g s@,
-- where @(-*)@ means linear functions.
data L :: (* -> *) -> (* -> *) -> (* -> *) where
  Scale :: s -> L Par1 Par1 s
  (:|#) :: V3 f g h => L f h s -> L g h s -> L (f :*: g) h s
  (:&#) :: V3 f h k => L f h s -> L f k s -> L f (h :*: k) s
  JoinL :: V3j f g h => h (L f g s) -> L (h :.: f) g s
  ForkL :: V3f f g h => h (L f g s) -> L f (h :.: g) s

unjoin2 :: V3 f g h => L (f :*: g) h s -> L f h s :* L g h s
unjoin2 (p :|# q) = (p,q)
unjoin2 ((unjoin2 -> (p,q)) :&# (unjoin2 -> (r,s))) = (p :& r, q :& s)
unjoin2 (ForkL ms) = (ForkL A.*** ForkL) (unzip (unjoin2 <$> ms))

-- unjoin2 ((p :| q) :&# (r :| s)) = (p :&# r, q :#& s)

-- Recursive pattern synonym definition with following bindings:
--   unjoin2 (defined at src/LinAlg.hs:(52,1)-(63,50))
--   :| (defined at src/LinAlg.hs:75:1-55)

#if 0
                               ForkL ms   :: L (f :*: g) (k :.: h) s
                                     ms   :: k (L (f :*: g) h s)
                          unjoin <$> ms   :: k (L f h s :* L g h s)
                   unzip (unjoin <$> ms)  :: k (L f h s) :* k (L g h s)
(ForkL *** ForkL) (unzip (unjoin <$> ms)) :: L f (k :.: h) s :* L g (k :.: h) s
#endif

unfork2 :: V3 f h k => L f (h :*: k) s -> L f h s :* L f k s
unfork2 (p :&# q) = (p,q)
unfork2 ((unfork2 -> (p,q)) :|# (unfork2 -> (r,s))) = (p :|# r, q :|# s)
unfork2 (JoinL ms) = (JoinL A.*** JoinL) (unzip (unfork2 <$> ms))

-- unfork2 ((p :& q) :|# (r :& s)) = (p :|# r, q :|# s)

pattern (:&) :: V3 f h k => L f h s -> L f k s -> L f (h :*: k) s
pattern u :& v <- (unfork2 -> (u,v)) where (:&) = (:&#)
{-# complete (:&) #-}

pattern (:|) :: V3 f g h => L f h s -> L g h s -> L (f :*: g) h s
pattern u :| v <- (unjoin2 -> (u,v)) where (:|) = (:|#)
{-# complete (:|) #-}

unforkL :: V3f f g h => L f (h :.: g) s -> h (L f g s)
unforkL (p :|# q)  = liftR2 (:|#) (unforkL p) (unforkL q)
unforkL (ForkL ms) = ms
unforkL (JoinL ms) = JoinL <$> distribute (unforkL <$> ms)

#if 0
-- Types for binary join clause
p :|# p' :: L (f :*: f') (h :.: g) s

                      p               :: L f  (h :.: g) s
                                  p'  :: L f' (h :.: g) s
              unforkL p               :: h (L f  g  s)
                          unforkL p'  :: h (L f' g  s)
liftR2 (:|#) (unforkL p) (unforkL p') :: h (L (f :*: f') g s)

-- Types for n-ary join clause:

     JoinL                     ms  :: L (k :.: f) (h :.: g) s
                               ms  :: k (L f (h :.: g) s)
                   unforkL <$> ms  :: k (h (L f g s))
          distrib (unforkL <$> ms) :: h (k (L f g s))
JoinL <$> distrib (unforkL <$> ms) :: h (L (k :.: f) g s)
#endif

unjoinL :: V3f f g h => L (h :.: f) g s -> h (L f g s)
unjoinL (p :&# p') = liftR2 (:&#) (unjoinL p) (unjoinL p')
unjoinL (JoinL ms) = ms
unjoinL (ForkL ms) = fmap ForkL (distribute (fmap unjoinL ms))

pattern Fork :: V3f f g h => h (L f g s) -> L f (h :.: g) s
pattern Fork ms <- (unforkL -> ms) where Fork = ForkL
{-# complete Fork #-}

pattern Join :: V3j f g h => h (L f g s) -> L (h :.: f) g s
pattern Join ms <- (unjoinL -> ms) where Join = JoinL
{-# complete Join #-}

instance (V2 f g, Additive s) => Additive (L f g s) where
  zero = zeroL
  Scale s + Scale s' = Scale (s + s') -- distributivity
  (f :|# g) + (h :| k) = (f + h) :| (g + k)
  (f :&# g) + (h :& k) = (f + h) :& (g + k)
  ForkL ms  + Fork ms' = Fork (ms +^ ms')
  JoinL ms  + Join ms' = Join (ms +^ ms')

-- | Row-major "matrix" of linear maps
rowMajor' :: (V2 f g, V2 h k) => k (h (L f g s)) -> L (h :.: f) (k :.: g) s
rowMajor' = Fork . fmap Join

-- | Row-major "matrix" of scalars
rowMajor :: (V f, V g) => g (f s) -> L (f :.: Par1) (g :.: Par1) s
rowMajor = rowMajor' . (fmap.fmap) Scale

diagRep :: (Representable h, Eq (Rep h)) => a -> h a -> h (h a)
diagRep dflt as =
  tabulate (\ i -> tabulate (\ j -> if i == j then as `index` i else dflt))

idL :: (V a, Semiring s) => L a a s
idL = scaleV one

infixr 9 .@
(.@) :: (V3 f g h, Semiring s) => L g h s -> L f g s -> L f h s
Scale a   .@ Scale b   = Scale (a * b)             -- Scale denotation
(r :|# s) .@ (p :&# q) = (r .@ p) + (s .@ q)       -- biproduct law
(p :&# q) .@ m         = (p .@ m) :&# (q .@ m)     -- binary product law
m         .@ (p :|# q) = (m .@ p) :|# (m .@ q)     -- binary coproduct law
JoinL ms' .@ ForkL ms  = sum (ms' .^ ms)           -- biproduct law
ForkL ms' .@ m         = ForkL (fmap (.@ m) ms')   -- n-ary product law
m'        .@ JoinL ms  = JoinL (fmap (m' .@) ms)   -- n-ary coproduct law

(.^) :: (V3 f g h, Representable p, Semiring s)
     => p (L g h s) -> p (L f g s) -> p (L f h s)
(.^) = liftR2 (.@)

instance (V f, Semiring s) => Semiring (L f f s) where
  one = idL
  (*) = (.@)

-- Binary injections

inl :: (V2 a b, Semiring s) => L a (a :*: b) s
inl = idL :& zero

inr :: (V2 a b, Semiring s) => L b (a :*: b) s
inr = zero :& idL

-- Binary projections

exl :: (V2 a b, Semiring s) => L (a :*: b) a s
exl = idL :| zero

exr :: (V2 a b, Semiring s) => L (a :*: b) b s
exr = zero :| idL

-- Note that idL == inl :| inr == exl :& exr.

-- N-ary injections
ins :: (V2 a c, Semiring s) => c (L a (c :.: a) s)
ins = unjoinL idL

-- N-ary projections
exs :: (V2 a c, Semiring s) => c (L (c :.: a) a s)
exs = unforkL idL

-- Note that idL == joinL ins == forkL exs

-- Binary biproduct bifunctor
(***) :: (V4 a b c d, Additive s)
      => L a c s -> L b d s -> L (a :*: b) (c :*: d) s
f *** g = (f :|# zero) :&# (zero :|# g)

-- N-ary biproduct bifunctor
cross :: (V3 a b c, Additive s) => c (L a b s) -> L (c :.: a) (c :.: b) s
cross = JoinL . fmap ForkL . diagRep zero

{- Note that

f *** g == (f :|# zero) :&# (zero :|# g)
        == (f :&# zero) :|# (zero :&# g)
        == (f .@ exl) :&# (g .@ exr)
        == (inl .@ f) :|# (inr .@ g)

cross fs == JoinL (ins .^ fs)
         == ForkL (fs .^ exs)

-}

-- See discussion in https://github.com/conal/linalg/pull/26

-- Linear algebra duality isomorphism: a s =~ a s :-* s.
class ToScalar a where
  rowToL :: a s -> L a Par1 s
  lToRow :: L a Par1 s -> a s

pattern RowToL :: ToScalar a => a s -> L a Par1 s
pattern RowToL a <- (lToRow -> a) where RowToL = rowToL
{-# complete RowToL #-}

type ToScalar2 a b = (ToScalar a, ToScalar b)

instance ToScalar Par1 where
  rowToL (Par1 s) = Scale s
  lToRow (Scale s) = Par1 s

instance V2 a b => ToScalar (a :*: b) where
  rowToL (a :*: b) = RowToL a :| RowToL b
  lToRow (RowToL a :| RowToL b) = a :*: b

instance V2 a b => ToScalar (b :.: a) where
  rowToL (Comp1 as) = Join (rowToL <$> as)
  lToRow (Join m) = Comp1 (lToRow <$> m)

--                  as  :: b (a s)
--       rowToL <$> as  :: b (L a Par1 s)
-- Join (rowToL <$> as) :: L (b :.: a) Par1 s

-- Row-major matrix
type Rows a b s = b (a s)

-- TODO: maybe "type Rows a b = b :.: a". If so, the zeroL' definition will have
-- one pureRep instead of two, but every ToRowMajor clause will get an
-- additional Comp1.

-- Matrices and vector spaces are isomorphic, row-major version
class ToRowMajor b where
  rowMajToL :: V a => Rows a b s -> L a b s
  lToRowMaj :: V a => L a b s -> Rows a b s

type ToRowMajor2 a b = (ToRowMajor a, ToRowMajor b)

pattern RowMajToL :: (V a, ToRowMajor b) => Rows a b s -> L a b s
pattern RowMajToL as <- (lToRowMaj -> as) where RowMajToL = rowMajToL
{-# complete RowMajToL #-}

instance ToRowMajor Par1 where
  rowMajToL (Par1 a) = rowToL a
  lToRowMaj (RowToL a) = Par1 a

instance V2 b b' => ToRowMajor (b :*: b') where
  rowMajToL (as :*: as') = RowMajToL as :& RowMajToL as'
  lToRowMaj (RowMajToL as :& RowMajToL as') = as :*: as'

instance V2 a b => ToRowMajor (b :.: a) where
  rowMajToL (Comp1 as) = Fork (rowMajToL <$> as)
  lToRowMaj (Fork m) = Comp1 (lToRowMaj <$> m)

-- TODO: Similarly for ToCol and ToColMajor

-- The zero linear map
zeroL :: (V2 a b, Additive s) => L a b s
zeroL = rowMajToL (pureRep (pureRep zero))

-- Vector scaling
scaleV :: (V a, Additive s) => s -> L a a s
scaleV s = rowMajToL (diagRep zero (pureRep s))


-- -- Experiment

-- Prove V/Obj constraints from morphisms
isV :: L a b s -> Dict (V2 a b)
isV (Scale _) = Dict
isV (_ :|# _) = Dict
isV (_ :&# _) = Dict
isV (JoinL _) = Dict
isV (ForkL _) = Dict

infixr 9 @.@
(@.@) :: Semiring s => L b c s -> L a b s -> L a c s
-- b @.@ a | (Dict, Dict) <- (isV a, isV b) = b .@ a

-- b@(isV -> Dict) @.@ a@(isV -> Dict) = b .@ a

pattern IsV :: () => V2 a b => L a b s
pattern IsV <- (isV -> Dict)
{-# COMPLETE IsV :: L #-}

b@IsV @.@ a@IsV = b .@ a
