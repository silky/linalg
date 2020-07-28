{-# LANGUAGE UndecidableInstances #-} -- see below

-- | Linear algebra after Fortran

module LinAlg where

import qualified Prelude as P
import Prelude hiding ((+),sum,(*),unzip)

import GHC.Types (Constraint)
import GHC.Generics (Par1(..), (:*:)(..), (:.:)(..))
import qualified Control.Arrow as A
import Data.Distributive
import Data.Functor.Rep

infixl 7 :*
type (:*)  = (,)

-- infixl 6 :+
-- type (:+)  = Either

unzip :: Functor f => f (a :* b) -> f a :* f b
unzip ps = (fst <$> ps, snd <$> ps)

type V f = ((Representable f, Foldable f, Eq (Rep f), HasZA f, HasZB f) :: Constraint)
type V2 f g = (V f, V g)
type V3 f g h = (V2 f g, V h)
type V4 f g h k = (V2 f g, V2 h k)

-- Why does V suddenly need ":: Constraint" after adding HasZA f and HasZB f?

class Additive a where
  infixl 6 +
  zero :: a
  (+) :: a -> a -> a

class Additive a => Semiring a where
  infixl 7 *
  one :: a
  (*) :: a -> a -> a

sum :: (Foldable f, Additive a) => f a -> a
sum = foldr (+) zero

-- | Vector addition
infixl 6 +^
(+^) :: (Representable f, Additive s) => f s -> f s -> f s
(+^) = liftR2 (+)

instance Additive Double where { zero = 0; (+) = (P.+) }
instance Semiring Double where { one  = 1; (*) = (P.*) }

infixr 3 :&#
infixr 2 :|#

-- | Compositional Linear map representation. @L f g s@ denotes @f s -* g s@,
-- where @(-*)@ means linear functions.
data L :: (* -> *) -> (* -> *) -> (* -> *) where
  Scale :: s -> L Par1 Par1 s
  (:|#) :: V3 f g h => L f h s -> L g h s -> L (f :*: g) h s
  (:&#) :: V3 f h k => L f h s -> L f k s -> L f (h :*: k) s
  JoinL :: V3 f g h => h (L f g s) -> L (h :.: f) g s
  ForkL :: V3 f g h => h (L f g s) -> L f (h :.: g) s

-- Scalable vectors
class V a => HasScaleV a where
  scaleV :: Semiring s => s -> L a a s

type HasScaleV2 a b = (HasScaleV a, HasScaleV b)

instance HasScaleV Par1 where scaleV = Scale

instance HasScaleV2 a b => HasScaleV (a :*: b) where
  scaleV s = scaleV s *** scaleV s

instance (HasScaleV2 a b, Representable b) => HasScaleV (b :.: a) where
  scaleV s = cross (pureRep (scaleV s))

unjoin2 :: (V3 f g h, Additive s) => L (f :*: g) h s -> L f h s :* L g h s
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

unfork2 :: (V3 f h k, Additive s) => L f (h :*: k) s -> L f h s :* L f k s
unfork2 (p :&# q) = (p,q)
unfork2 ((unfork2 -> (p,q)) :|# (unfork2 -> (r,s))) = (p :|# r, q :|# s)
unfork2 (JoinL ms) = (JoinL A.*** JoinL) (unzip (unfork2 <$> ms))

-- unfork2 ((p :& q) :|# (r :& s)) = (p :|# r, q :|# s)

pattern (:&) :: (V3 f h k, Additive s) => L f h s -> L f k s -> L f (h :*: k) s
pattern u :& v <- (unfork2 -> (u,v)) where (:&) = (:&#)
{-# complete (:&) #-}

pattern (:|) :: (V3 f g h, Additive s) => L f h s -> L g h s -> L (f :*: g) h s
pattern u :| v <- (unjoin2 -> (u,v)) where (:|) = (:|#)
{-# complete (:|) #-}

-- pattern Join :: V h => h (L f g s) -> L (h :.: f) g s
-- pattern Join ms <- (unjoinL -> ms) where Join = JoinL
-- {-# complete Join #-}

unforkL :: V3 f g h => L f (h :.: g) s -> h (L f g s)
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

unjoinL :: V3 f g h => L (h :.: f) g s -> h (L f g s)
unjoinL (p :&# p') = liftR2 (:&#) (unjoinL p) (unjoinL p')
unjoinL (JoinL ms) = ms
unjoinL (ForkL ms) = fmap ForkL (distribute (fmap unjoinL ms))

pattern Fork :: V3 f g h => h (L f g s) -> L f (h :.: g) s
pattern Fork ms <- (unforkL -> ms) where Fork = ForkL
{-# complete Fork #-}

pattern Join :: V3 f g h => h (L f g s) -> L (h :.: f) g s
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

idL :: (HasScaleV a, Semiring s) => L a a s
idL = scaleV one

infixr 9 .@
(.@) :: (V3 f g h, Semiring s) => L g h s -> L f g s -> L f h s
Scale a   .@ Scale b   = Scale (a * b)             -- Scale denotation
(p :&# q) .@ m         = (p .@ m) :&# (q .@ m)     -- binary product law
m         .@ (p :|# q) = (m .@ p) :|# (m .@ q)     -- binary coproduct law
(r :|# s) .@ (p :&# q) = (r .@ p) + (s .@ q)       -- biproduct law
ForkL ms' .@ m         = ForkL (fmap (.@ m) ms')   -- n-ary product law
m'        .@ JoinL ms  = JoinL (fmap (m' .@) ms)   -- n-ary coproduct law
JoinL ms' .@ ForkL ms  = sum (ms' .^ ms)           -- biproduct law

(.^) :: (V3 f g h, Representable p, Semiring s)
     => p (L g h s) -> p (L f g s) -> p (L f h s)
(.^) = liftR2 (.@)

instance (HasScaleV f, Semiring s) => Semiring (L f f s) where
  one = idL
  (*) = (.@)

-- Binary injections

inl :: (HasScaleV a, V b, Semiring s) => L a (a :*: b) s 
inl = idL :& zero

inr :: (V a, HasScaleV b, Semiring s) => L b (a :*: b) s 
inr = zero :& idL

-- Binary projections

exl :: (HasScaleV a, V b, Semiring s) => L (a :*: b) a s 
exl = idL :| zero

exr :: (V a, HasScaleV b, Semiring s) => L (a :*: b) b s 
exr = zero :| idL

-- Note that idL == inl :| inr == exl :& exr.

-- N-ary injections
ins :: (HasScaleV2 a c, Semiring s) => c (L a (c :.: a) s)
ins = unjoinL idL

-- N-ary projections
exs :: (HasScaleV2 a c, Semiring s) => c (L (c :.: a) a s)
exs = unforkL idL

-- Note that idL == joinL ins == forkL exs

-- Binary biproduct bifunctor
(***) :: (V4 a b c d, Additive s) => L a c s -> L b d s -> L (a :*: b) (c :*: d) s
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

-- The zero linear map
zeroL :: (V2 a b, Additive s) => L a b s
zeroL = zeroF

-- zeroL has a tidier ":i" signature than zeroF

class HasZA a where zeroJ :: Additive s => L a Par1 s
class HasZB b where zeroF :: (HasZA a, V a, Additive s) => L a b s

instance HasZA Par1 where zeroJ = Scale zero
instance (HasZA a, HasZA a', V2 a a') => HasZA (a :*: a') where zeroJ = zeroJ :| zeroJ
instance (HasZA a, V c, V a) => HasZA (c :.: a) where zeroJ = JoinL (pureRep zeroJ)

instance HasZB Par1 where zeroF = zeroJ
instance (HasZB b, HasZB b', V2 b b') => HasZB (b :*: b') where zeroF = zeroF :& zeroF
instance (HasZB b, V c, V b) => HasZB (c :.: b) where zeroF = ForkL (pureRep zeroF)

-- Illegal nested constraint ‘Eq (Rep c)’
-- (Use UndecidableInstances to permit this)
