-- | Linear algebra after Fortran

module LinAlg.L1 where

import qualified Prelude as P
import Prelude hiding ((+))
import Data.Kind

infixl 7 :*
infixl 6 :+

type (:*)  = (,)
type (:+)  = Either

class Additive u where
  infixl 6 +
  (+) :: u -> u -> u

type R = Double

instance Additive R where (+) = (P.+)

instance (Additive a, Additive b) => Additive (a :* b) where
  (a,b) + (a',b') = (a+a', b+b')

type Additive2 a b = (Additive a, Additive b)
type Additive3 a b c = (Additive2 a b, Additive c)

data L :: Type -> Type -> Type where
  Scale :: Num a => a -> L a a  -- TODO: Semiring instead of Num
  ForkL :: Additive3 u v v' => L u v -> L u v' -> L u (v :* v')
  JoinL :: Additive3 u u' v => L u v -> L u' v -> L (u :* u') v

unforkL :: Additive2 v v' => L u (v :* v') -> L u v :* L u v'
unforkL (Scale _) = error "oops"  -- TODO: eliminate this partiality
unforkL (ForkL f g) = (f,g)
unforkL (JoinL f g) = (JoinL p r, JoinL q s)
 where
  (p,q) = unforkL f
  (r,s) = unforkL g

-- unforkL (JoinL f g) = (joinL *** joinL) (transpose (unforkL f, unforkL g))

-- transpose :: (a :* b) :* (c :* d) -> (a :* c) :* (b :* d)
-- transpose ((a,b),(c,d)) = ((a,c),(b,d))

-- JoinL f g :: L (u * u') (v :* v')
-- f :: L u  (v :* v')
-- g :: L u' (v * v')
-- p :: L u v
-- q :: L u v'
-- r :: L u' v
-- s :: L u' v'

unjoinL :: Additive2 u u' => L (u :* u') v -> L u v :* L u' v
unjoinL (Scale _) = error "oops"  -- TODO: eliminate this partiality
unjoinL (JoinL f g) = (f,g)
unjoinL (ForkL f g) = (ForkL p r, ForkL q s)
 where
  (p,q) = unjoinL f
  (r,s) = unjoinL g

pattern Fork :: Additive3 u v v' => L u v -> L u v' -> L u (v :* v')
pattern Fork f g <- (unforkL -> (f,g))
 where Fork = ForkL
{-# complete Fork #-}

pattern Join :: Additive3 u u' v => L u v -> L u' v -> L (u :* u') v
pattern Join f g <- (unjoinL -> (f,g))
 where Join = JoinL
{-# complete Join #-}

instance Additive2 u v => Additive (L u v) where
  Scale a + Scale b = Scale (a + b)  -- distributive law
  ForkL f g + Fork f' g' = ForkL (f + f') (g + g')
  JoinL f g + Join f' g' = JoinL (f + f') (g + g')

  -- Same partiality bug as unforkL and unjoinL
  _ + _ = error "oops"  -- Scale + ForkL or Scale + JoinL

-- Pattern match(es) are non-exhaustive
-- In an equation for ‘+’:
--     Patterns not matched:
--         (Scale _) (ForkL _ _)
--         (Scale _) (JoinL _ _)

infixr 9 .@
(.@) :: Additive2 u w => L v w -> L u v -> L u w
Scale a .@ Scale b = Scale (a * b)                -- Scale denotation
JoinL h k .@ Fork f g = h .@ f + k .@ g   -- biproduct law
ForkL h k .@ g = ForkL (h .@ g) (k .@ g)  -- categorical product law
h .@ JoinL f g = JoinL (h .@ f) (h .@ g)  -- categorical coproduct law
_ .@ _ = undefined  -- see below

-- Pattern match(es) are non-exhaustive
-- In an equation for ‘comp’:
--     Patterns not matched: (Scale _) (ForkL _ _)

-- Same partiality issue as above.

