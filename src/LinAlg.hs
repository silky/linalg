{-# LANGUAGE TypeOperators #-}

{-# OPTIONS_GHC -Wall #-}
{-# OPTIONS_GHC -Wno-unused-imports #-} -- TEMP

-- | Linear algebra for the post-Fortran age

module LinAlg where

import Control.Category

-- | A g × f "matrix" of morphisms from a to b
newtype Matrix f g k a b = M (g (f (a `k` b)))

-- instance Category (Matrix f g k) where
--   id = M (...)

-- Hm. I think I need to compose Matrix g h k b c with Matrix f g k a b to get a
-- Matrix f h k a b.
