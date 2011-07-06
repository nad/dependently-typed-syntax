------------------------------------------------------------------------
-- A well-typed representation of a dependently typed language
------------------------------------------------------------------------

-- The code is parametrised by an arbitrary (small) universe.

open import Level using (zero)
open import Universe

module README.DependentlyTyped (Uni₀ : Universe zero zero) where
