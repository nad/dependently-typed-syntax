------------------------------------------------------------------------
-- A well-typed representation of a dependently typed language
------------------------------------------------------------------------

-- This module illustrates how the modules under deBruijn can be used.

-- The representation uses the technique which Conor McBride
-- introduced in "Outrageous but Meaningful Coincidences: Dependent
-- type-safe syntax and evaluation".

-- The code is parametrised by an arbitrary (small) universe.

open import Level using (zero)
open import Universe

module README.DependentlyTyped (Uni₀ : Universe zero zero) where
