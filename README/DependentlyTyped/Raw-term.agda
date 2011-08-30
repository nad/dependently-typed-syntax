------------------------------------------------------------------------
-- Raw terms
------------------------------------------------------------------------

import Level
open import Universe

module README.DependentlyTyped.Raw-term
  {Uni₀ : Universe Level.zero Level.zero}
  where

open import Data.Nat
open import Data.Product as Prod
import README.DependentlyTyped.Term

open README.DependentlyTyped.Term Uni₀

-- Two kinds of raw terms: checkable and inferrable.

data Kind : Set where
  chk inf : Kind

mutual

  infixl 9 _·_
  infix  5 _∶_

  -- Raw types.

  data Ty : Set where
    ⋆  : Ty
    el : (t : Term inf) → Ty
    π  : (t₁ t₂ : Ty) → Ty

  -- Raw terms.

  data Term : Kind → Set where
    var : (x : ℕ) → Term inf
    ƛ   : (t : Term chk) → Term chk
    _·_ : (t₁ : Term inf) (t₂ : Term chk) → Term inf

    -- Inferrable terms can be checked.
    inf : (t : Term inf) → Term chk

    -- Type annotation.
    _∶_ : (t : Term chk) (σ : Ty) → Term inf

-- Turns arbitrary raw terms into checkable ones.

checkable : ∃ Term → Term chk
checkable (inf , t) = inf t
checkable (chk , t) = t

-- Turns arbitrary raw terms into inferrable ones, given a potential
-- type annotation.

inferrable : ∃ Term → Ty → Term inf
inferrable (inf , t) _ = t
inferrable (chk , t) σ = t ∶ σ

-- The context position corresponding to a variable.

position : ∀ {Γ σ} → Γ ∋ σ → ℕ
position zero    = zero
position (suc x) = suc (position x)

mutual

  -- Well-typed terms can be turned into raw ones.
  --
  -- (As long as they do not involve applications of checkable terms…)

  ⌊_⌋ty : ∀ {Γ σ} → Γ ⊢ σ type → Ty
  ⌊ ⋆       ⌋ty = ⋆
  ⌊ el t    ⌋ty = el (inferrable ⌊ t ⌋ ⋆)
  ⌊ π σ′ τ′ ⌋ty = π ⌊ σ′ ⌋ty ⌊ τ′ ⌋ty

  ⌊_⌋ : ∀ {Γ σ} → Γ ⊢ σ → ∃ Term
  ⌊ var x   ⌋ = inf , var (position x)
  ⌊ ƛ t     ⌋ = , ƛ (checkable ⌊ t ⌋)
  ⌊ t₁ · t₂ ⌋ = , inferrable ⌊ t₁ ⌋ {!!} · checkable ⌊ t₂ ⌋
