------------------------------------------------------------------------
-- Raw terms
------------------------------------------------------------------------

import Level
open import Data.Universe

module README.DependentlyTyped.Raw-term
  (Uni₀ : Universe Level.zero Level.zero)
  where

open import Data.Nat
import README.DependentlyTyped.Term as Term; open Term Uni₀
open import Relation.Binary.PropositionalEquality as P using (_≡_)

mutual

  infixl 9 _·_
  infix  5 _∶_

  -- Raw types.

  data Raw-ty : Set where
    ⋆  : Raw-ty
    el : (t : Raw) → Raw-ty
    π  : (t₁ t₂ : Raw-ty) → Raw-ty

  -- Raw terms.
  --
  -- One could distinguish between "checkable" and "inferrable" terms,
  -- but without a corresponding split for the well-typed terms this
  -- seems awkward.

  data Raw : Set where
    var : (x : ℕ) → Raw
    ƛ   : (t : Raw) → Raw
    _·_ : (t₁ t₂ : Raw) → Raw

    -- Type annotation.
    _∶_ : (t : Raw) (σ : Raw-ty) → Raw

-- The context position corresponding to a variable.

position : ∀ {Γ σ} → Γ ∋ σ → ℕ
position zero    = zero
position (suc x) = suc (position x)

-- Well-typed terms can be turned into raw ones.

⌊_⌋ : ∀ {Γ σ} → Γ ⊢ σ → Raw
⌊ var x   ⌋ = var (position x)
⌊ ƛ t     ⌋ = ƛ ⌊ t ⌋
⌊ t₁ · t₂ ⌋ = ⌊ t₁ ⌋ · ⌊ t₂ ⌋

-- The same applies to syntactic types.

⌊_⌋ty : ∀ {Γ σ} → Γ ⊢ σ type → Raw-ty
⌊ ⋆       ⌋ty = ⋆
⌊ el t    ⌋ty = el ⌊ t ⌋
⌊ π σ′ τ′ ⌋ty = π ⌊ σ′ ⌋ty ⌊ τ′ ⌋ty

mutual

  -- The following functions remove type-annotations.

  ⌊_⌋raw-ty : Raw-ty → Raw-ty
  ⌊ ⋆       ⌋raw-ty = ⋆
  ⌊ el t    ⌋raw-ty = el ⌊ t ⌋raw
  ⌊ π t₁ t₂ ⌋raw-ty = π ⌊ t₁ ⌋raw-ty ⌊ t₂ ⌋raw-ty

  ⌊_⌋raw : Raw → Raw
  ⌊ var x   ⌋raw = var x
  ⌊ ƛ t     ⌋raw = ƛ ⌊ t ⌋raw
  ⌊ t₁ · t₂ ⌋raw = ⌊ t₁ ⌋raw · ⌊ t₂ ⌋raw
  ⌊ t ∶ σ   ⌋raw = ⌊ t ⌋raw

-- Some congruence lemmas.

position-cong : ∀ {Γ₁ σ₁} {x₁ : Γ₁ ∋ σ₁}
                  {Γ₂ σ₂} {x₂ : Γ₂ ∋ σ₂} →
                x₁ ≅-∋ x₂ → position x₁ ≡ position x₂
position-cong P.refl = P.refl

⌊⌋-cong : ∀ {Γ₁ σ₁} {t₁ : Γ₁ ⊢ σ₁}
            {Γ₂ σ₂} {t₂ : Γ₂ ⊢ σ₂} →
          t₁ ≅-⊢ t₂ → ⌊ t₁ ⌋ ≡ ⌊ t₂ ⌋
⌊⌋-cong P.refl = P.refl

⌊⌋ty-cong : ∀ {Γ₁ σ₁} {σ′₁ : Γ₁ ⊢ σ₁ type}
              {Γ₂ σ₂} {σ′₂ : Γ₂ ⊢ σ₂ type} →
            σ′₁ ≅-type σ′₂ → ⌊ σ′₁ ⌋ty ≡ ⌊ σ′₂ ⌋ty
⌊⌋ty-cong P.refl = P.refl
