------------------------------------------------------------------------
-- Normal and neutral terms
------------------------------------------------------------------------

open import Level using (zero)
open import Universe

module README.DependentlyTyped.NormalForm
  (Uni₀ : Universe zero zero) where

open import Data.Product as Prod renaming (curry to c; uncurry to uc)
open import Function hiding (_∋_) renaming (const to k; _∘_ to _⊚_)
import README.DependentlyTyped.Term as Term; open Term Uni₀
import Relation.Binary.PropositionalEquality as P

-- Atomic types (types for which the normaliser does not do
-- η-expansion).

data _⊢_atomic-type (Γ : Ctxt) : Type Γ → Set where
  ⋆  : ∀ {σ} → Γ ⊢ ⋆  , σ atomic-type
  el : ∀ {σ} → Γ ⊢ el , σ atomic-type

-- Two kinds: normal and neutral.

data Kind : Set where
  no ne : Kind

mutual

  -- Γ ⊢ σ ⟨ no ⟩ represents η-long, β-normal terms, Γ ⊢ σ ⟨ ne ⟩
  -- represents neutral terms.

  infixl 9 _·_
  infix  4 _⊢_⟨_⟩

  data _⊢_⟨_⟩ (Γ : Ctxt) : Type Γ → Kind → Set where
    ne  : ∀ {σ} (σ′ : Γ ⊢ σ atomic-type) (t : Γ ⊢ σ ⟨ ne ⟩) →
          Γ ⊢ σ ⟨ no ⟩
    var : ∀ {σ} (x : Γ ∋ σ) → Γ ⊢ σ ⟨ ne ⟩
    ƛ   : ∀ {σ τ} (t : Γ ▻ σ ⊢ τ ⟨ no ⟩) → Γ ⊢ Type-π σ τ ⟨ no ⟩
    _·_ : ∀ {sp₁ sp₂ σ}
          (t₁ : Γ ⊢ π sp₁ sp₂ , σ ⟨ ne ⟩) (t₂ : Γ ⊢ fst σ ⟨ no ⟩) →
          Γ ⊢ snd σ /̂ ŝub ⟦ ⌊ t₂ ⌋ ⟧ ⟨ ne ⟩

  -- Normal and neutral terms can be turned into ordinary terms.

  ⌊_⌋ : ∀ {Γ σ k} → Γ ⊢ σ ⟨ k ⟩ → Γ ⊢ σ
  ⌊ ne σ′ t ⌋ = ⌊ t ⌋
  ⌊ var x   ⌋ = var x
  ⌊ ƛ t     ⌋ = ƛ ⌊ t ⌋
  ⌊ t₁ · t₂ ⌋ = ⌊ t₁ ⌋ · ⌊ t₂ ⌋

-- Normal and neutral terms are "term-like".

Tm-n : Kind → Term-like _
Tm-n k = record { _⊢_ = λ Γ σ → Γ ⊢ σ ⟨ k ⟩; ⟦_⟧ = ⟦_⟧ ⊚ ⌊_⌋ }

private
  open module T {k} = Term-like (Tm-n k) public
    using ([_])
    renaming ( ⟦_⟧ to ⟦_⟧n; _≅-⊢_ to _≅-⊢n_
             ; drop-subst-⊢ to drop-subst-⊢n; ⟦⟧-cong to ⟦⟧n-cong
             )

-- As mentioned above normal and neutral terms can be turned into
-- ordinary terms.

forget-n : ∀ {k} → [ Tm-n k ⟶⁼ Tm ]
forget-n = record
  { function    = λ _ → ⌊_⌋
  ; corresponds = λ _ _ → P.refl
  }

-- Various congruences.

ne-cong : ∀ {Γ σ} {σ′ : Γ ⊢ σ atomic-type}
            {t₁ t₂ : Γ ⊢ σ ⟨ ne ⟩} →
          t₁ ≅-⊢n t₂ → ne σ′ t₁ ≅-⊢n ne σ′ t₂
ne-cong P.refl = P.refl

var-n-cong : ∀ {Γ₁ σ₁} {x₁ : Γ₁ ∋ σ₁}
               {Γ₂ σ₂} {x₂ : Γ₂ ∋ σ₂} →
             x₁ ≅-∋ x₂ → var x₁ ≅-⊢n var x₂
var-n-cong P.refl = P.refl

ƛn-cong : ∀ {Γ₁ σ₁ τ₁} {t₁ : Γ₁ ▻ σ₁ ⊢ τ₁ ⟨ no ⟩}
            {Γ₂ σ₂ τ₂} {t₂ : Γ₂ ▻ σ₂ ⊢ τ₂ ⟨ no ⟩} →
          t₁ ≅-⊢n t₂ → ƛ t₁ ≅-⊢n ƛ t₂
ƛn-cong P.refl = P.refl

·n-cong :
  ∀ {Γ₁ sp₁₁ sp₂₁ σ₁}
    {t₁₁ : Γ₁ ⊢ π sp₁₁ sp₂₁ , σ₁ ⟨ ne ⟩} {t₂₁ : Γ₁ ⊢ fst σ₁ ⟨ no ⟩}
    {Γ₂ sp₁₂ sp₂₂ σ₂}
    {t₁₂ : Γ₂ ⊢ π sp₁₂ sp₂₂ , σ₂ ⟨ ne ⟩} {t₂₂ : Γ₂ ⊢ fst σ₂ ⟨ no ⟩} →
    t₁₁ ≅-⊢n t₁₂ → t₂₁ ≅-⊢n t₂₂ → t₁₁ · t₂₁ ≅-⊢n t₁₂ · t₂₂
·n-cong P.refl P.refl = P.refl
