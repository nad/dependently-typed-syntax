------------------------------------------------------------------------
-- Normal and neutral terms
------------------------------------------------------------------------

open import Level using (zero)
open import Universe

module README.DependentlyTyped.NormalForm
  {Uni₀ : Universe zero zero} where

open import Data.Product as Prod renaming (curry to c; uncurry to uc)
import deBruijn.TermLike as TermLike
open import Function renaming (const to k; _∘_ to _⊚_)
import README.DependentlyTyped.Term as Term; open Term Uni₀
import Relation.Binary.PropositionalEquality as P

open TermLike Uni hiding (_·_)

-- Atomic types (types for which the normaliser does not do
-- η-expansion).

data _⊢_atomic-type (Γ : Ctxt) : Type Γ → Set where
  ⋆  : Γ ⊢ , k ⋆ atomic-type
  el : (t : Γ ⊢ , k ⋆) → Γ ⊢ , k U.el ˢ ⟦ t ⟧ atomic-type

-- Two kinds: normal and neutral.

data Kind : Set where
  no ne : Kind

mutual

  -- Γ ⊢ σ ⟨ no ⟩ represents η-long, β-normal terms, Γ ⊢ σ ⟨ ne ⟩
  -- represents neutral terms.

  infix 4 _⊢_⟨_⟩

  data _⊢_⟨_⟩ (Γ : Ctxt) : Type Γ → Kind → Set where
    ne  : ∀ {σ} (σ′ : Γ ⊢ σ atomic-type) (t : Γ ⊢ σ ⟨ ne ⟩) →
          Γ ⊢ σ ⟨ no ⟩
    var : ∀ {σ} (x : Γ ∋ σ) → Γ ⊢ σ ⟨ ne ⟩
    ƛ   : ∀ {σ τ} (σ′ : Γ ⊢ σ type) (t : Γ ▻ σ ⊢ τ ⟨ no ⟩) →
          Γ ⊢ , k U.π ˢ indexed-type σ ˢ c (indexed-type τ) ⟨ no ⟩
    _·_ : ∀ {σ τ}
          (t₁ : Γ ⊢ , k U.π ˢ indexed-type σ ˢ proj₂ τ ⟨ ne ⟩)
          (t₂ : Γ ⊢ σ ⟨ no ⟩) →
          Γ ⊢ Prod.map id uc τ /̂ ŝub ⟦ ⌊ t₂ ⌋ ⟧ ⟨ ne ⟩

  -- Normal and neutral terms can be turned into ordinary terms.

  ⌊_⌋ : ∀ {Γ σ k} → Γ ⊢ σ ⟨ k ⟩ → Γ ⊢ σ
  ⌊ ne σ′ t ⌋ = ⌊ t ⌋
  ⌊ var x   ⌋ = var x
  ⌊ ƛ σ′ t  ⌋ = ƛ σ′ ⌊ t ⌋
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

ƛn-cong : ∀ {Γ₁ σ₁ τ₁} {σ′₁ : Γ₁ ⊢ σ₁ type} {t₁ : Γ₁ ▻ σ₁ ⊢ τ₁ ⟨ no ⟩}
            {Γ₂ σ₂ τ₂} {σ′₂ : Γ₂ ⊢ σ₂ type} {t₂ : Γ₂ ▻ σ₂ ⊢ τ₂ ⟨ no ⟩} →
          σ′₁ ≅-type σ′₂ → t₁ ≅-⊢n t₂ → ƛ σ′₁ t₁ ≅-⊢n ƛ σ′₂ t₂
ƛn-cong P.refl P.refl = P.refl

·n-cong :
  ∀ {Γ σ τ} {t₂₁ t₂₂ : Γ ⊢ σ ⟨ no ⟩}
    {t₁₁ t₁₂ : Γ ⊢ , k U.π ˢ indexed-type σ
                           ˢ c (indexed-type τ) ⟨ ne ⟩} →
  t₁₁ ≅-⊢n t₁₂ → t₂₁ ≅-⊢n t₂₂ → t₁₁ · t₂₁ ≅-⊢n t₁₂ · t₂₂
·n-cong P.refl P.refl = P.refl
