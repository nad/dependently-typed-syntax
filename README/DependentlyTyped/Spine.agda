------------------------------------------------------------------------
-- Spines
------------------------------------------------------------------------

{-# OPTIONS --universe-polymorphism #-}

import Level
open import Universe

module README.DependentlyTyped.Spine
  {Uni₀ : Universe Level.zero Level.zero}
  where

open import Data.Product
open import deBruijn.Substitution.Data
open import README.DependentlyTyped.Substitution
import README.DependentlyTyped.Term as Term; open Term Uni₀
open import Relation.Binary.PropositionalEquality as P using (_≡_)

open P.≡-Reasoning

-- A type which represents the "spine" of a type.

data Spine : Set where
  ⋆ el : Spine
  π    : (sp₁ sp₂ : Spine) → Spine

-- The spine of a syntactic type.

spine : ∀ {Γ σ} → Γ ⊢ σ type → Spine
spine ⋆         = ⋆
spine (el t)    = el
spine (π σ′ τ′) = π (spine σ′) (spine τ′)

-- A spine together with a proof showing that it is the spine of a
-- given syntactic type.

Spine-of : ∀ {Γ σ} → Γ ⊢ σ type → Set _
Spine-of σ′ = ∃ λ (sp : Spine) → spine σ′ ≡ sp

-- A congruence lemma.

spine-cong : ∀ {Γ₁ σ₁} {σ′₁ : Γ₁ ⊢ σ₁ type}
               {Γ₂ σ₂} {σ′₂ : Γ₂ ⊢ σ₂ type} →
             σ′₁ ≅-type σ′₂ → spine σ′₁ ≡ spine σ′₂
spine-cong P.refl = P.refl

abstract

  -- Application of a substitution does not affect a type's spine.

  spine-preserved : ∀ {Γ Δ σ} {ρ̂ : Γ ⇨̂ Δ}
                    (σ′ : Γ ⊢ σ type) (ρ : Sub Tm ρ̂) →
                    spine (σ′ /⊢t ρ) ≡ spine σ′
  spine-preserved ⋆      ρ = P.refl
  spine-preserved (el t) ρ = begin
    spine (el t /⊢t ρ)   ≡⟨ spine-cong (el-/⊢t t ρ) ⟩
    spine (el (t /⊢ ρ))  ≡⟨ P.refl ⟩
    el                   ∎
  spine-preserved (π σ′ τ′) ρ = begin
    π (spine (σ′ /⊢t ρ)) (spine (τ′ /⊢t ρ ↑))  ≡⟨ P.cong₂ π (spine-preserved σ′ ρ) (spine-preserved τ′ (ρ ↑)) ⟩
    π (spine σ′) (spine τ′)                    ∎

-- Substitutions can be applied to Spine-of.

infixl 8 _/Spine-of_

_/Spine-of_ : ∀ {Γ Δ σ} {ρ̂ : Γ ⇨̂ Δ} {σ′ : Γ ⊢ σ type} →
              Spine-of σ′ → (ρ : Sub Tm ρ̂) → Spine-of (σ′ /⊢t ρ)
_/Spine-of_ {σ′ = σ′} (sp , eq) ρ = sp , (begin
  spine (σ′ /⊢t ρ)  ≡⟨ spine-preserved σ′ ρ ⟩
  spine σ′          ≡⟨ eq ⟩
  sp                ∎)

-- A syntactic type matching the semantic type, and a corresponding
-- spine.

infix 4 _⊢_⟨spine⟩

_⊢_⟨spine⟩ : (Γ : Ctxt) → Type Γ → Set _
Γ ⊢ σ ⟨spine⟩ = ∃₂ λ (σ′ : Γ ⊢ σ type) (sp : Spine) → spine σ′ ≡ sp

-- Substitutions can be applied to the contraptions of the previous
-- definition.

infixl 8 _/⟨spine⟩_

_/⟨spine⟩_ : ∀ {Γ Δ σ} {ρ̂ : Γ ⇨̂ Δ} →
             Γ ⊢ σ ⟨spine⟩ → (ρ : Sub Tm ρ̂) → Δ ⊢ σ / ρ ⟨spine⟩
(σ′ , spine-of) /⟨spine⟩ ρ = σ′ /⊢t ρ , spine-of /Spine-of ρ
