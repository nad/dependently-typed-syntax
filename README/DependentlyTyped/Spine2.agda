------------------------------------------------------------------------
-- Spines
------------------------------------------------------------------------

open import Level using (zero)
open import Universe

module README.DependentlyTyped.Spine2 (Uni₀ : Universe zero zero) where

import README.DependentlyTyped.Term as Term; open Term Uni₀

open import Data.Product renaming (curry to c)
open import Function renaming (const to k)
open import Relation.Binary.HeterogeneousEquality as H using (_≅_)
open import Relation.Binary.PropositionalEquality as P using (_≡_)

-- A type which represents the "spine" of a (semantic) type.

-- TODO: Rename this type.

data Spine (Γ : Ctxt) : Type Γ → Set where
  ⋆  : Spine Γ (k U.⋆)
  el : (σ₀ : Env Γ → U₀) → Spine Γ (k U.el ˢ σ₀)
  π  : ∀ {σ τ} (σ′ : Spine Γ σ) (τ′ : Spine (Γ ▻ σ) τ) →
       Spine Γ (k U.π ˢ σ ˢ c τ)

-- The spine of a syntactic type's semantic type.

spine : ∀ {Γ σ} → Γ ⊢ σ type → Spine Γ σ
spine ⋆         = ⋆
spine (el t)    = el ⟦ t ⟧
spine (π σ′ τ′) = π (spine σ′) (spine τ′)

-- Applies a context morphism to a spine.

infix 8 _/Spine_

_/Spine_ : ∀ {Γ Δ σ} → Spine Γ σ → (ρ : Γ ⇨̂ Δ) → Spine Δ (σ /̂ ρ)
⋆       /Spine ρ = ⋆
el σ₀    /Spine ρ = el (σ₀ ∘ ρ)
π σ′ τ′ /Spine ρ = π (σ′ /Spine ρ) (τ′ /Spine ρ ↑̂)

-- Some simple lemmas.

spine-cong : ∀ {Γ₁ σ₁} {σ′₁ : Γ₁ ⊢ σ₁ type}
               {Γ₂ σ₂} {σ′₂ : Γ₂ ⊢ σ₂ type} →
             Γ₁ ≡ Γ₂ → σ₁ ≅ σ₂ → σ′₁ ≅ σ′₂ → spine σ′₁ ≅ spine σ′₂
spine-cong P.refl H.refl H.refl = H.refl

fst-cong : ∀ {Γ₁ σ₁ τ₁} {σ′₁ : Spine Γ₁ σ₁} {τ′₁ : Spine (Γ₁ ▻ σ₁) τ₁}
             {Γ₂ σ₂ τ₂} {σ′₂ : Spine Γ₂ σ₂} {τ′₂ : Spine (Γ₂ ▻ σ₂) τ₂} →
           Γ₁ ≡ Γ₂ → σ₁ ≅ σ₂ → τ₁ ≅ τ₂ →
           Spine.π σ′₁ τ′₁ ≅ Spine.π σ′₂ τ′₂ → σ′₁ ≅ σ′₂
fst-cong P.refl H.refl H.refl H.refl = H.refl

snd-cong : ∀ {Γ₁ σ₁ τ₁} {σ′₁ : Spine Γ₁ σ₁} {τ′₁ : Spine (Γ₁ ▻ σ₁) τ₁}
             {Γ₂ σ₂ τ₂} {σ′₂ : Spine Γ₂ σ₂} {τ′₂ : Spine (Γ₂ ▻ σ₂) τ₂} →
           Γ₁ ≡ Γ₂ → σ₁ ≅ σ₂ → τ₁ ≅ τ₂ →
           Spine.π σ′₁ τ′₁ ≅ Spine.π σ′₂ τ′₂ → τ′₁ ≅ τ′₂
snd-cong P.refl H.refl H.refl H.refl = H.refl
