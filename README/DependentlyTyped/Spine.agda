------------------------------------------------------------------------
-- Spines
------------------------------------------------------------------------

open import Level using (zero)
open import Universe

module README.DependentlyTyped.Spine (Uni₀ : Universe zero zero) where

import README.DependentlyTyped.Term as Term
import README.DependentlyTyped.Substitution as Substitution
open Term Uni₀
open Substitution Uni₀

open import Data.Product renaming (curry to c; uncurry to uc)
open import Function renaming (const to k)
open import Relation.Binary.HeterogeneousEquality as H using (_≅_)
open import Relation.Binary.PropositionalEquality as P using (_≡_)

open Tm-subst

-- A type which represents the "spine" of a (syntactic) type.

data Spine : Set where
  ⋆ el : Spine
  π    : (sp₁ sp₂ : Spine) → Spine

-- The spine of a type.

spine : ∀ {Γ σ} → Γ ⊢ σ type → Spine
spine ⋆         = ⋆
spine (el t)    = el
spine (π σ′ τ′) = π (spine σ′) (spine τ′)

-- Some simple lemmas.

spine-cong : ∀ {Γ₁ σ₁} {σ′₁ : Γ₁ ⊢ σ₁ type}
               {Γ₂ σ₂} {σ′₂ : Γ₂ ⊢ σ₂ type} →
             Γ₁ ≡ Γ₂ → σ₁ ≅ σ₂ → σ′₁ ≅ σ′₂ → spine σ′₁ ≡ spine σ′₂
spine-cong P.refl H.refl H.refl = P.refl

fst-cong : ∀ {sp₁₁ sp₂₁ sp₁₂ sp₂₂} →
           Spine.π sp₁₁ sp₂₁ ≡ π sp₁₂ sp₂₂ → sp₁₁ ≡ sp₁₂
fst-cong P.refl = P.refl

snd-cong : ∀ {sp₁₁ sp₂₁ sp₁₂ sp₂₂} →
           Spine.π sp₁₁ sp₂₁ ≡ π sp₁₂ sp₂₂ → sp₂₁ ≡ sp₂₂
snd-cong P.refl = P.refl

abstract

  -- Application of a substitution does not affect a type's spine.

  spine-preserved : ∀ {Γ Δ σ} (σ′ : Γ ⊢ σ type) (ρ : Γ ⇨ Δ) →
                    spine (σ′ /⊢t ρ) ≡ spine σ′
  spine-preserved ⋆      ρ = P.refl
  spine-preserved (el t) ρ = begin
    spine (P.subst (λ v → _ ⊢ k U.el ˢ v type)
                   (P.sym $ t /⊢-lemma ρ)
                   (el (t /⊢ ρ)))               ≡⟨ spine-cong P.refl
                                                              (H.≡-to-≅ $ P.cong (λ v → k U.el ˢ v) $ t /⊢-lemma ρ)
                                                              (H.≡-subst-removable (λ v → _ ⊢ k U.el ˢ v type)
                                                                                   (P.sym $ t /⊢-lemma ρ) _) ⟩
    spine (el (t /⊢ ρ))                         ≡⟨ P.refl ⟩
    el                                          ∎
    where open P.≡-Reasoning
  spine-preserved (π {σ = σ} {τ = τ} σ′ τ′) ρ = begin
    spine (P.subst (λ ρ′ → _ ⊢ k U.π ˢ (σ / ρ) ˢ c (τ /̂ ρ′) type)
                   (P.sym $ ρ ↑-lemma)
                   (π (σ′ /⊢t ρ) (τ′ /⊢t ρ ↑)))                    ≡⟨ spine-cong P.refl
                                                                                 (H.≡-to-≅ $
                                                                                    P.cong (λ ρ′ → k U.π ˢ (σ / ρ) ˢ c (τ /̂ ρ′))
                                                                                           (ρ ↑-lemma))
                                                                                 (H.≡-subst-removable
                                                                                    (λ ρ′ → _ ⊢ k U.π ˢ (σ / ρ) ˢ c (τ /̂ ρ′) type)
                                                                                    (P.sym $ ρ ↑-lemma) _) ⟩
    spine (π (σ′ /⊢t ρ) (τ′ /⊢t ρ ↑))                              ≡⟨ P.refl ⟩
    π (spine (σ′ /⊢t ρ)) (spine (τ′ /⊢t ρ ↑))                      ≡⟨ P.cong₂ π (spine-preserved σ′ ρ) (spine-preserved τ′ (ρ ↑)) ⟩
    π (spine σ′) (spine τ′)                                        ∎
    where open P.≡-Reasoning
