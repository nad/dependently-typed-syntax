------------------------------------------------------------------------
-- The type of every closed term exists in syntactic form
------------------------------------------------------------------------

-- If we assume that equality of functions is extensional.

import Level
open import Relation.Binary.PropositionalEquality as P using (_≡_; _≢_)
open import Universe

module README.DependentlyTyped.TypeOf
  {Uni₀ : Universe Level.zero Level.zero}
  (ext : P.Extensionality Level.zero Level.zero)
  where

open import Data.Empty
open import Data.Product renaming (uncurry to uc)
open import Function renaming (const to k)
open import README.DependentlyTyped.Substitution
import README.DependentlyTyped.Term as Term; open Term Uni₀

-- We can project out the second component of a syntactic Π-type.

snd : ∀ {Γ σ τ} → Γ ⊢ k U.π ˢ σ ˢ τ type → Γ ▻ σ ⊢ uc τ type
snd πστ = snd′ πστ P.refl
  where
  ⋆≢π : ∀ {a b} → U.⋆ ≢ U.π a b
  ⋆≢π ()

  el≢π : ∀ {a b c} → U.el a ≢ U.π b c
  el≢π ()

  fst-cong : ∀ {a₁ b₁ a₂ b₂} → U.π a₁ b₁ ≡ U.π a₂ b₂ → a₁ ≡ a₂
  fst-cong P.refl = P.refl

  snd-cong : ∀ {a b₁ b₂} → U.π a b₁ ≡ U.π a b₂ → b₁ ≡ b₂
  snd-cong P.refl = P.refl

  snd′ : ∀ {Γ σ τ υ} →
         Γ ⊢ υ type → υ ≡ k U.π ˢ σ ˢ τ → Γ ▻ σ ⊢ uc τ type
  snd′ {Γ} {σ} ⋆ eq =
    P.subst (λ υ → Γ ▻ σ ⊢ υ type)
            (ext λ γ → ⊥-elim $ ⋆≢π $ P.cong (λ f → f (proj₁ γ)) eq)
            ⋆

  snd′ {Γ} {σ} (el t) eq =
    P.subst (λ υ → Γ ▻ σ ⊢ υ type)
            (ext λ γ → ⊥-elim $ el≢π $ P.cong (λ f → f (proj₁ γ)) eq)
            (el (t /⊢ wk))

  snd′ {τ = τ₁} (π σ′ τ′) eq
    with ext λ γ → fst-cong $ P.cong (λ f → f γ) eq
  snd′ {τ = τ₁} (π σ′ τ′) eq | P.refl
    with ext {g = uc τ₁} λ γ →
           P.cong (λ f → f (proj₂ γ)) $
             snd-cong $ P.cong (λ f → f (proj₁ γ)) eq
  snd′ (π σ′ τ′) eq | P.refl | P.refl = τ′

-- A term's syntactic type.
--
-- This is a sanity check: every term which can be constructed has a
-- type which can be constructed (assuming that all types in the
-- context can be constructed, and assuming that equality of functions
-- is extensional).

type-of : ∀ {Γ τ} → Γ ⊢ τ → (∀ {σ} → Γ ∋ σ → Γ ⊢ σ type) → Γ ⊢ τ type
type-of     (var x)          hyp = hyp x
type-of     (t₁ · t₂)        hyp = snd (type-of t₁ hyp) /⊢t sub t₂
type-of {Γ} (ƛ {σ = σ} σ′ t) hyp = π σ′ (type-of t hyp′)
  where
  hyp′ : ∀ {τ} → Γ ▻ σ ∋ τ → Γ ▻ σ ⊢ τ type
  hyp′ zero    = σ′    /⊢t wk
  hyp′ (suc x) = hyp x /⊢t wk
