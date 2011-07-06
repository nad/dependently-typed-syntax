------------------------------------------------------------------------
-- The type of every closed term exists in syntactic form
------------------------------------------------------------------------

import Level
open import Universe

module README.DependentlyTyped.TypeOf
  {Uni₀ : Universe Level.zero Level.zero} where

import README.DependentlyTyped.Term as Term; open Term Uni₀
open import README.DependentlyTyped.Term.Substitution

-- A term's syntactic type.
--
-- This is a sanity check: every term which can be constructed has a
-- type which can be constructed (assuming that all types in the
-- context can be constructed).

type-of : ∀ {Γ τ} → Γ ⊢ τ → (∀ {σ} → Γ ∋ σ → Γ ⊢ σ type) → Γ ⊢ τ type
type-of     (var x)          hyp = hyp x
type-of     (t₁ · t₂)        hyp = snd′ (type-of t₁ hyp) /⊢t sub t₂
type-of {Γ} (ƛ {σ = σ} σ′ t) hyp = π σ′ (type-of t hyp′)
  where
  hyp′ : ∀ {τ} → Γ ▻ σ ∋ τ → Γ ▻ σ ⊢ τ type
  hyp′ zero    = σ′    /⊢t wk
  hyp′ (suc x) = hyp x /⊢t wk
