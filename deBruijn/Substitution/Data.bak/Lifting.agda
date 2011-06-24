------------------------------------------------------------------------
-- Liftings
------------------------------------------------------------------------

{-# OPTIONS --universe-polymorphism #-}

open import Universe

module deBruijn.Substitution.Data.Lifting
  {u e} (Uni : Universe u e)
  where

import deBruijn.Context as Context
import deBruijn.Substitution.Basics as Basics
import deBruijn.Substitution.Map as Map
import deBruijn.Substitution.Simple
open import Level using (_⊔_)
open import Relation.Binary.HeterogeneousEquality as H using (_≅_)
open import Relation.Binary.PropositionalEquality as P using (_≡_)

open Context Uni
open deBruijn.Substitution.Simple Uni

------------------------------------------------------------------------
-- Liftings

record Lifting {t₁} (T₁ : Term-like t₁)
               {t₂} (T₂ : Term-like t₂) :
               Set (u ⊔ e ⊔ t₁ ⊔ t₂) where

  open Term-like T₁ renaming (_⊢_ to _⊢₁_; ⟦_⟧ to ⟦_⟧₁)
  open Term-like T₂ renaming (_⊢_ to _⊢₂_; ⟦_⟧ to ⟦_⟧₂)
  -- T₂ is listed before T₁ below due to a bug in the Agda system.
  open Basics T₂ renaming (_⇨_ to _⇨₂_; ⟦_⟧⇨ to ⟦_⟧₂⇨; _/∋_ to _/∋₂_)
  open Basics T₁ renaming (_⇨_ to _⇨₁_; ⟦_⟧⇨ to ⟦_⟧₁⇨; _/∋_ to _/∋₁_)
  open Map T₁ T₂

  field
    -- Simple substitutions for the first kind of terms.
    simple₁ : Simple T₁

    -- Transforms the first kind of terms to the second.
    lift       : ∀ {Γ σ} → Γ ⊢₁ σ → Γ ⊢₂ σ
    lift-lemma : ∀ {Γ σ} (t : Γ ⊢₁ σ) → ⟦ t ⟧₁ ≡ ⟦ lift t ⟧₂

  -- Transforms substitutions.

  lift⇨ : ∀ {Γ Δ} → Γ ⇨₁ Δ → Γ ⇨₂ Δ
  lift⇨ = map (record { function = lift; preserves = lift-lemma })

  abstract

    lift⇨-lemma : ∀ {Γ Δ} (ρ : Γ ⇨₁ Δ) → ⟦ lift⇨ ρ ⟧₂⇨ ≡ ⟦ ρ ⟧₁⇨
    lift⇨-lemma = map-lemma _

    -- lift(⇨) commutes with /∋.

    /∋-lift⇨ : ∀ {Γ Δ σ} (x : Γ ∋ σ) (ρ : Γ ⇨₁ Δ) →
               x /∋₂ lift⇨ ρ ≅ lift (x /∋₁ ρ)
    /∋-lift⇨ x ρ = /∋-map x _ ρ

  -- A congruence lemma.

  lift-cong : ∀ {Γ₁ σ₁} {t₁ : Γ₁ ⊢₁ σ₁}
                {Γ₂ σ₂} {t₂ : Γ₂ ⊢₁ σ₂} →
              Γ₁ ≡ Γ₂ → σ₁ ≅ σ₂ → t₁ ≅ t₂ → lift t₁ ≅ lift t₂
  lift-cong P.refl H.refl H.refl = H.refl

  abstract

    -- A simple consequence of _/∋-lemma_.

    ⟦⟧-lift-/∋ : ∀ {Γ Δ σ} (x : Γ ∋ σ) (ρ : Γ ⇨₁ Δ) →
                 x /̂∋ ⟦ ρ ⟧₁⇨ ≡ ⟦ lift (x /∋₁ ρ) ⟧₂
    ⟦⟧-lift-/∋ x ρ = begin
      x /̂∋ ⟦ ρ ⟧₁⇨         ≡⟨ Basics._/∋-lemma_ T₁ x ρ ⟩
      ⟦ x /∋₁ ρ ⟧₁         ≡⟨ lift-lemma (x /∋₁ ρ) ⟩
      ⟦ lift (x /∋₁ ρ) ⟧₂  ∎
      where open P.≡-Reasoning

  open Simple simple₁ public
