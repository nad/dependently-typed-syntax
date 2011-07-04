------------------------------------------------------------------------
-- Application of substitutions
------------------------------------------------------------------------

{-# OPTIONS --universe-polymorphism #-}

open import Universe

module deBruijn.Substitution.Data.Application.Application
  {u e} {Uni : Universe u e} where

import deBruijn.Context as Context
open import deBruijn.Substitution.Data.Basics
open import deBruijn.Substitution.Data.Map
import deBruijn.TermLike as TermLike
open import Level using (_⊔_)
import Relation.Binary.PropositionalEquality as P

open Context Uni
open TermLike Uni

-- Given an operation which applies substitutions to terms one can
-- define composition of substitutions.

record Application
  {t₁} (T₁ : Term-like t₁)
  {t₂} (T₂ : Term-like t₂) :
  Set (u ⊔ e ⊔ t₁ ⊔ t₂) where

  open Term-like T₂ renaming (_⊢_ to _⊢₂_; _≅-⊢_ to _≅-⊢₂_)

  field
    -- Application of substitutions to terms.
    app : ∀ {Γ Δ} {ρ̂ : Γ ⇨̂ Δ} → Sub T₁ ρ̂ → [ T₂ ⟶ T₂ ] ρ̂

  -- Post-application of substitutions to terms.

  infixl 8 _/⊢_

  _/⊢_ : ∀ {Γ Δ σ} {ρ̂ : Γ ⇨̂ Δ} → Γ ⊢₂ σ → Sub T₁ ρ̂ → Δ ⊢₂ σ /̂ ρ̂
  t /⊢ ρ = app ρ · t

  -- Reverse composition. (Fits well with post-application.)

  infixl 9 _∘_

  _∘_ : ∀ {Γ Δ Ε} {ρ̂₁ : Γ ⇨̂ Δ} {ρ̂₂ : Δ ⇨̂ Ε} →
        Sub T₂ ρ̂₁ → Sub T₁ ρ̂₂ → Sub T₂ (ρ̂₁ ∘̂ ρ̂₂)
  ρ₁ ∘ ρ₂ = map (app ρ₂) ρ₁

  -- Application of multiple substitutions to terms.

  app⋆ : ∀ {Γ Δ} {ρ̂ : Γ ⇨̂ Δ} → Subs T₁ ρ̂ → [ T₂ ⟶ T₂ ] ρ̂
  app⋆ = fold [ T₂ ⟶ T₂ ] [id] (λ f ρ → app ρ [∘] f)

  infixl 8 _/⊢⋆_

  _/⊢⋆_ : ∀ {Γ Δ σ} {ρ̂ : Γ ⇨̂ Δ} → Γ ⊢₂ σ → Subs T₁ ρ̂ → Δ ⊢₂ σ /̂ ρ̂
  t /⊢⋆ ρs = app⋆ ρs · t

  -- Some congruence lemmas.

  app-cong : ∀ {Γ₁ Δ₁} {ρ̂₁ : Γ₁ ⇨̂ Δ₁} {ρ₁ : Sub T₁ ρ̂₁}
               {Γ₂ Δ₂} {ρ̂₂ : Γ₂ ⇨̂ Δ₂} {ρ₂ : Sub T₁ ρ̂₂} →
             ρ₁ ≅-⇨ ρ₂ → app ρ₁ ≅-⟶ app ρ₂
  app-cong P.refl = [ P.refl ]

  /⊢-cong :
    ∀ {Γ₁ Δ₁ σ₁} {t₁ : Γ₁ ⊢₂ σ₁} {ρ̂₁ : Γ₁ ⇨̂ Δ₁} {ρ₁ : Sub T₁ ρ̂₁}
      {Γ₂ Δ₂ σ₂} {t₂ : Γ₂ ⊢₂ σ₂} {ρ̂₂ : Γ₂ ⇨̂ Δ₂} {ρ₂ : Sub T₁ ρ̂₂} →
    t₁ ≅-⊢₂ t₂ → ρ₁ ≅-⇨ ρ₂ → t₁ /⊢ ρ₁ ≅-⊢₂ t₂ /⊢ ρ₂
  /⊢-cong P.refl P.refl = P.refl

  ∘-cong :
    ∀ {Γ₁ Δ₁ Ε₁} {ρ̂₁₁ : Γ₁ ⇨̂ Δ₁} {ρ̂₂₁ : Δ₁ ⇨̂ Ε₁}
      {ρ₁₁ : Sub T₂ ρ̂₁₁} {ρ₂₁ : Sub T₁ ρ̂₂₁}
      {Γ₂ Δ₂ Ε₂} {ρ̂₁₂ : Γ₂ ⇨̂ Δ₂} {ρ̂₂₂ : Δ₂ ⇨̂ Ε₂}
      {ρ₁₂ : Sub T₂ ρ̂₁₂} {ρ₂₂ : Sub T₁ ρ̂₂₂} →
    ρ₁₁ ≅-⇨ ρ₁₂ → ρ₂₁ ≅-⇨ ρ₂₂ → ρ₁₁ ∘ ρ₂₁ ≅-⇨ ρ₁₂ ∘ ρ₂₂
  ∘-cong P.refl P.refl = P.refl

  app⋆-cong : ∀ {Γ₁ Δ₁} {ρ̂₁ : Γ₁ ⇨̂ Δ₁} {ρs₁ : Subs T₁ ρ̂₁}
                {Γ₂ Δ₂} {ρ̂₂ : Γ₂ ⇨̂ Δ₂} {ρs₂ : Subs T₁ ρ̂₂} →
              ρs₁ ≅-⇨⋆ ρs₂ → app⋆ ρs₁ ≅-⟶ app⋆ ρs₂
  app⋆-cong P.refl = [ P.refl ]

  /⊢⋆-cong :
    ∀ {Γ₁ Δ₁ σ₁} {t₁ : Γ₁ ⊢₂ σ₁} {ρ̂₁ : Γ₁ ⇨̂ Δ₁} {ρs₁ : Subs T₁ ρ̂₁}
      {Γ₂ Δ₂ σ₂} {t₂ : Γ₂ ⊢₂ σ₂} {ρ̂₂ : Γ₂ ⇨̂ Δ₂} {ρs₂ : Subs T₁ ρ̂₂} →
    t₁ ≅-⊢₂ t₂ → ρs₁ ≅-⇨⋆ ρs₂ → t₁ /⊢⋆ ρs₁ ≅-⊢₂ t₂ /⊢⋆ ρs₂
  /⊢⋆-cong P.refl P.refl = P.refl

  abstract

    -- An unfolding lemma.

    ▻-∘ : ∀ {Γ Δ Ε} {ρ̂₁ : Γ ⇨̂ Δ} {ρ̂₂ : Δ ⇨̂ Ε} {σ}
          (ρ₁ : Sub T₂ ρ̂₁) (t : Δ ⊢₂ σ / ρ₁) (ρ₂ : Sub T₁ ρ̂₂) →
          (ρ₁ ▻⇨[ σ ] t) ∘ ρ₂ ≅-⇨ ρ₁ ∘ ρ₂ ▻⇨[ σ ] t /⊢ ρ₂
    ▻-∘ ρ₁ t ρ₂ = map-▻ (app ρ₂) ρ₁ t

    -- Applying a composed substitution to a variable is equivalent to
    -- applying one substitution and then the other.

    /∋-∘ : ∀ {Γ Δ Ε σ} {ρ̂₁ : Γ ⇨̂ Δ} {ρ̂₂ : Δ ⇨̂ Ε}
           (x : Γ ∋ σ) (ρ₁ : Sub T₂ ρ̂₁) (ρ₂ : Sub T₁ ρ̂₂) →
           x /∋ ρ₁ ∘ ρ₂ ≅-⊢₂ x /∋ ρ₁ /⊢ ρ₂
    /∋-∘ x ρ₁ ρ₂ = /∋-map x (app ρ₂) ρ₁
