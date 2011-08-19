------------------------------------------------------------------------
-- Lemmas related to application of substitutions
------------------------------------------------------------------------

{-# OPTIONS --universe-polymorphism #-}

open import Universe

module deBruijn.Substitution.Data.Application.Application22
  {i u e} {Uni : Indexed-universe i u e}
  where

import deBruijn.Context as Context
open import deBruijn.Substitution.Data.Application.Application21
open import deBruijn.Substitution.Data.Application.Application222
open import deBruijn.Substitution.Data.Basics
open import deBruijn.Substitution.Data.Simple
import deBruijn.TermLike as TermLike
open import Level using (_⊔_)

open Context Uni
open TermLike Uni

-- Lemmas related to application.
--
-- In order to lessen the performance problems which—at the time of
-- writing—plague Agda this module has been split into two,
-- Application221 and Application222.

record Application₂₂
  {t₁} {T₁ : Term-like t₁}
  {t₂} {T₂ : Term-like t₂}

  -- Simple substitutions for the first kind of terms.
  (simple₁ : Simple T₁)

  -- Simple substitutions for the second kind of terms.
  (simple₂ : Simple T₂)

  -- A translation from the first to the second kind of terms.
  (trans : [ T₁ ⟶⁼ T₂ ])
  : Set (i ⊔ u ⊔ e ⊔ t₁ ⊔ t₂) where

  open Term-like T₂ renaming (_⊢_ to _⊢₂_; _≅-⊢_ to _≅-⊢₂_)
  open Simple simple₁
    using () renaming (wk[_] to wk₁[_]; _↑⁺⋆_ to _↑⁺⋆₁_)
  open Simple simple₂
    using () renaming (var to var₂; weaken[_] to weaken₂[_])

  field
    application₂₁ : Application₂₁ simple₁ simple₂ trans

  open Application₂₁ application₂₁

  field
    -- Lifts equalities valid for all variables and liftings to
    -- arbitrary terms.
    var-/⊢⋆-↑⁺⋆-⇒-/⊢⋆-↑⁺⋆ :
      ∀ {Γ Δ} {ρ̂ : Γ ⇨̂ Δ} (ρs₁ : Subs T₁ ρ̂) (ρs₂ : Subs T₁ ρ̂) →
      (∀ Γ⁺ {σ} (x : Γ ++⁺ Γ⁺ ∋ σ) →
         var₂ · x /⊢⋆ ρs₁ ↑⁺⋆₁ Γ⁺ ≅-⊢₂ var₂ · x /⊢⋆ ρs₂ ↑⁺⋆₁ Γ⁺) →
      ∀ Γ⁺ {σ} (t : Γ ++⁺ Γ⁺ ⊢₂ σ) →
      t /⊢⋆ ρs₁ ↑⁺⋆₁ Γ⁺ ≅-⊢₂ t /⊢⋆ ρs₂ ↑⁺⋆₁ Γ⁺

    -- The wk substitution and the weaken function are equivalent.
    /⊢-wk : ∀ {Γ σ τ} (t : Γ ⊢₂ τ) →
            t /⊢ wk₁[ σ ] ≅-⊢₂ weaken₂[ σ ] · t

  open Application₂₂₂
    (record { application₂₂₁ = record
              { application₂₁         = application₂₁
              ; var-/⊢⋆-↑⁺⋆-⇒-/⊢⋆-↑⁺⋆ = var-/⊢⋆-↑⁺⋆-⇒-/⊢⋆-↑⁺⋆
              ; /⊢-wk                 = /⊢-wk
              }
            }) public
    hiding (application₂₁; var-/⊢⋆-↑⁺⋆-⇒-/⊢⋆-↑⁺⋆; /⊢-wk)
