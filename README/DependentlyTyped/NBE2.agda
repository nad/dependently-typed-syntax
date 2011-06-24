------------------------------------------------------------------------
-- Normalisation by evaluation
------------------------------------------------------------------------

{-# OPTIONS --no-positivity-check #-}

open import Level using (zero)
open import Universe

module README.DependentlyTyped.NBE2 (Uni₀ : Universe zero zero) where

import README.DependentlyTyped.Term as Term
import README.DependentlyTyped.Substitution as Substitution
import README.DependentlyTyped.NormalForm as NormalForm
open Term Uni₀
open Substitution Uni₀
open NormalForm Uni₀

open import Data.Product renaming (curry to c; uncurry to uc)
import deBruijn.Substitution; open deBruijn.Substitution Uni
open import Function hiding (id) renaming (_∘_ to _⊚_; const to k)
import Relation.Binary.HeterogeneousEquality as H
import Relation.Binary.PropositionalEquality as P

open Tm-subst

mutual

  data Kripke-val Γ : Type Γ → Set where
    ⋆  : (t : Γ ⊢ k U.⋆ [ ne ]) → Kripke-val Γ (k ⋆)
    el : {t′ : Γ ⊢ k ⋆} (t : Γ ⊢ k U.el ˢ ⟦ t′ ⟧ [ ne ]) →
         Kripke-val Γ (k U.el ˢ ⟦ t′ ⟧)
    π  : ∀ {σ τ}
         (f : (Γ⁺ : Ctxt⁺ Γ)
              (v : Kripke-val (Γ ++ Γ⁺) (σ /̂ ŵk⋆ Γ⁺)) →
              Kripke-val (Γ ++ Γ⁺) (uc τ /̂ ŵk⋆ Γ⁺ ↑̂ ⊚ ŝub Kripke-⟦ v ⟧)) →
         Kripke-val Γ (k U.π ˢ σ ˢ τ)

  Kripke-⟦_⟧ : ∀ {Γ σ} → Kripke-val Γ σ → Value Γ σ
  Kripke-⟦ ⋆ t  ⟧ = ⟦ ⌊ t ⌋ ⟧
  Kripke-⟦ el t ⟧ = ⟦ ⌊ t ⌋ ⟧
  Kripke-⟦ π f  ⟧ = λ γ v → {!f ε!}

  foo : ∀ {Γ σ} → Value Γ σ → Kripke-val Γ σ
  foo v = {!!}

-- P.subst (λ v → uc τ /̂ ŝub v) Kripke-⟦ f ε {!v!} ⟧ γ
