------------------------------------------------------------------------
-- Map for substitutions
------------------------------------------------------------------------

{-# OPTIONS --universe-polymorphism #-}

import deBruijn.TermLike as TermLike
open import Universe

module deBruijn.Substitution.Function.Map
  {u e} {Uni : Universe u e}
  where

import deBruijn.Context as Context
import deBruijn.Substitution.Function.Basics as Basics
open import Function using (_$_)
open import Level using (_⊔_)
open import Relation.Binary.HeterogeneousEquality as H using (_≅_)
open import Relation.Binary.PropositionalEquality as P using (_≡_)

open Context Uni
open TermLike Uni

private
 module Dummy
   {t₁} {T₁ : Term-like t₁}
   {t₂} {T₂ : Term-like t₂}
   where

  open Basics T₁ renaming (Sub to Sub₁; _/∋_ to _/∋₁_)
  open Basics T₂ renaming (Sub to Sub₂; _/∋_ to _/∋₂_)

  -- Map.

  map : ∀ {Γ Δ Ε} {ρ̂₁ : Γ ⇨̂ Δ} {ρ̂₂ : Δ ⇨̂ Ε} →
        [ T₁ ⟶ T₂ ] ρ̂₂ → (ρ₁ : Sub₁ ρ̂₁) → Sub₂ (ρ̂₁ ∘̂ ρ̂₂)
  map f ρ₁ = f [∘] ρ₁

  -- A congruence lemma.

  map-cong : ∀ {Γ₁ Δ₁ Ε₁} {ρ̂₁₁ : Γ₁ ⇨̂ Δ₁} {ρ̂₂₁ : Δ₁ ⇨̂ Ε₁}
               {f₁ : [ T₁ ⟶ T₂ ] ρ̂₂₁} {ρ₁ : Sub₁ ρ̂₁₁}
               {Γ₂ Δ₂ Ε₂} {ρ̂₁₂ : Γ₂ ⇨̂ Δ₂} {ρ̂₂₂ : Δ₂ ⇨̂ Ε₂}
               {f₂ : [ T₁ ⟶ T₂ ] ρ̂₂₂} {ρ₂ : Sub₁ ρ̂₁₂} →
             Γ₁ ≡ Γ₂ → Δ₁ ≡ Δ₂ → Ε₁ ≡ Ε₂ → ρ̂₁₁ ≅ ρ̂₁₂ → ρ̂₂₁ ≅ ρ̂₂₂ →
             f₁ ≅ f₂ → ρ₁ ≅ ρ₂ → map f₁ ρ₁ ≅ map f₂ ρ₂
  map-cong P.refl P.refl P.refl H.refl H.refl H.refl H.refl = H.refl

  -- Some sort of naturality statement for _/∋_. (Note that this lemma
  -- holds definitionally.)

  /∋-map : ∀ {Γ Δ Ε σ} {ρ̂₁ : Γ ⇨̂ Δ} {ρ̂₂ : Δ ⇨̂ Ε} →
           (x : Γ ∋ σ) (f : [ T₁ ⟶ T₂ ] ρ̂₂) (ρ : Sub₁ ρ̂₁) →
           x /∋₂ map f ρ ≡ f · (x /∋₁ ρ)
  /∋-map x f ρ = P.refl

open Dummy public

-- Map is functorial (assuming extensionality).

abstract

  map-[id] : P.Extensionality (e ⊔ u) (e ⊔ u) →
             ∀ {t} {T : Term-like t} {Γ Δ} {ρ̂ : Γ ⇨̂ Δ}
             (ρ : Basics.Sub T ρ̂) →
             map ([id] {T = T}) ρ ≡ ρ
  map-[id] ext ρ = [id]-[∘] ext ρ

  map-[∘] :
    P.Extensionality (e ⊔ u) (e ⊔ u) →
    ∀ {t₁} {T₁ : Term-like t₁}
      {t₂} {T₂ : Term-like t₂}
      {t₃} {T₃ : Term-like t₃}
      {Γ Δ Ε Ζ} {ρ̂₁ : Γ ⇨̂ Δ} {ρ̂₂ : Δ ⇨̂ Ε} {ρ̂₃ : Ε ⇨̂ Ζ}
    (f₂ : [ T₂ ⟶ T₃ ] ρ̂₃) (f₁ : [ T₁ ⟶ T₂ ] ρ̂₂)
    (ρ : Basics.Sub T₁ ρ̂₁) →
    map (f₂ [∘] f₁) ρ ≡ map f₂ (map f₁ ρ)
  map-[∘] ext f₂ f₁ ρ = P.sym $ [∘]-[∘] ext f₂ f₁ ρ
