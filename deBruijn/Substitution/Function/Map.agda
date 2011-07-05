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
open import deBruijn.Substitution.Function.Basics
open import Function using (_$_)
open import Level using (_⊔_)
import Relation.Binary.PropositionalEquality as P

open Context Uni
open TermLike Uni

private
 module Dummy
   {t₁} {T₁ : Term-like t₁}
   {t₂} {T₂ : Term-like t₂}
   where

  open Term-like T₁ using ()
                    renaming (_⊢_ to _⊢₁_; _≅-⊢_ to _≅-⊢₁_; [_] to [_]₁)
  open Term-like T₂ using () renaming (_≅-⊢_ to _≅-⊢₂_)

  -- Map.

  map : ∀ {Γ Δ Ε} {ρ̂₁ : Γ ⇨̂ Δ} {ρ̂₂ : Δ ⇨̂ Ε} →
        [ T₁ ⟶ T₂ ] ρ̂₂ → (ρ₁ : Sub T₁ ρ̂₁) → Sub T₂ (ρ̂₁ ∘̂ ρ̂₂)
  map f ρ₁ = f [∘] ρ₁

  abstract

    -- An unfolding lemma.

    map-▻ :
      P.Extensionality (u ⊔ e) (u ⊔ e ⊔ t₂) →
      ∀ {Γ Δ Ε} {ρ̂₁ : Γ ⇨̂ Δ} {ρ̂₂ : Δ ⇨̂ Ε} {σ}
      (f : [ T₁ ⟶ T₂ ] ρ̂₂) (ρ : Sub T₁ ρ̂₁) t →
      map f (ρ ▻⇨[ σ ] t) ≅-⇨ map f ρ ▻⇨[ σ ] f · t
    map-▻ ext {Γ} {σ = σ} f ρ t = extensionality ext P.refl lemma
      where
      lemma : ∀ {τ} (x : Γ ▻ σ ∋ τ) →
              f · (x /∋ (ρ ▻⇨ t)) ≅-⊢₂ x /∋ (map f ρ ▻⇨ f · t)
      lemma zero    = P.refl
      lemma (suc x) = P.refl

  -- A congruence lemma.

  map-cong : ∀ {Γ₁ Δ₁ Ε₁} {ρ̂₁₁ : Γ₁ ⇨̂ Δ₁} {ρ̂₂₁ : Δ₁ ⇨̂ Ε₁}
               {f₁ : [ T₁ ⟶ T₂ ] ρ̂₂₁} {ρ₁ : Sub T₁ ρ̂₁₁}
               {Γ₂ Δ₂ Ε₂} {ρ̂₁₂ : Γ₂ ⇨̂ Δ₂} {ρ̂₂₂ : Δ₂ ⇨̂ Ε₂}
               {f₂ : [ T₁ ⟶ T₂ ] ρ̂₂₂} {ρ₂ : Sub T₁ ρ̂₁₂} →
             f₁ ≅-⟶ f₂ → ρ₁ ≅-⇨ ρ₂ → map f₁ ρ₁ ≅-⇨ map f₂ ρ₂
  map-cong {f₁ = _ , _} {ρ₁ = _ , _} {f₂ = ._ , _} {ρ₂ = ._ , _}
           [ P.refl ] [ P.refl ] = [ P.refl ]

  abstract

    -- Variants which only require that the functions are
    -- extensionally equal.

    map-cong-ext₁ : P.Extensionality (u ⊔ e) (u ⊔ e ⊔ t₂) →
                    ∀ {Γ₁ Δ Ε₁} {ρ̂₁₁ : Γ₁ ⇨̂ Δ} {ρ̂₂₁ : Δ ⇨̂ Ε₁}
                      {f₁ : [ T₁ ⟶ T₂ ] ρ̂₂₁} {ρ₁ : Sub T₁ ρ̂₁₁}
                      {Γ₂   Ε₂} {ρ̂₁₂ : Γ₂ ⇨̂ Δ} {ρ̂₂₂ : Δ ⇨̂ Ε₂}
                      {f₂ : [ T₁ ⟶ T₂ ] ρ̂₂₂} {ρ₂ : Sub T₁ ρ̂₁₂} →
                    Ε₁ ≅-Ctxt Ε₂ →
                    (∀ {σ} (t : Δ ⊢₁ σ) → f₁ · t ≅-⊢₂ f₂ · t) →
                    ρ₁ ≅-⇨ ρ₂ → map f₁ ρ₁ ≅-⇨ map f₂ ρ₂
    map-cong-ext₁ ext {ρ₁ = ρ} {ρ₂ = ._ , _} Ε₁≅Ε₂ f₁≅f₂ [ P.refl ] =
      extensionality ext Ε₁≅Ε₂ (λ x → f₁≅f₂ (x /∋ ρ))

    map-cong-ext₂ : P.Extensionality (u ⊔ e) (u ⊔ e ⊔ t₂) →
                    ∀ {Γ₁ Δ₁ Ε₁} {ρ̂₁₁ : Γ₁ ⇨̂ Δ₁} {ρ̂₂₁ : Δ₁ ⇨̂ Ε₁}
                      {f₁ : [ T₁ ⟶ T₂ ] ρ̂₂₁} {ρ₁ : Sub T₁ ρ̂₁₁}
                      {Γ₂ Δ₂ Ε₂} {ρ̂₁₂ : Γ₂ ⇨̂ Δ₂} {ρ̂₂₂ : Δ₂ ⇨̂ Ε₂}
                      {f₂ : [ T₁ ⟶ T₂ ] ρ̂₂₂} {ρ₂ : Sub T₁ ρ̂₁₂} →
                    Δ₁ ≅-Ctxt Δ₂ → Ε₁ ≅-Ctxt Ε₂ →
                    (∀ {σ₁ σ₂} {t₁ : Δ₁ ⊢₁ σ₁} {t₂ : Δ₂ ⊢₁ σ₂} →
                       t₁ ≅-⊢₁ t₂ → f₁ · t₁ ≅-⊢₂ f₂ · t₂) →
                    ρ₁ ≅-⇨ ρ₂ → map f₁ ρ₁ ≅-⇨ map f₂ ρ₂
    map-cong-ext₂ ext P.refl Ε₁≅Ε₂ f₁≅f₂ ρ₁≅ρ₂ =
      map-cong-ext₁ ext Ε₁≅Ε₂ (λ t → f₁≅f₂ (P.refl {x = [ t ]₁})) ρ₁≅ρ₂

  -- Some sort of naturality statement for _/∋_. (Note that this lemma
  -- holds definitionally. This is not the case for the corresponding
  -- lemma in deBruijn.Substitution.Data.Map.)

  /∋-map : ∀ {Γ Δ Ε σ} {ρ̂₁ : Γ ⇨̂ Δ} {ρ̂₂ : Δ ⇨̂ Ε} →
           (x : Γ ∋ σ) (f : [ T₁ ⟶ T₂ ] ρ̂₂) (ρ : Sub T₁ ρ̂₁) →
           x /∋ map f ρ ≅-⊢₂ f · (x /∋ ρ)
  /∋-map x f ρ = P.refl

open Dummy public

-- Map is functorial.

map-[id] : ∀ {t} {T : Term-like t} {Γ Δ} {ρ̂ : Γ ⇨̂ Δ}
           (ρ : Sub T ρ̂) →
           map ([id] {T = T}) ρ ≅-⇨ ρ
map-[id] = [id]-[∘]

map-[∘] :
  ∀ {t₁} {T₁ : Term-like t₁}
    {t₂} {T₂ : Term-like t₂}
    {t₃} {T₃ : Term-like t₃}
    {Γ Δ Ε Ζ} {ρ̂₁ : Γ ⇨̂ Δ} {ρ̂₂ : Δ ⇨̂ Ε} {ρ̂₃ : Ε ⇨̂ Ζ}
  (f₂ : [ T₂ ⟶ T₃ ] ρ̂₃) (f₁ : [ T₁ ⟶ T₂ ] ρ̂₂)
  (ρ : Sub T₁ ρ̂₁) →
  map (f₂ [∘] f₁) ρ ≅-⇨ map f₂ (map f₁ ρ)
map-[∘] f₂ f₁ ρ = sym-⟶ $ [∘]-[∘] f₂ f₁ ρ
