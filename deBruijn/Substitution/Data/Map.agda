------------------------------------------------------------------------
-- Map for substitutions
------------------------------------------------------------------------

{-# OPTIONS --universe-polymorphism #-}

import deBruijn.TermLike as TermLike
open import Universe

module deBruijn.Substitution.Data.Map
  {u e} {Uni : Universe u e}
  where

import deBruijn.Context as Context
open import deBruijn.Substitution.Data.Basics
open import Function using (_$_)
import Relation.Binary.PropositionalEquality as P

open Context Uni
open P.≡-Reasoning
open TermLike Uni

private
 module Dummy
   {t₁} {T₁ : Term-like t₁}
   {t₂} {T₂ : Term-like t₂}
   where

  open Term-like T₁ using () renaming (_⊢_ to _⊢₁_; _≅-⊢_ to _≅-⊢₁_)
  open Term-like T₂ using ([_]) renaming (_≅-⊢_ to _≅-⊢₂_)

  -- Map.

  map : ∀ {Γ Δ Ε} {ρ̂₁ : Γ ⇨̂ Δ} {ρ̂₂ : Δ ⇨̂ Ε} →
        [ T₁ ⟶ T₂ ] ρ̂₂ → Sub T₁ ρ̂₁ → Sub T₂ (ρ̂₁ ∘̂ ρ̂₂)
  map           f ε        = ε
  map {ρ̂₂ = ρ̂₂} f (ρ₁ ▻ t) =
    P.subst (λ v → Sub T₂ (⟦ ρ₁ ⟧⇨ ∘̂ ρ̂₂ ▻̂ v))
            (≅-Value-⇒-≡ $ P.sym $ corresponds f t)
            (map f ρ₁ ▻ f · t)

  abstract

    -- An unfolding lemma.

    map-▻ :
      ∀ {Γ Δ Ε} {ρ̂₁ : Γ ⇨̂ Δ} {ρ̂₂ : Δ ⇨̂ Ε} {σ}
      (f : [ T₁ ⟶ T₂ ] ρ̂₂) (ρ : Sub T₁ ρ̂₁) t →
      map f (ρ ▻⇨[ σ ] t) ≅-⇨ map f ρ ▻⇨[ σ ] f · t
    map-▻ {ρ̂₂ = ρ̂₂} f ρ t =
      drop-subst-Sub (λ v → ⟦ ρ ⟧⇨ ∘̂ ρ̂₂ ▻̂ v)
                     (≅-Value-⇒-≡ $ P.sym $ corresponds f t)

  -- A congruence lemma.

  map-cong : ∀ {Γ₁ Δ₁ Ε₁} {ρ̂₁₁ : Γ₁ ⇨̂ Δ₁} {ρ̂₂₁ : Δ₁ ⇨̂ Ε₁}
               {f₁ : [ T₁ ⟶ T₂ ] ρ̂₂₁} {ρ₁ : Sub T₁ ρ̂₁₁}
               {Γ₂ Δ₂ Ε₂} {ρ̂₁₂ : Γ₂ ⇨̂ Δ₂} {ρ̂₂₂ : Δ₂ ⇨̂ Ε₂}
               {f₂ : [ T₁ ⟶ T₂ ] ρ̂₂₂} {ρ₂ : Sub T₁ ρ̂₁₂} →
             f₁ ≅-⟶ f₂ → ρ₁ ≅-⇨ ρ₂ → map f₁ ρ₁ ≅-⇨ map f₂ ρ₂
  map-cong P.refl P.refl = P.refl

  abstract

    -- Variants which only require that the functions are
    -- extensionally equal.

    map-cong-ext₁ : ∀ {Γ₁ Δ Ε₁} {ρ̂₁₁ : Γ₁ ⇨̂ Δ} {ρ̂₂₁ : Δ ⇨̂ Ε₁}
                      {f₁ : [ T₁ ⟶ T₂ ] ρ̂₂₁} {ρ₁ : Sub T₁ ρ̂₁₁}
                      {Γ₂   Ε₂} {ρ̂₁₂ : Γ₂ ⇨̂ Δ} {ρ̂₂₂ : Δ ⇨̂ Ε₂}
                      {f₂ : [ T₁ ⟶ T₂ ] ρ̂₂₂} {ρ₂ : Sub T₁ ρ̂₁₂} →
                    Ε₁ ≅-Ctxt Ε₂ →
                    (∀ {σ} (t : Δ ⊢₁ σ) → f₁ · t ≅-⊢₂ f₂ · t) →
                    ρ₁ ≅-⇨ ρ₂ → map f₁ ρ₁ ≅-⇨ map f₂ ρ₂
    map-cong-ext₁ {Δ = Δ} {f₁ = f₁} {f₂ = f₂} {ρ₂ = ρ}
                  Ε₁≅Ε₂ f₁≅f₂ P.refl = helper ρ
      where
      helper : ∀ {Γ} {ρ̂ : Γ ⇨̂ Δ} (ρ : Sub T₁ ρ̂) → map f₁ ρ ≅-⇨ map f₂ ρ
      helper ε       = ε⇨-cong Ε₁≅Ε₂
      helper (ρ ▻ t) = begin
        [ map f₁ (ρ ▻ t)    ]  ≡⟨ map-▻ f₁ ρ t ⟩
        [ map f₁ ρ ▻ f₁ · t ]  ≡⟨ ▻⇨-cong P.refl (helper ρ) (f₁≅f₂ t) ⟩
        [ map f₂ ρ ▻ f₂ · t ]  ≡⟨ P.sym $ map-▻ f₂ ρ t ⟩
        [ map f₂ (ρ ▻ t)    ]  ∎

    map-cong-ext₂ : ∀ {Γ₁ Δ₁ Ε₁} {ρ̂₁₁ : Γ₁ ⇨̂ Δ₁} {ρ̂₂₁ : Δ₁ ⇨̂ Ε₁}
                      {f₁ : [ T₁ ⟶ T₂ ] ρ̂₂₁} {ρ₁ : Sub T₁ ρ̂₁₁}
                      {Γ₂ Δ₂ Ε₂} {ρ̂₁₂ : Γ₂ ⇨̂ Δ₂} {ρ̂₂₂ : Δ₂ ⇨̂ Ε₂}
                      {f₂ : [ T₁ ⟶ T₂ ] ρ̂₂₂} {ρ₂ : Sub T₁ ρ̂₁₂} →
                    Δ₁ ≅-Ctxt Δ₂ → Ε₁ ≅-Ctxt Ε₂ →
                    (∀ {σ₁ σ₂} {t₁ : Δ₁ ⊢₁ σ₁} {t₂ : Δ₂ ⊢₁ σ₂} →
                       t₁ ≅-⊢₁ t₂ → f₁ · t₁ ≅-⊢₂ f₂ · t₂) →
                    ρ₁ ≅-⇨ ρ₂ → map f₁ ρ₁ ≅-⇨ map f₂ ρ₂
    map-cong-ext₂ P.refl Ε₁≅Ε₂ f₁≅f₂ ρ₁≅ρ₂ =
      map-cong-ext₁ Ε₁≅Ε₂
                    (λ t → f₁≅f₂ (P.refl {x = Term-like.[_] t}))
                    ρ₁≅ρ₂

    private

      -- A helper lemma.

      /∋-map-▻ :
        ∀ {Γ Δ Ε σ τ} {ρ̂₁ : Γ ⇨̂ Δ} {ρ̂₂ : Δ ⇨̂ Ε} {t} →
        (x : Γ ▻ σ ∋ τ) (f : [ T₁ ⟶ T₂ ] ρ̂₂) (ρ : Sub T₁ ρ̂₁) →
        x /∋ map f (ρ ▻ t) ≅-⊢₂ x /∋ (map f ρ ▻ f · t)
      /∋-map-▻ {t = t} x f ρ =
        /∋-cong (P.refl {x = [ x ]}) (map-▻ f ρ t)

    -- Some sort of naturality statement for _/∋_.

    /∋-map : ∀ {Γ Δ Ε σ} {ρ̂₁ : Γ ⇨̂ Δ} {ρ̂₂ : Δ ⇨̂ Ε} →
             (x : Γ ∋ σ) (f : [ T₁ ⟶ T₂ ] ρ̂₂) (ρ : Sub T₁ ρ̂₁) →
             x /∋ map f ρ ≅-⊢₂ f · (x /∋ ρ)
    /∋-map (zero {σ = σ}) f (ρ ▻ t) = begin
      [ zero[ σ ] /∋ map f (ρ ▻ t)     ]  ≡⟨ /∋-map-▻ zero[ σ ] f ρ ⟩
      [ zero[ σ ] /∋ (map f ρ ▻ f · t) ]  ≡⟨ P.refl ⟩
      [ f · t                          ]  ∎
    /∋-map (suc {σ = σ} x) f (ρ ▻ t) = begin
      [ suc      x /∋ map f (ρ ▻ t)     ]  ≡⟨ /∋-map-▻ (suc x) f ρ ⟩
      [ suc[ σ ] x /∋ (map f ρ ▻ f · t) ]  ≡⟨ P.refl ⟩
      [ x /∋ map f ρ                    ]  ≡⟨ /∋-map x f ρ ⟩
      [ f · (x /∋ ρ)                    ]  ∎

open Dummy public

abstract

  -- Map is functorial.

  map-[id] : ∀ {t} {T : Term-like t} {Γ Δ} {ρ̂ : Γ ⇨̂ Δ}
             (ρ : Sub T ρ̂) → map ([id] {T = T}) ρ ≅-⇨ ρ
  map-[id] ε       = P.refl
  map-[id] (ρ ▻ t) = ▻⇨-cong P.refl (map-[id] ρ) P.refl

  map-[∘] :
    ∀ {t₁} {T₁ : Term-like t₁}
      {t₂} {T₂ : Term-like t₂}
      {t₃} {T₃ : Term-like t₃}
      {Γ Δ Ε Ζ} {ρ̂₁ : Γ ⇨̂ Δ} {ρ̂₂ : Δ ⇨̂ Ε} {ρ̂₃ : Ε ⇨̂ Ζ}
    (f₂ : [ T₂ ⟶ T₃ ] ρ̂₃) (f₁ : [ T₁ ⟶ T₂ ] ρ̂₂)
    (ρ : Sub T₁ ρ̂₁) →
    map (f₂ [∘] f₁) ρ ≅-⇨ map f₂ (map f₁ ρ)
  map-[∘] f₂ f₁ ε       = P.refl
  map-[∘] f₂ f₁ (ρ ▻ t) = begin
    [ map (f₂ [∘] f₁) (ρ ▻ t)           ]  ≡⟨ map-▻ (f₂ [∘] f₁) ρ t ⟩
    [ map (f₂ [∘] f₁) ρ ▻ f₂ · (f₁ · t) ]  ≡⟨ ▻⇨-cong P.refl (map-[∘] f₂ f₁ ρ) P.refl ⟩
    [ map f₂ (map f₁ ρ) ▻ f₂ · (f₁ · t) ]  ≡⟨ P.sym $ map-▻ f₂ (map f₁ ρ) (f₁ · t) ⟩
    [ map f₂ (map f₁ ρ ▻ f₁ · t)        ]  ≡⟨ map-cong (P.refl {x = [ f₂ ]}) (P.sym $ map-▻ f₁ ρ t) ⟩
    [ map f₂ (map f₁ (ρ ▻ t))           ]  ∎
