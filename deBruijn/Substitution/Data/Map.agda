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
open import Relation.Binary.HeterogeneousEquality as H using (_≅_)
open import Relation.Binary.PropositionalEquality as P using (_≡_)

open Context Uni
open TermLike Uni

private
 module Dummy
   {t₁} {T₁ : Term-like t₁}
   {t₂} {T₂ : Term-like t₂}
   where

  open Term-like T₁ using () renaming (_⊢_ to _⊢₁_)

  -- Map.

  map : ∀ {Γ Δ Ε} {ρ̂₁ : Γ ⇨̂ Δ} {ρ̂₂ : Δ ⇨̂ Ε} →
        [ T₁ ⟶ T₂ ] ρ̂₂ → Sub T₁ ρ̂₁ → Sub T₂ (ρ̂₁ ∘̂ ρ̂₂)
  map           f ε        = ε
  map {ρ̂₂ = ρ̂₂} f (ρ₁ ▻ t) =
    P.subst (λ v → Sub T₂ (⟦ ρ₁ ⟧⇨ ∘̂ ρ̂₂ ▻̂ v))
            (P.sym $ corresponds f t)
            (map f ρ₁ ▻ f · t)

  abstract

    -- An unfolding lemma.

    map-▻ :
      ∀ {Γ Δ Ε} {ρ̂₁ : Γ ⇨̂ Δ} {ρ̂₂ : Δ ⇨̂ Ε} {σ}
      (f : [ T₁ ⟶ T₂ ] ρ̂₂) (ρ : Sub T₁ ρ̂₁) t →
      map f (_▻_ {σ = σ} ρ t) ≅ Sub._▻_ {σ = σ} (map f ρ) (f · t)
    map-▻ {ρ̂₂ = ρ̂₂} f ρ t =
      H.≡-subst-removable (λ v → Sub T₂ (⟦ ρ ⟧⇨ ∘̂ ρ̂₂ ▻̂ v))
                          (P.sym $ corresponds f t) _

  -- A congruence lemma.

  map-cong : ∀ {Γ₁ Δ₁ Ε₁} {ρ̂₁₁ : Γ₁ ⇨̂ Δ₁} {ρ̂₂₁ : Δ₁ ⇨̂ Ε₁}
               {f₁ : [ T₁ ⟶ T₂ ] ρ̂₂₁} {ρ₁ : Sub T₁ ρ̂₁₁}
               {Γ₂ Δ₂ Ε₂} {ρ̂₁₂ : Γ₂ ⇨̂ Δ₂} {ρ̂₂₂ : Δ₂ ⇨̂ Ε₂}
               {f₂ : [ T₁ ⟶ T₂ ] ρ̂₂₂} {ρ₂ : Sub T₁ ρ̂₁₂} →
             Γ₁ ≡ Γ₂ → Δ₁ ≡ Δ₂ → Ε₁ ≡ Ε₂ → ρ̂₁₁ ≅ ρ̂₁₂ → ρ̂₂₁ ≅ ρ̂₂₂ →
             f₁ ≅ f₂ → ρ₁ ≅ ρ₂ → map f₁ ρ₁ ≅ map f₂ ρ₂
  map-cong P.refl P.refl P.refl H.refl H.refl H.refl H.refl = H.refl

  abstract

    -- Variants which only require that the functions are
    -- extensionally equal.

    map-cong-ext₁ : ∀ {Γ₁ Δ Ε₁} {ρ̂₁₁ : Γ₁ ⇨̂ Δ} {ρ̂₂₁ : Δ ⇨̂ Ε₁}
                      {f₁ : [ T₁ ⟶ T₂ ] ρ̂₂₁} {ρ₁ : Sub T₁ ρ̂₁₁}
                      {Γ₂   Ε₂} {ρ̂₁₂ : Γ₂ ⇨̂ Δ} {ρ̂₂₂ : Δ ⇨̂ Ε₂}
                      {f₂ : [ T₁ ⟶ T₂ ] ρ̂₂₂} {ρ₂ : Sub T₁ ρ̂₁₂} →
                    Γ₁ ≡ Γ₂ → Ε₁ ≡ Ε₂ → ρ̂₁₁ ≅ ρ̂₁₂ → ρ̂₂₁ ≅ ρ̂₂₂ →
                    (∀ {σ} (t : Δ ⊢₁ σ) → f₁ · t ≅ f₂ · t) →
                    ρ₁ ≅ ρ₂ → map f₁ ρ₁ ≅ map f₂ ρ₂
    map-cong-ext₁ {Δ = Δ} {f₁ = f₁} {f₂ = f₂} {ρ₂ = ρ}
                  P.refl P.refl H.refl H.refl f₁≅f₂ H.refl = helper ρ
      where
      open H.≅-Reasoning

      helper : ∀ {Γ} {ρ̂ : Γ ⇨̂ Δ} (ρ : Sub T₁ ρ̂) → map f₁ ρ ≅ map f₂ ρ
      helper ε       = H.refl
      helper (ρ ▻ t) = begin
        map f₁ (ρ ▻ t)     ≅⟨ map-▻ f₁ ρ t ⟩
        map f₁ ρ ▻ f₁ · t  ≅⟨ ▻⇨-cong P.refl P.refl H.refl H.refl
                                      (helper ρ) (f₁≅f₂ t) ⟩
        map f₂ ρ ▻ f₂ · t  ≅⟨ H.sym $ map-▻ f₂ ρ t ⟩
        map f₂ (ρ ▻ t)     ∎

    map-cong-ext₂ : ∀ {Γ₁ Δ₁ Ε₁} {ρ̂₁₁ : Γ₁ ⇨̂ Δ₁} {ρ̂₂₁ : Δ₁ ⇨̂ Ε₁}
                      {f₁ : [ T₁ ⟶ T₂ ] ρ̂₂₁} {ρ₁ : Sub T₁ ρ̂₁₁}
                      {Γ₂ Δ₂ Ε₂} {ρ̂₁₂ : Γ₂ ⇨̂ Δ₂} {ρ̂₂₂ : Δ₂ ⇨̂ Ε₂}
                      {f₂ : [ T₁ ⟶ T₂ ] ρ̂₂₂} {ρ₂ : Sub T₁ ρ̂₁₂} →
                    Γ₁ ≡ Γ₂ → Δ₁ ≡ Δ₂ → Ε₁ ≡ Ε₂ → ρ̂₁₁ ≅ ρ̂₁₂ → ρ̂₂₁ ≅ ρ̂₂₂ →
                    (∀ {σ₁ σ₂} {t₁ : Δ₁ ⊢₁ σ₁} {t₂ : Δ₂ ⊢₁ σ₂} →
                       σ₁ ≅ σ₂ → t₁ ≅ t₂ → f₁ · t₁ ≅ f₂ · t₂) →
                    ρ₁ ≅ ρ₂ → map f₁ ρ₁ ≅ map f₂ ρ₂
    map-cong-ext₂ Γ₁≡Γ₂ P.refl Ε₁≡Ε₂ ρ̂₁₁≅ρ̂₁₂ ρ̂₂₁≅ρ̂₂₂ f₁≅f₂ ρ₁≅ρ₂ =
      map-cong-ext₁ Γ₁≡Γ₂ Ε₁≡Ε₂ ρ̂₁₁≅ρ̂₁₂ ρ̂₂₁≅ρ̂₂₂
                    (λ t → f₁≅f₂ H.refl (H.refl {x = t})) ρ₁≅ρ₂

    private

      -- A helper lemma.

      /∋-map-▻ :
        ∀ {Γ Δ Ε σ τ} {ρ̂₁ : Γ ⇨̂ Δ} {ρ̂₂ : Δ ⇨̂ Ε} {t} →
        (x : Γ ▻ σ ∋ τ) (f : [ T₁ ⟶ T₂ ] ρ̂₂) (ρ : Sub T₁ ρ̂₁) →
        x /∋ map f (ρ ▻ t) ≅ x /∋ (map f ρ ▻ f · t)
      /∋-map-▻ {t = t} x f ρ =
        /∋-cong P.refl P.refl H.refl
          (H.refl {x = x})
          (▻̂-cong P.refl P.refl H.refl H.refl
                  (H.≡-to-≅ $ corresponds f t))
          (map-▻ f ρ t)

    -- Some sort of naturality statement for _/∋_.

    /∋-map : ∀ {Γ Δ Ε σ} {ρ̂₁ : Γ ⇨̂ Δ} {ρ̂₂ : Δ ⇨̂ Ε} →
             (x : Γ ∋ σ) (f : [ T₁ ⟶ T₂ ] ρ̂₂) (ρ : Sub T₁ ρ̂₁) →
             x /∋ map f ρ ≡ f · (x /∋ ρ)
    /∋-map (zero {σ = σ}) f (ρ ▻ t) = H.≅-to-≡ (begin
      zero {σ = σ} /∋ map f (ρ ▻ t)     ≅⟨ /∋-map-▻ (zero {σ = σ}) f ρ ⟩
      zero {σ = σ} /∋ (map f ρ ▻ f · t) ≡⟨ P.refl ⟩
      f · t                             ∎)
      where open H.≅-Reasoning
    /∋-map (suc {σ = σ} x) f (ρ ▻ t) = H.≅-to-≡ (begin
      suc         x /∋ map f (ρ ▻ t)      ≅⟨ /∋-map-▻ (suc x) f ρ ⟩
      suc {σ = σ} x /∋ (map f ρ ▻ f · t)  ≡⟨ P.refl ⟩
      x /∋ map f ρ                        ≡⟨ /∋-map x f ρ ⟩
      f · (x /∋ ρ)                        ∎)
      where open H.≅-Reasoning

open Dummy public

abstract

  -- Map is functorial.

  map-[id] : ∀ {t} {T : Term-like t} {Γ Δ} {ρ̂ : Γ ⇨̂ Δ}
             (ρ : Sub T ρ̂) → map ([id] {T = T}) ρ ≡ ρ
  map-[id] ε       = P.refl
  map-[id] (ρ ▻ t) = H.≅-to-≡ $
    ▻⇨-cong P.refl P.refl H.refl H.refl
            (H.≡-to-≅ $ map-[id] ρ) H.refl

  map-[∘] :
    ∀ {t₁} {T₁ : Term-like t₁}
      {t₂} {T₂ : Term-like t₂}
      {t₃} {T₃ : Term-like t₃}
      {Γ Δ Ε Ζ} {ρ̂₁ : Γ ⇨̂ Δ} {ρ̂₂ : Δ ⇨̂ Ε} {ρ̂₃ : Ε ⇨̂ Ζ}
    (f₂ : [ T₂ ⟶ T₃ ] ρ̂₃) (f₁ : [ T₁ ⟶ T₂ ] ρ̂₂)
    (ρ : Sub T₁ ρ̂₁) →
    map (f₂ [∘] f₁) ρ ≡ map f₂ (map f₁ ρ)
  map-[∘] f₂ f₁ ε       = P.refl
  map-[∘] f₂ f₁ (ρ ▻ t) = H.≅-to-≡ (begin
    map (f₂ [∘] f₁) (ρ ▻ t)            ≅⟨ map-▻ (f₂ [∘] f₁) ρ t ⟩
    map (f₂ [∘] f₁) ρ ▻ f₂ · (f₁ · t)  ≅⟨ ▻⇨-cong P.refl P.refl H.refl H.refl
                                                  (H.≡-to-≅ $ map-[∘] f₂ f₁ ρ) H.refl ⟩
    map f₂ (map f₁ ρ) ▻ f₂ · (f₁ · t)  ≅⟨ H.sym $ map-▻ f₂ (map f₁ ρ) (f₁ · t) ⟩
    map f₂ (map f₁ ρ ▻ f₁ · t)         ≅⟨ map-cong P.refl P.refl P.refl
                                                   (▻̂-cong P.refl P.refl H.refl H.refl
                                                           (H.≡-to-≅ $ P.sym $ corresponds f₁ t))
                                                   H.refl H.refl
                                                   (H.sym $ map-▻ f₁ ρ t) ⟩
    map f₂ (map f₁ (ρ ▻ t))            ∎)
    where open H.≅-Reasoning
