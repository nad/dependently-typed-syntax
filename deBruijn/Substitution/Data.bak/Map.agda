------------------------------------------------------------------------
-- Map for substitutions
------------------------------------------------------------------------

{-# OPTIONS --universe-polymorphism #-}

import deBruijn.Context as Context
open import Universe

module deBruijn.Substitution.Data.Map
  {u e t₁ t₂}
  {Uni : Universe u e}
  (T₁ : Context.Term-like Uni t₁)
  (T₂ : Context.Term-like Uni t₂)
  where

import deBruijn.Substitution.Basics as Basics
open import Function using (_$_)
open import Level using (_⊔_)
open import Relation.Binary.HeterogeneousEquality as H using (_≅_)
open import Relation.Binary.PropositionalEquality as P using (_≡_)

open Context Uni
open Term-like T₁ renaming (_⊢_ to _⊢₁_; ⟦_⟧ to ⟦_⟧₁)
open Term-like T₂ renaming (_⊢_ to _⊢₂_; ⟦_⟧ to ⟦_⟧₂)
-- T₂ is listed before T₁ below due to a bug in the Agda system.
open Basics T₂ renaming (_⇨_ to _⇨₂_; ⟦_⟧⇨ to ⟦_⟧₂⇨; _/∋_ to _/∋₂_)
open Basics T₁ renaming (_⇨_ to _⇨₁_; ⟦_⟧⇨ to ⟦_⟧₁⇨; _/∋_ to _/∋₁_)

-- Families of semantics-preserving functions.

record Semantics-preserving
         {Γ Δ : Ctxt} (ρ : Γ ⇨̂ Δ) : Set (u ⊔ e ⊔ t₁ ⊔ t₂) where
  field
    function  : ∀ {σ} → Γ ⊢₁ σ → Δ ⊢₂ σ /̂ ρ
    preserves : ∀ {σ} (t : Γ ⊢₁ σ) → ⟦ t ⟧₁ /Val ρ ≡ ⟦ function t ⟧₂

open Semantics-preserving

mutual

  -- Map.

  map : ∀ {Γ Δ Ε} {ρ₂ : Δ ⇨̂ Ε} →
        Semantics-preserving ρ₂ → (ρ₁ : Γ ⇨₁ Δ) → Γ ⇨₂ Ε
  map f ε                 = ε
  map f (_▻_ {σ = σ} ρ t) =
    map f ρ ▻
    P.subst (λ ρ → _ ⊢₂ σ /̂ ρ) (P.sym $ map-lemma f ρ) (function f t)

  abstract

    map-lemma :
      ∀ {Γ Δ Ε} {ρ₂ : Δ ⇨̂ Ε} →
      (f : Semantics-preserving ρ₂) (ρ₁ : Γ ⇨₁ Δ) →
      ⟦ map f ρ₁ ⟧₂⇨ ≡ ⟦ ρ₁ ⟧₁⇨ ∘̂ ρ₂
    map-lemma           f ε                 = P.refl
    map-lemma {ρ₂ = ρ₂} f (_▻_ {σ = σ} ρ t) = H.≅-to-≡ $
      ▻̂-cong P.refl P.refl H.refl (H.≡-to-≅ $ map-lemma f ρ) (begin
        ⟦ P.subst (λ ρ′ → _ ⊢₂ σ /̂ ρ′)
                  (P.sym (map-lemma f ρ))
                  (function f t) ⟧₂        ≅⟨ Term-like.⟦⟧-cong T₂ P.refl
                                                (/̂-cong P.refl P.refl (H.refl {x = σ})
                                                        (H.≡-to-≅ $ map-lemma f ρ))
                                                (H.≡-subst-removable (λ ρ′ → _ ⊢₂ σ /̂ ρ′)
                                                                     (P.sym (map-lemma f ρ)) _) ⟩
        ⟦ function f t ⟧₂                  ≡⟨ P.sym $ preserves f t ⟩
        ⟦ t ⟧₁ /Val ρ₂                     ∎)
      where open H.≅-Reasoning

--     -- Some sort of naturality statement for _/∋_.

--     /∋-map : ∀ {Γ Δ σ}
--              (x : Γ ∋ σ) (f : Semantics-preserving Δ) (ρ : Γ ⇨₁ Δ) →
--              x /∋₂ map f ρ ≅ function f (x /∋₁ ρ)
--     /∋-map (suc x) f (ρ ▻ t)           = /∋-map x f ρ
--     /∋-map zero    f (_▻_ {σ = σ} ρ t) = begin
--       P.subst (λ ρ′ → _ ⊢₂ σ /̂ ρ′)
--               (P.sym $ map-lemma f ρ)
--               (function f t)           ≅⟨ H.≡-subst-removable (λ ρ′ → _ ⊢₂ σ /̂ ρ′)
--                                                               (P.sym (map-lemma f ρ)) _ ⟩
--       function f t                     ∎
--       where open H.≅-Reasoning
