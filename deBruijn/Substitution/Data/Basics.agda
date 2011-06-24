------------------------------------------------------------------------
-- Substitutions containing certain term-like things
------------------------------------------------------------------------

{-# OPTIONS --universe-polymorphism #-}

import deBruijn.TermLike as TermLike
open import Universe

module deBruijn.Substitution.Data.Basics
  {u e} {Uni : Universe u e} where

import deBruijn.Context as Context
open import Function using (id; _∘_; _$_)
open import Level using (_⊔_)
open import Relation.Binary.HeterogeneousEquality as H using (_≅_)
open import Relation.Binary.PropositionalEquality as P using (_≡_)

open Context Uni
open TermLike Uni

private
 module Dummy₁ {t} (T : TermLike.Term-like Uni t) where

  open Term-like T

  infixl 5 _▻_

  -- Substitutions, represented as sequences of terms.

  data Sub : ∀ {Γ Δ} → Γ ⇨̂ Δ → Set (u ⊔ e ⊔ t) where
    ε   : ∀ {Δ} → Sub (ε̂ {Δ = Δ})
    _▻_ : ∀ {Γ Δ σ} {ρ̂ : Γ ⇨̂ Δ}
          (ρ : Sub ρ̂) (t : Δ ⊢ σ /̂ ρ̂) → Sub (_▻̂_ {σ = σ} ρ̂ ⟦ t ⟧)

  -- A sequence of matching substitutions. (The reflexive transitive
  -- closure of Sub.)

  data Subs {Γ} : ∀ {Δ} → Γ ⇨̂ Δ → Set (u ⊔ e ⊔ t) where
    ε   : Subs (îd {Γ = Γ})
    _▻_ : ∀ {Δ Ε} {ρ̂₁ : Γ ⇨̂ Δ} {ρ̂₂ : Δ ⇨̂ Ε}
          (ρs : Subs ρ̂₁) (ρ : Sub ρ̂₂) → Subs (ρ̂₁ ∘̂ ρ̂₂)

open Dummy₁ public

-- Originally these substitutions were defined without the context
-- morphism index, but this led to the need to prove lots of lemmas
-- which hold by definition in the current setting. As an example the
-- map function (in deBruijn.Substitution.Data.Map) is currently
-- defined as follows:
--
--   -- Map.
--
--   map : ∀ {Γ Δ Ε} {ρ̂₁ : Γ ⇨̂ Δ} {ρ̂₂ : Δ ⇨̂ Ε} →
--         [ T₁ ⟶ T₂ ] ρ̂₂ → Sub T₁ ρ̂₁ → Sub T₂ (ρ̂₁ ∘̂ ρ̂₂)
--   map           f ε        = ε
--   map {ρ̂₂ = ρ̂₂} f (ρ₁ ▻ t) =
--     P.subst (λ v → Sub T₂ (⟦ ρ₁ ⟧⇨ ∘̂ ρ̂₂ ▻̂ v))
--             (P.sym $ corresponds f t)
--             (map f ρ₁ ▻ f · t)
--
-- Previously it was defined roughly as follows:
--
--   mutual
--
--     -- Map.
--
--     map : ∀ {Γ Δ Ε} {ρ̂₂ : Δ ⇨̂ Ε} →
--           [ T₁ ⟶ T₂ ] ρ̂₂ → (ρ₁ : Γ ⇨₁ Δ) → Γ ⇨₂ Ε
--     map f ε                 = ε
--     map f (_▻_ {σ = σ} ρ t) =
--       map f ρ ▻
--       P.subst (λ ρ̂ → _ ⊢₂ σ /̂ ρ̂) (P.sym $ map-lemma f ρ) (f · t)
--
--     abstract
--
--       map-lemma :
--         ∀ {Γ Δ Ε} {ρ̂₂ : Δ ⇨̂ Ε} →
--         (f : [ T₁ ⟶ T₂ ] ρ̂₂) (ρ₁ : Γ ⇨₁ Δ) →
--         ⟦ map f ρ₁ ⟧₂⇨ ≡ ⟦ ρ₁ ⟧₁⇨ ∘̂ ρ₂
--       map-lemma           f ε                 = P.refl
--       map-lemma {ρ₂ = ρ₂} f (_▻_ {σ = σ} ρ t) = H.≅-to-≡ $
--         ▻̂-cong P.refl P.refl H.refl (H.≡-to-≅ $ map-lemma f ρ) (begin
--           ⟦ P.subst (λ ρ̂ → _ ⊢₂ σ /̂ ρ̂)
--                     (P.sym (map-lemma f ρ))
--                     (f · t) ⟧₂               ≅⟨ Term-like.⟦⟧-cong T₂ P.refl
--                                                   (/̂-cong P.refl P.refl (H.refl {x = σ})
--                                                           (H.≡-to-≅ $ map-lemma f ρ))
--                                                   (H.≡-subst-removable (λ ρ̂ → _ ⊢₂ σ /̂ ρ̂)
--                                                                        (P.sym (map-lemma f ρ)) _) ⟩
--           ⟦ f · t ⟧₂                         ≡⟨ P.sym $ corresponds f t ⟩
--           ⟦ t ⟧₁ /Val ρ₂                     ∎)
--         where open H.≅-Reasoning

private
 module Dummy₂ {t} {T : TermLike.Term-like Uni t} where

  open Term-like T

  -- Interpretation of substitutions: context morphisms.

  ⟦_⟧⇨ : ∀ {Γ Δ} {ρ̂ : Γ ⇨̂ Δ} → Sub T ρ̂ → Γ ⇨̂ Δ
  ⟦_⟧⇨ {ρ̂ = ρ̂} _ = ρ̂

  ⟦_⟧⇨⋆ : ∀ {Γ Δ} {ρ̂ : Γ ⇨̂ Δ} → Subs T ρ̂ → Γ ⇨̂ Δ
  ⟦_⟧⇨⋆ {ρ̂ = ρ̂} _ = ρ̂

  -- Application of substitutions to types.

  infixl 8 _/_ _/⋆_

  _/_ : ∀ {Γ Δ} {ρ̂ : Γ ⇨̂ Δ} → Type Γ → Sub T ρ̂ → Type Δ
  σ / ρ = σ /̂ ⟦ ρ ⟧⇨

  _/⋆_ : ∀ {Γ Δ} {ρ̂ : Γ ⇨̂ Δ} → Type Γ → Subs T ρ̂ → Type Δ
  σ /⋆ ρs = σ /̂ ⟦ ρs ⟧⇨⋆

  -- Application of substitutions to context extensions.

  infixl 8 _/⁺_ _/⁺⋆_

  _/⁺_ : ∀ {Γ Δ} {ρ̂ : Γ ⇨̂ Δ} → Ctxt⁺ Γ → Sub T ρ̂ → Ctxt⁺ Δ
  Γ⁺ /⁺ ρ = Γ⁺ /̂⁺ ⟦ ρ ⟧⇨

  _/⁺⋆_ : ∀ {Γ Δ} {ρ̂ : Γ ⇨̂ Δ} → Ctxt⁺ Γ → Subs T ρ̂ → Ctxt⁺ Δ
  Γ⁺ /⁺⋆ ρs = Γ⁺ /̂⁺ ⟦ ρs ⟧⇨⋆

  -- Application of substitutions to variables.

  infixl 8 _/∋_ _/∋-lemma_

  _/∋_ : ∀ {Γ Δ σ} {ρ̂ : Γ ⇨̂ Δ} → Γ ∋ σ → (ρ : Sub T ρ̂) → Δ ⊢ σ / ρ
  zero  /∋ (ρ ▻ y) = y
  suc x /∋ (ρ ▻ y) = x /∋ ρ

  abstract

    _/∋-lemma_ : ∀ {Γ Δ σ} {ρ̂ : Γ ⇨̂ Δ} (x : Γ ∋ σ) (ρ : Sub T ρ̂) →
                 x /̂∋ ⟦ ρ ⟧⇨ ≡ ⟦ x /∋ ρ ⟧
    zero  /∋-lemma (ρ ▻ y) = P.refl
    suc x /∋-lemma (ρ ▻ y) = x /∋-lemma ρ

  app∋ : ∀ {Γ Δ} {ρ̂ : Γ ⇨̂ Δ} → Sub T ρ̂ → [ Var ⟶ T ] ρ̂
  app∋ ρ = record
    { function    = λ _ x → x /∋       ρ
    ; corresponds = λ _ x → x /∋-lemma ρ
    }

  -- The tail of a nonempty substitution.

  tail : ∀ {Γ Δ σ} {ρ̂ : Γ ▻ σ ⇨̂ Δ} → Sub T ρ̂ → Sub T (t̂ail ρ̂)
  tail (ρ ▻ t) = ρ

  -- The head of a nonempty substitution.

  head : ∀ {Γ Δ σ} {ρ̂ : Γ ▻ σ ⇨̂ Δ} (ρ : Sub T ρ̂) → Δ ⊢ σ / tail ρ
  head (ρ ▻ t) = t

  head-lemma : ∀ {Γ Δ σ} {ρ̂ : Γ ▻ σ ⇨̂ Δ} (ρ : Sub T ρ̂) →
               ĥead ⟦ ρ ⟧⇨ ≡ ⟦ head ρ ⟧
  head-lemma (ρ ▻ t) = P.refl

  -- Fold for sequences of substitutions.

  fold : ∀ {f} (F : ∀ {Γ Δ} → Γ ⇨̂ Δ → Set f) {Γ} →
         F (îd {Γ = Γ}) →
         (∀ {Δ Ε} {ρ̂₁ : Γ ⇨̂ Δ} {ρ̂₂ : Δ ⇨̂ Ε} →
            F ρ̂₁ → Sub T ρ̂₂ → F (ρ̂₁ ∘̂ ρ̂₂)) →
         ∀ {Δ} {ρ̂ : Γ ⇨̂ Δ} → Subs T ρ̂ → F ρ̂
  fold F nil cons ε        = nil
  fold F nil cons (ρs ▻ ρ) = cons (fold F nil cons ρs) ρ

  -- Some congruence lemmas.

  ε⇨-cong : ∀ {Δ₁ Δ₂} → Δ₁ ≡ Δ₂ →
            Sub.ε {T = T} {Δ = Δ₁} ≅ Sub.ε {T = T} {Δ = Δ₂}
  ε⇨-cong P.refl = H.refl

  ▻⇨-cong :
    ∀ {Γ₁ Δ₁ σ₁} {ρ̂₁ : Γ₁ ⇨̂ Δ₁} {ρ₁ : Sub T ρ̂₁} {t₁ : Δ₁ ⊢ σ₁ / ρ₁}
      {Γ₂ Δ₂ σ₂} {ρ̂₂ : Γ₂ ⇨̂ Δ₂} {ρ₂ : Sub T ρ̂₂} {t₂ : Δ₂ ⊢ σ₂ / ρ₂} →
    Γ₁ ≡ Γ₂ → Δ₁ ≡ Δ₂ → σ₁ ≅ σ₂ → ρ̂₁ ≅ ρ̂₂ → ρ₁ ≅ ρ₂ → t₁ ≅ t₂ →
    Sub._▻_ {σ = σ₁} ρ₁ t₁ ≅ Sub._▻_ {σ = σ₂} ρ₂ t₂
  ▻⇨-cong P.refl P.refl H.refl H.refl H.refl H.refl = H.refl

  ε⇨⋆-cong : ∀ {Γ₁ Γ₂} → Γ₁ ≡ Γ₂ →
             Subs.ε {T = T} {Γ = Γ₁} ≅ Subs.ε {T = T} {Γ = Γ₂}
  ε⇨⋆-cong P.refl = H.refl

  ▻⇨⋆-cong :
    ∀ {Γ₁ Δ₁ Ε₁} {ρ̂₁₁ : Γ₁ ⇨̂ Δ₁} {ρ̂₂₁ : Δ₁ ⇨̂ Ε₁}
      {ρs₁ : Subs T ρ̂₁₁} {ρ₁ : Sub T ρ̂₂₁}
      {Γ₂ Δ₂ Ε₂} {ρ̂₁₂ : Γ₂ ⇨̂ Δ₂} {ρ̂₂₂ : Δ₂ ⇨̂ Ε₂}
      {ρs₂ : Subs T ρ̂₁₂} {ρ₂ : Sub T ρ̂₂₂} →
    Γ₁ ≡ Γ₂ → Δ₁ ≡ Δ₂ → Ε₁ ≡ Ε₂ → ρ̂₁₁ ≅ ρ̂₁₂ → ρ̂₂₁ ≅ ρ̂₂₂ →
    ρs₁ ≅ ρs₂ → ρ₁ ≅ ρ₂ → Subs._▻_ ρs₁ ρ₁ ≅ Subs._▻_ ρs₂ ρ₂
  ▻⇨⋆-cong P.refl P.refl P.refl H.refl H.refl H.refl H.refl = H.refl

  ⟦⟧⇨-cong : ∀ {Γ₁ Δ₁} {ρ̂₁ : Γ₁ ⇨̂ Δ₁} {ρ₁ : Sub T ρ̂₁}
               {Γ₂ Δ₂} {ρ̂₂ : Γ₂ ⇨̂ Δ₂} {ρ₂ : Sub T ρ̂₂} →
             ρ̂₁ ≅ ρ̂₂ → ⟦ ρ₁ ⟧⇨ ≅ ⟦ ρ₂ ⟧⇨
  ⟦⟧⇨-cong = id

  /-cong : ∀ {Γ₁ Δ₁ σ₁} {ρ̂₁ : Γ₁ ⇨̂ Δ₁} {ρ₁ : Sub T ρ̂₁}
             {Γ₂ Δ₂ σ₂} {ρ̂₂ : Γ₂ ⇨̂ Δ₂} {ρ₂ : Sub T ρ̂₂} →
           Γ₁ ≡ Γ₂ → Δ₁ ≡ Δ₂ → σ₁ ≅ σ₂ → ρ̂₁ ≅ ρ̂₂ → σ₁ / ρ₁ ≅ σ₂ / ρ₂
  /-cong P.refl P.refl H.refl H.refl = H.refl

  /⁺-cong : ∀ {Γ₁ Δ₁ Γ⁺₁} {ρ̂₁ : Γ₁ ⇨̂ Δ₁} {ρ₁ : Sub T ρ̂₁}
              {Γ₂ Δ₂ Γ⁺₂} {ρ̂₂ : Γ₂ ⇨̂ Δ₂} {ρ₂ : Sub T ρ̂₂} →
            Γ₁ ≡ Γ₂ → Δ₁ ≡ Δ₂ → Γ⁺₁ ≅ Γ⁺₂ → ρ̂₁ ≅ ρ̂₂ →
            Γ⁺₁ /⁺ ρ₁ ≅ Γ⁺₂ /⁺ ρ₂
  /⁺-cong P.refl P.refl H.refl H.refl = H.refl

  /⁺⋆-cong : ∀ {Γ₁ Δ₁ Γ⁺₁} {ρ̂₁ : Γ₁ ⇨̂ Δ₁} {ρs₁ : Subs T ρ̂₁}
               {Γ₂ Δ₂ Γ⁺₂} {ρ̂₂ : Γ₂ ⇨̂ Δ₂} {ρs₂ : Subs T ρ̂₂} →
             Γ₁ ≡ Γ₂ → Δ₁ ≡ Δ₂ → Γ⁺₁ ≅ Γ⁺₂ → ρ̂₁ ≅ ρ̂₂ →
             Γ⁺₁ /⁺⋆ ρs₁ ≅ Γ⁺₂ /⁺⋆ ρs₂
  /⁺⋆-cong P.refl P.refl H.refl H.refl = H.refl

  /∋-cong : ∀ {Γ₁ Δ₁ σ₁} {x₁ : Γ₁ ∋ σ₁} {ρ̂₁ : Γ₁ ⇨̂ Δ₁} {ρ₁ : Sub T ρ̂₁}
              {Γ₂ Δ₂ σ₂} {x₂ : Γ₂ ∋ σ₂} {ρ̂₂ : Γ₂ ⇨̂ Δ₂} {ρ₂ : Sub T ρ̂₂} →
            Γ₁ ≡ Γ₂ → Δ₁ ≡ Δ₂ → σ₁ ≅ σ₂ → x₁ ≅ x₂ → ρ̂₁ ≅ ρ̂₂ → ρ₁ ≅ ρ₂ →
            x₁ /∋ ρ₁ ≅ x₂ /∋ ρ₂
  /∋-cong P.refl P.refl H.refl H.refl H.refl H.refl = H.refl

  tail-cong : ∀ {Γ₁ Δ₁ σ₁} {ρ̂₁ : Γ₁ ▻ σ₁ ⇨̂ Δ₁} {ρ₁ : Sub T ρ̂₁}
                {Γ₂ Δ₂ σ₂} {ρ̂₂ : Γ₂ ▻ σ₂ ⇨̂ Δ₂} {ρ₂ : Sub T ρ̂₂} →
              Γ₁ ≡ Γ₂ → Δ₁ ≡ Δ₂ → σ₁ ≅ σ₂ → ρ̂₁ ≅ ρ̂₂ → ρ₁ ≅ ρ₂ →
              tail ρ₁ ≅ tail ρ₂
  tail-cong P.refl P.refl H.refl H.refl H.refl = H.refl

  head-cong : ∀ {Γ₁ Δ₁ σ₁} {ρ̂₁ : Γ₁ ▻ σ₁ ⇨̂ Δ₁} {ρ₁ : Sub T ρ̂₁}
                {Γ₂ Δ₂ σ₂} {ρ̂₂ : Γ₂ ▻ σ₂ ⇨̂ Δ₂} {ρ₂ : Sub T ρ̂₂} →
              Γ₁ ≡ Γ₂ → Δ₁ ≡ Δ₂ → σ₁ ≅ σ₂ → ρ̂₁ ≅ ρ̂₂ → ρ₁ ≅ ρ₂ →
              head ρ₁ ≅ head ρ₂
  head-cong P.refl P.refl H.refl H.refl H.refl = H.refl

  abstract

    -- Some eta-laws.

    ηε : ∀ {Δ} {ρ̂ : ε ⇨̂ Δ} (ρ : Sub T ρ̂) → ρ ≡ Sub.ε {Δ = Δ}
    ηε ε = P.refl

    η▻ : ∀ {Γ Δ σ} {ρ̂ : Γ ▻ σ ⇨̂ Δ} (ρ : Sub T ρ̂) →
         ρ ≅ Sub._▻_ {σ = σ} (tail ρ) (head ρ)
    η▻ (ρ ▻ t) = H.refl

    -- Two substitutions are equal if their indices are equal and
    -- their projections are pairwise equal.

    extensionality :
      ∀ {Γ Δ₁ Δ₂} {ρ̂₁ : Γ ⇨̂ Δ₁} {ρ̂₂ : Γ ⇨̂ Δ₂}
      {ρ₁ : Sub T ρ̂₁} {ρ₂ : Sub T ρ̂₂} →
      Δ₁ ≡ Δ₂ → ρ̂₁ ≅ ρ̂₂ → (∀ {σ} (x : Γ ∋ σ) → x /∋ ρ₁ ≅ x /∋ ρ₂) →
      ρ₁ ≅ ρ₂
    extensionality {ρ₁ = ε}       {ρ₂ = ε}       P.refl H.refl hyp = H.refl
    extensionality {ρ₁ = ρ₁ ▻ t₁} {ρ₂ = ρ₂ ▻ t₂} P.refl eq     hyp =
      let ρ̂₁≅ρ̂₂ = t̂ail-cong P.refl P.refl H.refl eq in
      ▻⇨-cong P.refl P.refl H.refl ρ̂₁≅ρ̂₂
              (extensionality P.refl ρ̂₁≅ρ̂₂ (hyp ∘ suc))
              (hyp zero)

open Dummy₂ public
