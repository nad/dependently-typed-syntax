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
open import Relation.Binary.PropositionalEquality as P using (_≡_)

open Context Uni
open TermLike Uni

private
 module Dummy₁ {t} (T : TermLike.Term-like Uni t) where

  open Term-like T

  infixl 5 _▻_

  -- Substitutions, represented as sequences of terms.

  data Sub : ∀ {Γ Δ} → Γ ⇨̂ Δ → Set (u ⊔ e ⊔ t) where
    ε   : ∀ {Δ} → Sub ε̂[ Δ ]
    _▻_ : ∀ {Γ Δ σ} {ρ̂ : Γ ⇨̂ Δ}
          (ρ : Sub ρ̂) (t : Δ ⊢ σ /̂ ρ̂) → Sub (ρ̂ ▻̂[ σ ] ⟦ t ⟧)

  -- A sequence of matching substitutions. (The reflexive transitive
  -- closure of Sub.)

  data Subs {Γ} : ∀ {Δ} → Γ ⇨̂ Δ → Set (u ⊔ e ⊔ t) where
    ε   : Subs îd[ Γ ]
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
--             (≅-Value-⇒-≡ $ P.sym $ corresponds f t)
--             (map f ρ₁ ▻ f · t)
--
-- Previously it was defined roughly as follows (the code below is
-- untested and has been adapted to the current version of the
-- library, as it was at the time of writing, with some imagined
-- changes):
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
--       P.subst (λ ρ̂ → _ ⊢₂ σ /̂ ρ̂)
--               (≅-⇨̂-⇒-≡ $ P.sym $ map-lemma f ρ)
--               (f · t)
--
--     abstract
--
--       map-lemma :
--         ∀ {Γ Δ Ε} {ρ̂₂ : Δ ⇨̂ Ε} →
--         (f : [ T₁ ⟶ T₂ ] ρ̂₂) (ρ₁ : Γ ⇨₁ Δ) →
--         ⟦ map f ρ₁ ⟧₂⇨ ≅-⇨̂ ⟦ ρ₁ ⟧₁⇨ ∘̂ ρ₂
--       map-lemma           f ε                 = P.refl
--       map-lemma {ρ₂ = ρ₂} f (_▻_ {σ = σ} ρ t) =
--         ▻̂-cong P.refl (map-lemma f ρ) (begin
--           [ ⟦ P.subst (λ ρ̂ → _ ⊢₂ σ /̂ ρ̂)
--                       (≅-⇨̂-⇒-≡ $ P.sym (map-lemma f ρ))
--                       (f · t) ⟧₂                        ]  ≡⟨ Term-like.⟦⟧-cong T₂
--                                                                 (Term-like.drop-subst-⊢ T₂
--                                                                    (λ ρ̂ → σ /̂ ρ̂)
--                                                                    (≅-⇨̂-⇒-≡ $ P.sym (map-lemma f ρ))) ⟩
--           [ ⟦ f · t ⟧₂                                  ]  ≡⟨ P.sym $ corresponds f t ⟩
--           [ ⟦ t ⟧₁ /̂Val ρ₂                              ]  ∎)

private
 module Dummy₂ {t} {T : TermLike.Term-like Uni t} where

  open Term-like T

  -- Some variants.

  ε⇨[_] : ∀ Δ → Sub T ε̂[ Δ ]
  ε⇨[ _ ] = ε

  infixl 5 _▻⇨[_]_

  _▻⇨[_]_ : ∀ {Γ Δ} {ρ̂ : Γ ⇨̂ Δ} →
            Sub T ρ̂ → ∀ σ (t : Δ ⊢ σ /̂ ρ̂) → Sub T (ρ̂ ▻̂[ σ ] ⟦ t ⟧)
  ρ ▻⇨[ _ ] t = ρ ▻ t

  ε⇨⋆[_] : ∀ Γ → Subs T îd[ Γ ]
  ε⇨⋆[ _ ] = ε

  -- Equality of substitutions.

  record [⇨] : Set (u ⊔ e ⊔ t) where
    constructor [_]
    field
      {Γ Δ} : Ctxt
      {ρ̂}   : Γ ⇨̂ Δ
      ρ     : Sub T ρ̂

  infix 4 _≅-⇨_

  _≅-⇨_ : ∀ {Γ₁ Δ₁} {ρ̂₁ : Γ₁ ⇨̂ Δ₁} (ρ₁ : Sub T ρ̂₁)
            {Γ₂ Δ₂} {ρ̂₂ : Γ₂ ⇨̂ Δ₂} (ρ₂ : Sub T ρ̂₂) → Set _
  ρ₁ ≅-⇨ ρ₂ = [⇨].[_] ρ₁ ≡ [ ρ₂ ]

  ≅-⇨-⇒-≡ : ∀ {Γ Δ} {ρ̂ : Γ ⇨̂ Δ} {ρ₁ ρ₂ : Sub T ρ̂} →
            ρ₁ ≅-⇨ ρ₂ → ρ₁ ≡ ρ₂
  ≅-⇨-⇒-≡ P.refl = P.refl

  -- Certain uses of substitutivity can be removed.

  drop-subst-Sub :
    ∀ {a} {A : Set a} {x₁ x₂ : A} {Γ Δ}
    (f : A → Γ ⇨̂ Δ) {ρ} (eq : x₁ ≡ x₂) →
    P.subst (λ x → Sub T (f x)) eq ρ ≅-⇨ ρ
  drop-subst-Sub f P.refl = P.refl

  -- Equality of sequences of substitutions.

  record [⇨⋆] : Set (u ⊔ e ⊔ t) where
    constructor [_]
    field
      {Γ Δ} : Ctxt
      {ρ̂}   : Γ ⇨̂ Δ
      ρs    : Subs T ρ̂

  infix 4 _≅-⇨⋆_

  _≅-⇨⋆_ : ∀ {Γ₁ Δ₁} {ρ̂₁ : Γ₁ ⇨̂ Δ₁} (ρs₁ : Subs T ρ̂₁)
             {Γ₂ Δ₂} {ρ̂₂ : Γ₂ ⇨̂ Δ₂} (ρs₂ : Subs T ρ̂₂) → Set _
  ρs₁ ≅-⇨⋆ ρs₂ = [⇨⋆].[_] ρs₁ ≡ [ ρs₂ ]

  ≅-⇨⋆-⇒-≡ : ∀ {Γ Δ} {ρ̂ : Γ ⇨̂ Δ} {ρs₁ ρs₂ : Subs T ρ̂} →
             ρs₁ ≅-⇨⋆ ρs₂ → ρs₁ ≡ ρs₂
  ≅-⇨⋆-⇒-≡ P.refl = P.refl

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

  -- Application of substitutions to values.

  infixl 8 _/Val_

  _/Val_ : ∀ {Γ Δ σ} {ρ̂ : Γ ⇨̂ Δ} →
           Value Γ σ → Sub T ρ̂ → Value Δ (σ /̂ ρ̂)
  v /Val ρ = v /̂Val ⟦ ρ ⟧⇨

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
                 x /̂∋ ⟦ ρ ⟧⇨ ≅-Value ⟦ x /∋ ρ ⟧
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
               ĥead ⟦ ρ ⟧⇨ ≅-Value ⟦ head ρ ⟧
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

  ε⇨-cong : ∀ {Δ₁ Δ₂} → Δ₁ ≡ Δ₂ → ε⇨[ Δ₁ ] ≅-⇨ ε⇨[ Δ₂ ]
  ε⇨-cong P.refl = P.refl

  ▻⇨-cong :
    ∀ {Γ₁ Δ₁ σ₁} {ρ̂₁ : Γ₁ ⇨̂ Δ₁} {ρ₁ : Sub T ρ̂₁} {t₁ : Δ₁ ⊢ σ₁ / ρ₁}
      {Γ₂ Δ₂ σ₂} {ρ̂₂ : Γ₂ ⇨̂ Δ₂} {ρ₂ : Sub T ρ̂₂} {t₂ : Δ₂ ⊢ σ₂ / ρ₂} →
    σ₁ ≅-Type σ₂ → ρ₁ ≅-⇨ ρ₂ → t₁ ≅-⊢ t₂ →
    ρ₁ ▻⇨[ σ₁ ] t₁ ≅-⇨ ρ₂ ▻⇨[ σ₂ ] t₂
  ▻⇨-cong P.refl P.refl P.refl = P.refl

  ε⇨⋆-cong : ∀ {Γ₁ Γ₂} → Γ₁ ≡ Γ₂ → ε⇨⋆[ Γ₁ ] ≅-⇨⋆ ε⇨⋆[ Γ₂ ]
  ε⇨⋆-cong P.refl = P.refl

  ▻⇨⋆-cong :
    ∀ {Γ₁ Δ₁ Ε₁} {ρ̂₁₁ : Γ₁ ⇨̂ Δ₁} {ρ̂₂₁ : Δ₁ ⇨̂ Ε₁}
      {ρs₁ : Subs T ρ̂₁₁} {ρ₁ : Sub T ρ̂₂₁}
      {Γ₂ Δ₂ Ε₂} {ρ̂₁₂ : Γ₂ ⇨̂ Δ₂} {ρ̂₂₂ : Δ₂ ⇨̂ Ε₂}
      {ρs₂ : Subs T ρ̂₁₂} {ρ₂ : Sub T ρ̂₂₂} →
    ρs₁ ≅-⇨⋆ ρs₂ → ρ₁ ≅-⇨ ρ₂ → ρs₁ ▻ ρ₁ ≅-⇨⋆ ρs₂ ▻ ρ₂
  ▻⇨⋆-cong P.refl P.refl = P.refl

  ⟦⟧⇨-cong : ∀ {Γ₁ Δ₁} {ρ̂₁ : Γ₁ ⇨̂ Δ₁} {ρ₁ : Sub T ρ̂₁}
               {Γ₂ Δ₂} {ρ̂₂ : Γ₂ ⇨̂ Δ₂} {ρ₂ : Sub T ρ̂₂} →
             ρ₁ ≅-⇨ ρ₂ → ⟦ ρ₁ ⟧⇨ ≅-⇨̂ ⟦ ρ₂ ⟧⇨
  ⟦⟧⇨-cong P.refl = P.refl

  /-cong : ∀ {Γ₁ Δ₁ σ₁} {ρ̂₁ : Γ₁ ⇨̂ Δ₁} {ρ₁ : Sub T ρ̂₁}
             {Γ₂ Δ₂ σ₂} {ρ̂₂ : Γ₂ ⇨̂ Δ₂} {ρ₂ : Sub T ρ̂₂} →
           σ₁ ≅-Type σ₂ → ρ₁ ≅-⇨ ρ₂ → σ₁ / ρ₁ ≅-Type σ₂ / ρ₂
  /-cong P.refl P.refl = P.refl

  /⁺-cong : ∀ {Γ₁ Δ₁ Γ⁺₁} {ρ̂₁ : Γ₁ ⇨̂ Δ₁} {ρ₁ : Sub T ρ̂₁}
              {Γ₂ Δ₂ Γ⁺₂} {ρ̂₂ : Γ₂ ⇨̂ Δ₂} {ρ₂ : Sub T ρ̂₂} →
            Γ⁺₁ ≅-Ctxt⁺ Γ⁺₂ → ρ₁ ≅-⇨ ρ₂ → Γ⁺₁ /⁺ ρ₁ ≅-Ctxt⁺ Γ⁺₂ /⁺ ρ₂
  /⁺-cong P.refl P.refl = P.refl

  /⁺⋆-cong : ∀ {Γ₁ Δ₁ Γ⁺₁} {ρ̂₁ : Γ₁ ⇨̂ Δ₁} {ρs₁ : Subs T ρ̂₁}
               {Γ₂ Δ₂ Γ⁺₂} {ρ̂₂ : Γ₂ ⇨̂ Δ₂} {ρs₂ : Subs T ρ̂₂} →
             Γ⁺₁ ≅-Ctxt⁺ Γ⁺₂ → ρs₁ ≅-⇨⋆ ρs₂ →
             Γ⁺₁ /⁺⋆ ρs₁ ≅-Ctxt⁺ Γ⁺₂ /⁺⋆ ρs₂
  /⁺⋆-cong P.refl P.refl = P.refl

  /∋-cong : ∀ {Γ₁ Δ₁ σ₁} {x₁ : Γ₁ ∋ σ₁} {ρ̂₁ : Γ₁ ⇨̂ Δ₁} {ρ₁ : Sub T ρ̂₁}
              {Γ₂ Δ₂ σ₂} {x₂ : Γ₂ ∋ σ₂} {ρ̂₂ : Γ₂ ⇨̂ Δ₂} {ρ₂ : Sub T ρ̂₂} →
            x₁ ≅-∋ x₂ → ρ₁ ≅-⇨ ρ₂ → x₁ /∋ ρ₁ ≅-⊢ x₂ /∋ ρ₂
  /∋-cong P.refl P.refl = P.refl

  tail-cong : ∀ {Γ₁ Δ₁ σ₁} {ρ̂₁ : Γ₁ ▻ σ₁ ⇨̂ Δ₁} {ρ₁ : Sub T ρ̂₁}
                {Γ₂ Δ₂ σ₂} {ρ̂₂ : Γ₂ ▻ σ₂ ⇨̂ Δ₂} {ρ₂ : Sub T ρ̂₂} →
              ρ₁ ≅-⇨ ρ₂ → tail ρ₁ ≅-⇨ tail ρ₂
  tail-cong P.refl = P.refl

  head-cong : ∀ {Γ₁ Δ₁ σ₁} {ρ̂₁ : Γ₁ ▻ σ₁ ⇨̂ Δ₁} {ρ₁ : Sub T ρ̂₁}
                {Γ₂ Δ₂ σ₂} {ρ̂₂ : Γ₂ ▻ σ₂ ⇨̂ Δ₂} {ρ₂ : Sub T ρ̂₂} →
              ρ₁ ≅-⇨ ρ₂ → head ρ₁ ≅-⊢ head ρ₂
  head-cong P.refl = P.refl

  abstract

    -- Some eta-laws.

    ηε : ∀ {Δ} {ρ̂ : ε ⇨̂ Δ} (ρ : Sub T ρ̂) → ρ ≅-⇨ ε⇨[ Δ ]
    ηε ε = P.refl

    η▻ : ∀ {Γ Δ σ} {ρ̂ : Γ ▻ σ ⇨̂ Δ} (ρ : Sub T ρ̂) →
         ρ ≅-⇨ tail ρ ▻⇨[ σ ] head ρ
    η▻ (ρ ▻ t) = P.refl

    -- Two substitutions are equal if their indices are equal and
    -- their projections are pairwise equal.

    extensionality :
      ∀ {Γ Δ₁} {ρ̂₁ : Γ ⇨̂ Δ₁} {ρ₁ : Sub T ρ̂₁}
          {Δ₂} {ρ̂₂ : Γ ⇨̂ Δ₂} {ρ₂ : Sub T ρ̂₂} →
      Δ₁ ≅-Ctxt Δ₂ → (∀ {σ} (x : Γ ∋ σ) → x /∋ ρ₁ ≅-⊢ x /∋ ρ₂) →
      ρ₁ ≅-⇨ ρ₂
    extensionality {ρ₁ = ε}       {ρ₂ = ε}       Δ₁≅Δ₂ hyp = ε⇨-cong Δ₁≅Δ₂
    extensionality {ρ₁ = ρ₁ ▻ t₁} {ρ₂ = ρ₂ ▻ t₂} Δ₁≅Δ₂ hyp =
      ▻⇨-cong P.refl
              (extensionality Δ₁≅Δ₂ (hyp ∘ suc))
              (hyp zero)

open Dummy₂ public
