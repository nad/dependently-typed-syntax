------------------------------------------------------------------------
-- Substitutions containing certain term-like things
------------------------------------------------------------------------

{-# OPTIONS --universe-polymorphism #-}

import deBruijn.TermLike as TermLike
open import Universe

module deBruijn.Substitution.Function.Basics
  {u e t} {Uni : Universe u e} {T : TermLike.Term-like Uni t} where

import deBruijn.Context as Context
open import Function using (id; _∘_; _$_)
open import Level using (suc; _⊔_)
open import Relation.Binary.HeterogeneousEquality as H using (_≅_)
open import Relation.Binary.PropositionalEquality as P using (_≡_)

open Context Uni
open TermLike Uni
open Term-like T

-- Substitutions, represented as functions from variables to terms.

Sub : {Γ Δ : Ctxt} → Γ ⇨̂ Δ → Set _
Sub = [ Var ⟶ T ]

-- Interpretation of substitutions: context morphisms.

⟦_⟧⇨ : ∀ {Γ Δ} {ρ̂ : Γ ⇨̂ Δ} → Sub ρ̂ → Γ ⇨̂ Δ
⟦_⟧⇨ {ρ̂ = ρ̂} _ = ρ̂

-- Application of substitutions to types.

infixl 8 _/_

_/_ : ∀ {Γ Δ} {ρ̂ : Γ ⇨̂ Δ} → Type Γ → Sub ρ̂ → Type Δ
σ / ρ = σ /̂ ⟦ ρ ⟧⇨

-- Application of substitutions to variables.

infixl 8 _/∋_ _/∋-lemma_

_/∋_ : ∀ {Γ Δ σ} {ρ̂ : Γ ⇨̂ Δ} → Γ ∋ σ → (ρ : Sub ρ̂) → Δ ⊢ σ / ρ
x /∋ ρ = ρ · x

_/∋-lemma_ : ∀ {Γ Δ σ} {ρ̂ : Γ ⇨̂ Δ} (x : Γ ∋ σ) (ρ : Sub ρ̂) →
             x /̂∋ ⟦ ρ ⟧⇨ ≡ ⟦ x /∋ ρ ⟧
x /∋-lemma ρ = corresponds ρ x

-- Empty substitution.

ε⇨ : ∀ {Δ} → Sub (ε̂ {Δ = Δ})
ε⇨ = record { function = λ _ (); corresponds = λ _ () }

-- Extends a substitution with another term.

infixl 5 _▻⇨_

_▻⇨_ : ∀ {Γ Δ σ} {ρ̂ : Γ ⇨̂ Δ}
       (ρ : Sub ρ̂) (t : Δ ⊢ σ / ρ) → Sub (_▻̂_ {σ = σ} ρ̂ ⟦ t ⟧)
_▻⇨_ {Γ} {Δ} {σ} {ρ̂} ρ t =
  record { function = λ _ → fun; corresponds = λ _ → corr }
  where
  fun : ∀ {τ} → Γ ▻ σ ∋ τ → Δ ⊢ τ /̂ (ρ̂ ▻̂ ⟦ t ⟧)
  fun zero    = t
  fun (suc x) = x /∋ ρ

  corr : ∀ {τ} (x : Γ ▻ σ ∋ τ) → x /̂∋ (ρ̂ ▻̂ ⟦ t ⟧) ≡ ⟦ fun x ⟧
  corr zero    = P.refl
  corr (suc x) = x /∋-lemma ρ

-- The tail of a nonempty substitution.

tail : ∀ {Γ Δ σ} {ρ̂ : Γ ▻ σ ⇨̂ Δ} → Sub ρ̂ → Sub (t̂ail ρ̂)
tail ρ = record
  { function    = λ _ → _·_ ρ ∘ suc
  ; corresponds = λ _ → corresponds ρ ∘ suc
  }

-- The head of a nonempty substitution.

head : ∀ {Γ Δ σ} {ρ̂ : Γ ▻ σ ⇨̂ Δ} (ρ : Sub ρ̂) → Δ ⊢ σ / tail ρ
head ρ = zero /∋ ρ

head-lemma : ∀ {Γ Δ σ} {ρ̂ : Γ ▻ σ ⇨̂ Δ}
             (ρ : Sub ρ̂) → ĥead ρ̂ ≡ ⟦ head ρ ⟧
head-lemma ρ = zero /∋-lemma ρ

-- Some congruence lemmas.

ε⇨-cong : ∀ {Δ₁ Δ₂} → Δ₁ ≡ Δ₂ → ε⇨ {Δ = Δ₁} ≅ ε⇨ {Δ = Δ₂}
ε⇨-cong P.refl = H.refl

▻⇨-cong :
  ∀ {Γ₁ Δ₁ σ₁} {ρ̂₁ : Γ₁ ⇨̂ Δ₁} {ρ₁ : Sub ρ̂₁} {t₁ : Δ₁ ⊢ σ₁ / ρ₁}
    {Γ₂ Δ₂ σ₂} {ρ̂₂ : Γ₂ ⇨̂ Δ₂} {ρ₂ : Sub ρ̂₂} {t₂ : Δ₂ ⊢ σ₂ / ρ₂} →
  Γ₁ ≡ Γ₂ → Δ₁ ≡ Δ₂ → σ₁ ≅ σ₂ → ρ̂₁ ≅ ρ̂₂ → ρ₁ ≅ ρ₂ → t₁ ≅ t₂ →
  _▻⇨_ {σ = σ₁} ρ₁ t₁ ≅ _▻⇨_ {σ = σ₂} ρ₂ t₂
▻⇨-cong P.refl P.refl H.refl H.refl H.refl H.refl = H.refl

⟦⟧⇨-cong : ∀ {Γ₁ Δ₁} {ρ̂₁ : Γ₁ ⇨̂ Δ₁} {ρ₁ : Sub ρ̂₁}
             {Γ₂ Δ₂} {ρ̂₂ : Γ₂ ⇨̂ Δ₂} {ρ₂ : Sub ρ̂₂} →
           ρ̂₁ ≅ ρ̂₂ → ⟦ ρ₁ ⟧⇨ ≅ ⟦ ρ₂ ⟧⇨
⟦⟧⇨-cong = id

/-cong : ∀ {Γ₁ Δ₁ σ₁} {ρ̂₁ : Γ₁ ⇨̂ Δ₁} {ρ₁ : Sub ρ̂₁}
           {Γ₂ Δ₂ σ₂} {ρ̂₂ : Γ₂ ⇨̂ Δ₂} {ρ₂ : Sub ρ̂₂} →
         Γ₁ ≡ Γ₂ → Δ₁ ≡ Δ₂ → σ₁ ≅ σ₂ → ρ̂₁ ≅ ρ̂₂ → σ₁ / ρ₁ ≅ σ₂ / ρ₂
/-cong P.refl P.refl H.refl H.refl = H.refl

/∋-cong : ∀ {Γ₁ Δ₁ σ₁} {x₁ : Γ₁ ∋ σ₁} {ρ̂₁ : Γ₁ ⇨̂ Δ₁} {ρ₁ : Sub ρ̂₁}
            {Γ₂ Δ₂ σ₂} {x₂ : Γ₂ ∋ σ₂} {ρ̂₂ : Γ₂ ⇨̂ Δ₂} {ρ₂ : Sub ρ̂₂} →
          Γ₁ ≡ Γ₂ → Δ₁ ≡ Δ₂ → σ₁ ≅ σ₂ → x₁ ≅ x₂ → ρ̂₁ ≅ ρ̂₂ → ρ₁ ≅ ρ₂ →
          x₁ /∋ ρ₁ ≅ x₂ /∋ ρ₂
/∋-cong P.refl P.refl H.refl H.refl H.refl H.refl = H.refl

tail-cong : ∀ {Γ₁ Δ₁ σ₁} {ρ̂₁ : Γ₁ ▻ σ₁ ⇨̂ Δ₁} {ρ₁ : Sub ρ̂₁}
              {Γ₂ Δ₂ σ₂} {ρ̂₂ : Γ₂ ▻ σ₂ ⇨̂ Δ₂} {ρ₂ : Sub ρ̂₂} →
            Γ₁ ≡ Γ₂ → Δ₁ ≡ Δ₂ → σ₁ ≅ σ₂ → ρ̂₁ ≅ ρ̂₂ → ρ₁ ≅ ρ₂ →
            tail ρ₁ ≅ tail ρ₂
tail-cong P.refl P.refl H.refl H.refl H.refl = H.refl

head-cong : ∀ {Γ₁ Δ₁ σ₁} {ρ̂₁ : Γ₁ ▻ σ₁ ⇨̂ Δ₁} {ρ₁ : Sub ρ̂₁}
              {Γ₂ Δ₂ σ₂} {ρ̂₂ : Γ₂ ▻ σ₂ ⇨̂ Δ₂} {ρ₂ : Sub ρ̂₂} →
            Γ₁ ≡ Γ₂ → Δ₁ ≡ Δ₂ → σ₁ ≅ σ₂ → ρ̂₁ ≅ ρ̂₂ → ρ₁ ≅ ρ₂ →
            head ρ₁ ≅ head ρ₂
head-cong P.refl P.refl H.refl H.refl H.refl = H.refl

abstract

  -- Some eta-laws, based on the assumption of extensionality.

  private
   module Dummy (ext : P.Extensionality (e ⊔ u) (suc (e ⊔ u ⊔ t))) where

    -- Various derived instances of extensionality.

    private
      ext₁ : P.Extensionality (e ⊔ u) (e ⊔ u ⊔ t)
      ext₁ = P.extensionality-for-lower-levels
               (e ⊔ u) (suc (e ⊔ u ⊔ t)) ext

      ext₁′ : P.Extensionality (e ⊔ u) t
      ext₁′ = P.extensionality-for-lower-levels
                (e ⊔ u) (suc (e ⊔ u ⊔ t)) ext

      ext₂ : H.Extensionality (e ⊔ u) (e ⊔ u)
      ext₂ = H.≡-ext-to-≅-ext $
               P.extensionality-for-lower-levels
                 (e ⊔ u) (suc (e ⊔ u ⊔ t)) ext

      ext₂′ : P.Extensionality (e ⊔ u) (suc e)
      ext₂′ = P.extensionality-for-lower-levels
                (e ⊔ u) (suc (e ⊔ u ⊔ t)) ext

      ext₂″ : H.Extensionality (e ⊔ u) e
      ext₂″ = H.≡-ext-to-≅-ext $
                P.extensionality-for-lower-levels
                  (e ⊔ u) (suc (e ⊔ u ⊔ t)) ext

      ext₃ : H.Extensionality (e ⊔ u) (e ⊔ u ⊔ t)
      ext₃ = H.≡-ext-to-≅-ext $
               P.extensionality-for-lower-levels
                 (e ⊔ u) (suc (e ⊔ u ⊔ t)) ext

      ext₃′ : H.Extensionality (e ⊔ u) t
      ext₃′ = H.≡-ext-to-≅-ext $
                P.extensionality-for-lower-levels
                  (e ⊔ u) (suc (e ⊔ u ⊔ t)) ext

      -- Some congruence lemmas.

      ≡-cong : ∀ {ℓ} {A B : Set ℓ} {x₁ y₁ : A} {x₂ y₂ : B} →
               A ≡ B → x₁ ≅ x₂ → y₁ ≅ y₂ → (x₁ ≡ y₁) ≡ (x₂ ≡ y₂)
      ≡-cong P.refl H.refl H.refl = P.refl

      $-cong : ∀ {a b}
                 {A₁ : Set a} {B₁ : A₁ → Set b}
                 {f₁ : (x : A₁) → B₁ x} {x₁ : A₁}
                 {A₂ : Set a} {B₂ : A₂ → Set b}
                 {f₂ : (x : A₂) → B₂ x} {x₂ : A₂} →
               A₁ ≡ A₂ → B₁ ≅ B₂ → f₁ ≅ f₂ → x₁ ≅ x₂ → f₁ x₁ ≅ f₂ x₂
      $-cong P.refl H.refl H.refl H.refl = H.refl

      -- Proof irrelevance.

      irrelevance : ∀ {ℓ} {A B : Set ℓ} {x₁ x₂ : A} {y₁ y₂ : B}
                      {p : x₁ ≡ x₂} {q : y₁ ≡ y₂} →
                    A ≡ B → x₁ ≅ y₁ → x₂ ≅ y₂ → p ≅ q
      irrelevance {p = p} {q = q} P.refl H.refl H.refl with p | q
      ... | P.refl | P.refl = H.refl

    -- Eta in empty contexts.

    ηε : ∀ {Δ} {ρ̂ : ε ⇨̂ Δ} (ρ : Sub ρ̂) → ρ ≡ ε⇨ {Δ = Δ}
    ηε {ρ̂ = ρ̂} ρ = H.≅-to-≡ $
      function-corresponds-cong
        P.refl P.refl H.refl (H.≡-to-≅ lemma₁) lemma₂
      where
      lemma₁ : [_⟶_].function ρ ≡ [_⟶_].function ε⇨
      lemma₁ = ext₁ λ _ → ext₁′ λ ()

      lemma₂ : [_⟶_].corresponds ρ ≅ [_⟶_].corresponds ε⇨
      lemma₂ = ext₂ (λ _ → P.∀-extensionality ext₂′
                             (λ x → x /̂∋ ρ̂ ≡ ⟦ x /∋ ρ ⟧)
                             (λ x → x /̂∋ ε̂ ≡ ⟦ x /∋ ε⇨ ⟧)
                             λ ())
                    (λ _ → ext₂″ (λ ()) λ ())

    -- Eta in non-empty contexts.

    η▻ : ∀ {Γ Δ σ} {ρ̂ : Γ ▻ σ ⇨̂ Δ} (ρ : Sub ρ̂) →
         ρ ≅ _▻⇨_ {σ = σ} (tail ρ) (head ρ)
    η▻ {Γ} {Δ} {σ} {ρ̂} ρ =
      function-corresponds-cong
        P.refl P.refl (H.≡-to-≅ lemma₀) lemma₁ lemma₂
      where
      lemma₀ : ρ̂ ≡ t̂ail ρ̂ ▻̂ ⟦ head ρ ⟧
      lemma₀ = begin
        ρ̂                    ≡⟨ P.refl ⟩
        t̂ail ρ̂ ▻̂ ĥead ρ̂      ≡⟨ H.≅-to-≡ $ ▻̂-cong P.refl P.refl H.refl H.refl
                                                  (H.≡-to-≅ $ head-lemma ρ) ⟩
        t̂ail ρ̂ ▻̂ ⟦ head ρ ⟧  ∎
        where open P.≡-Reasoning

      lemma₁′ : ∀ {υ} (x : Γ ▻ σ ∋ υ) →
                x /∋ ρ ≅ x /∋ _▻⇨_ {σ = σ} (tail ρ) (head ρ)
      lemma₁′ zero    = H.refl
      lemma₁′ (suc x) = H.refl

      lemma₁ : [_⟶_].function ρ ≅
               [_⟶_].function (_▻⇨_ {σ = σ} (tail ρ) (head ρ))
      lemma₁ =
        ext₃ (λ τ → P.cong (λ ρ → Γ ▻ σ ∋ τ → Δ ⊢ τ /̂ ρ) lemma₀)
             (λ τ → ext₃′ (λ _ → P.cong (λ ρ → Δ ⊢ τ /̂ ρ) lemma₀)
                          lemma₁′)

      lemma₂′ :
        ∀ {τ} (x : Γ ▻ σ ∋ τ) →
        (x /̂∋ ρ̂                     ≡ ⟦ x /∋ ρ ⟧) ≡
        (x /̂∋ (t̂ail ρ̂ ▻̂ ⟦ head ρ ⟧) ≡ ⟦ x /∋ (tail ρ ▻⇨ head ρ) ⟧)
      lemma₂′ {τ} x = ≡-cong
        (P.cong (λ ρ̂ → Value Δ (τ /̂ ρ̂)) lemma₀)
        (/̂∋-cong P.refl P.refl H.refl
                 (H.refl {x = x}) (H.≡-to-≅ lemma₀))
        (⟦⟧-cong P.refl
           (/̂-cong P.refl P.refl (H.refl {x = τ}) (H.≡-to-≅ lemma₀))
           ($-cong P.refl
              (H.≡-to-≅ $ P.cong (λ ρ̂ → λ _ → Δ ⊢ τ /̂ ρ̂) lemma₀)
              ($-cong P.refl
                 (H.≡-to-≅ $ ext λ τ →
                    P.cong (λ ρ̂ → _ → Δ ⊢ τ /̂ ρ̂) lemma₀)
                 lemma₁
                 (H.refl {x = τ}))
              (H.refl {x = x})))

      lemma₂″ : ∀ {τ} (x : Γ ▻ σ ∋ τ) →
                x /∋-lemma ρ ≅
                x /∋-lemma _▻⇨_ {σ = σ} (tail ρ) (head ρ)
      lemma₂″ (suc x) = H.refl
      lemma₂″ zero    =
        irrelevance P.refl (H.≡-to-≅ $ head-lemma ρ) H.refl

      lemma₂ : [_⟶_].corresponds ρ ≅
               [_⟶_].corresponds (_▻⇨_ {σ = σ} (tail ρ) (head ρ))
      lemma₂ = ext₂ (λ τ → P.∀-extensionality ext₂′
                             (λ x → x /̂∋ ρ̂ ≡ ⟦ x /∋ ρ ⟧)
                             (λ x → x /̂∋ (t̂ail ρ̂ ▻̂ ⟦ head ρ ⟧) ≡
                                    ⟦ x /∋ (tail ρ ▻⇨ head ρ) ⟧)
                             lemma₂′)
                    (λ τ → ext₂″ lemma₂′ lemma₂″)

  open Dummy public

abstract

  -- Two substitutions are equal if their indices are equal and their
  -- projections are pairwise equal (assuming extensionality).

  extensionality :
    P.Extensionality (e ⊔ u) (suc (e ⊔ u ⊔ t)) →
    ∀ {Γ Δ₁ Δ₂} {ρ̂₁ : Γ ⇨̂ Δ₁} {ρ̂₂ : Γ ⇨̂ Δ₂}
    (ρ₁ : Sub ρ̂₁) (ρ₂ : Sub ρ̂₂) →
    Δ₁ ≡ Δ₂ → ρ̂₁ ≅ ρ̂₂ → (∀ {σ} (x : Γ ∋ σ) → x /∋ ρ₁ ≅ x /∋ ρ₂) →
    ρ₁ ≅ ρ₂
  extensionality ext {ε} ρ₁ ρ₂ P.refl H.refl hyp = begin
    ρ₁  ≡⟨ ηε ext ρ₁ ⟩
    ε⇨  ≡⟨ P.sym $ ηε ext ρ₂ ⟩
    ρ₂  ∎
    where open H.≅-Reasoning
  extensionality ext {Γ ▻ σ} ρ₁ ρ₂ P.refl H.refl hyp = begin
    ρ₁                  ≅⟨ η▻ ext ρ₁ ⟩
    tail ρ₁ ▻⇨ head ρ₁  ≅⟨ ▻⇨-cong P.refl P.refl H.refl H.refl
                                   (extensionality ext (tail ρ₁) (tail ρ₂)
                                                   P.refl H.refl (hyp ∘ suc))
                                   (hyp zero) ⟩
    tail ρ₂ ▻⇨ head ρ₂  ≅⟨ H.sym $ η▻ ext ρ₂ ⟩
    ρ₂                  ∎
    where open H.≅-Reasoning
