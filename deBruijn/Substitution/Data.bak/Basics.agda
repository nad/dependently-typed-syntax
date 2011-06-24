------------------------------------------------------------------------
-- Substitutions containing certain term-like things
------------------------------------------------------------------------

{-# OPTIONS --universe-polymorphism #-}

open import Universe
import deBruijn.Context as Context

module deBruijn.Substitution.Data.Basics
  {u e t} {Uni : Universe u e} (T : Context.Term-like Uni t) where

open import Function using () renaming (_∘_ to _⊚_)
open import Level using (_⊔_)
open import Relation.Binary.HeterogeneousEquality as H using (_≅_)
open import Relation.Binary.PropositionalEquality as P using (_≡_)

open Context Uni
open Term-like T

mutual

  infixr 4 _⇨_
  infixl 5 _▻_

  -- Substitutions.

  data _⇨_ : Ctxt → Ctxt → Set (u ⊔ e ⊔ t) where
    ε   : ∀ {Δ} → ε ⇨ Δ
    _▻_ : ∀ {Γ Δ σ} (ρ : Γ ⇨ Δ) (t : Δ ⊢ σ / ρ) → Γ ▻ σ ⇨ Δ

  -- Application of substitutions to types.

  infixl 8 _/_

  _/_ : ∀ {Γ Δ} → Type Γ → Γ ⇨ Δ → Type Δ
  σ / ρ = σ /̂ ⟦ ρ ⟧⇨

  -- Interpretation of substitutions: context morphisms.

  ⟦_⟧⇨ : ∀ {Γ Δ} → Γ ⇨ Δ → Γ ⇨̂ Δ
  ⟦ ε     ⟧⇨ = _
  ⟦ ρ ▻ t ⟧⇨ = ⟦ ρ ⟧⇨ ▻̂ ⟦ t ⟧

-- The tail of a nonempty substitution.

tail : ∀ {Γ Δ σ} → Γ ▻ σ ⇨ Δ → Γ ⇨ Δ
tail (ρ ▻ t) = ρ

tail-lemma : ∀ {Γ Δ σ} (ρ : Γ ▻ σ ⇨ Δ) → t̂ail ⟦ ρ ⟧⇨ ≡ ⟦ tail ρ ⟧⇨
tail-lemma (ρ ▻ t) = P.refl

-- The head of a nonempty substitution.

head : ∀ {Γ Δ σ} (ρ : Γ ▻ σ ⇨ Δ) → Δ ⊢ σ / tail ρ
head (ρ ▻ t) = t

head-lemma : ∀ {Γ Δ σ} (ρ : Γ ▻ σ ⇨ Δ) → ĥead ⟦ ρ ⟧⇨ ≅ ⟦ head ρ ⟧
head-lemma (ρ ▻ t) = H.refl

-- Application of substitutions to variables.

infixl 8 _/∋_ _/∋-lemma_

_/∋_ : ∀ {Γ Δ σ} → Γ ∋ σ → (ρ : Γ ⇨ Δ) → Δ ⊢ σ / ρ
zero  /∋ (ρ ▻ y) = y
suc x /∋ (ρ ▻ y) = x /∋ ρ

abstract

  _/∋-lemma_ : ∀ {Γ Δ σ} (x : Γ ∋ σ) (ρ : Γ ⇨ Δ) →
               x /̂∋ ⟦ ρ ⟧⇨ ≡ ⟦ x /∋ ρ ⟧
  zero  /∋-lemma (ρ ▻ y) = P.refl
  suc x /∋-lemma (ρ ▻ y) = x /∋-lemma ρ

-- Some congruence lemmas.

ε⇨-cong : ∀ {Δ₁ Δ₂} → Δ₁ ≡ Δ₂ → _⇨_.ε {Δ = Δ₁} ≅ _⇨_.ε {Δ = Δ₂}
ε⇨-cong P.refl = H.refl

▻⇨-cong : ∀ {Γ₁ Δ₁ σ₁} {ρ₁ : Γ₁ ⇨ Δ₁} {t₁ : Δ₁ ⊢ σ₁ / ρ₁}
            {Γ₂ Δ₂ σ₂} {ρ₂ : Γ₂ ⇨ Δ₂} {t₂ : Δ₂ ⊢ σ₂ / ρ₂} →
          Γ₁ ≡ Γ₂ → Δ₁ ≡ Δ₂ → σ₁ ≅ σ₂ → ρ₁ ≅ ρ₂ → t₁ ≅ t₂ →
          _⇨_._▻_ {σ = σ₁} ρ₁ t₁ ≅ _⇨_._▻_ {σ = σ₂} ρ₂ t₂
▻⇨-cong P.refl P.refl H.refl H.refl H.refl = H.refl

/-cong : ∀ {Γ₁ Δ₁ σ₁} {ρ₁ : Γ₁ ⇨ Δ₁}
           {Γ₂ Δ₂ σ₂} {ρ₂ : Γ₂ ⇨ Δ₂} →
         Γ₁ ≡ Γ₂ → Δ₁ ≡ Δ₂ → σ₁ ≅ σ₂ → ρ₁ ≅ ρ₂ → σ₁ / ρ₁ ≅ σ₂ / ρ₂
/-cong P.refl P.refl H.refl H.refl = H.refl

⟦⟧⇨-cong : ∀ {Γ₁ Δ₁} {ρ₁ : Γ₁ ⇨ Δ₁}
             {Γ₂ Δ₂} {ρ₂ : Γ₂ ⇨ Δ₂} →
           Γ₁ ≡ Γ₂ → Δ₁ ≡ Δ₂ → ρ₁ ≅ ρ₂ → ⟦ ρ₁ ⟧⇨ ≅ ⟦ ρ₂ ⟧⇨
⟦⟧⇨-cong P.refl P.refl H.refl = H.refl

tail-cong : ∀ {Γ₁ Δ₁ σ₁} {ρ₁ : Γ₁ ▻ σ₁ ⇨ Δ₁}
              {Γ₂ Δ₂ σ₂} {ρ₂ : Γ₂ ▻ σ₂ ⇨ Δ₂} →
            Γ₁ ≡ Γ₂ → Δ₁ ≡ Δ₂ → σ₁ ≅ σ₂ → ρ₁ ≅ ρ₂ → tail ρ₁ ≅ tail ρ₂
tail-cong P.refl P.refl H.refl H.refl = H.refl

head-cong : ∀ {Γ₁ Δ₁ σ₁} {ρ₁ : Γ₁ ▻ σ₁ ⇨ Δ₁}
              {Γ₂ Δ₂ σ₂} {ρ₂ : Γ₂ ▻ σ₂ ⇨ Δ₂} →
            Γ₁ ≡ Γ₂ → Δ₁ ≡ Δ₂ → σ₁ ≅ σ₂ → ρ₁ ≅ ρ₂ → head ρ₁ ≅ head ρ₂
head-cong P.refl P.refl H.refl H.refl = H.refl

/∋-cong : ∀ {Γ₁ Δ₁ σ₁} {x₁ : Γ₁ ∋ σ₁} {ρ₁ : Γ₁ ⇨ Δ₁}
            {Γ₂ Δ₂ σ₂} {x₂ : Γ₂ ∋ σ₂} {ρ₂ : Γ₂ ⇨ Δ₂} →
          Γ₁ ≡ Γ₂ → Δ₁ ≡ Δ₂ → σ₁ ≅ σ₂ → x₁ ≅ x₂ → ρ₁ ≅ ρ₂ →
          x₁ /∋ ρ₁ ≅ x₂ /∋ ρ₂
/∋-cong P.refl P.refl H.refl H.refl H.refl = H.refl

abstract

  -- Two substitutions are equal if their indices are equal and their
  -- projections are pairwise equal.

  extensionality :
    ∀ {Γ Δ₁ Δ₂} (ρ₁ : Γ ⇨ Δ₁) (ρ₂ : Γ ⇨ Δ₂) →
    Δ₁ ≡ Δ₂ → (∀ {σ} (x : Γ ∋ σ) → x /∋ ρ₁ ≅ x /∋ ρ₂) → ρ₁ ≅ ρ₂
  extensionality ε         ε         P.refl hyp = H.refl
  extensionality (ρ₁ ▻ t₁) (ρ₂ ▻ t₂) P.refl hyp =
    ▻⇨-cong P.refl P.refl H.refl
            (extensionality ρ₁ ρ₂ P.refl (hyp ⊚ suc))
            (hyp zero)
