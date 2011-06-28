------------------------------------------------------------------------
-- Term-like things
------------------------------------------------------------------------

{-# OPTIONS --universe-polymorphism #-}

open import Universe

module deBruijn.TermLike {u e} (Uni : Universe u e) where

open import Data.Product
import deBruijn.Context as Context
open import Function
open import Level using (_⊔_)
open import Relation.Binary.PropositionalEquality as P using (_≡_)

open Context Uni
open P.≡-Reasoning

------------------------------------------------------------------------
-- Term-like things

record Term-like ℓ : Set (u ⊔ e ⊔ Level.suc ℓ) where
  infix 4 _⊢_
  field
    _⊢_ : (Γ : Ctxt) → Type Γ → Set ℓ
    ⟦_⟧ : ∀ {Γ σ} → Γ ⊢ σ → Value Γ σ

  -- Equality of term-like things.

  record [⊢] : Set (u ⊔ e ⊔ ℓ) where
    constructor [_]
    field
      {Γ} : Ctxt
      {σ} : Type Γ
      t   : Γ ⊢ σ

  infix 4 _≅-⊢_

  _≅-⊢_ : ∀ {Γ₁ σ₁} (t₁ : Γ₁ ⊢ σ₁)
            {Γ₂ σ₂} (t₂ : Γ₂ ⊢ σ₂) → Set _
  t₁ ≅-⊢ t₂ = [⊢].[_] t₁ ≡ [ t₂ ]

  ≅-⊢-⇒-≡ : ∀ {Γ σ} {t₁ t₂ : Γ ⊢ σ} →
            t₁ ≅-⊢ t₂ → t₁ ≡ t₂
  ≅-⊢-⇒-≡ P.refl = P.refl

  -- Certain uses of substitutivity can be removed.

  drop-subst-⊢ :
    ∀ {a} {A : Set a} {x₁ x₂ : A} {Γ}
    (f : A → Type Γ) {t} (eq : x₁ ≡ x₂) →
    P.subst (λ x → Γ ⊢ f x) eq t ≅-⊢ t
  drop-subst-⊢ f P.refl = P.refl

  -- A congruence lemma.

  ⟦⟧-cong : ∀ {Γ₁ σ₁} {t₁ : Γ₁ ⊢ σ₁}
              {Γ₂ σ₂} {t₂ : Γ₂ ⊢ σ₂} →
            t₁ ≅-⊢ t₂ → ⟦ t₁ ⟧ ≅-Value ⟦ t₂ ⟧
  ⟦⟧-cong P.refl = P.refl

-- Values are term-like.

Val : Term-like _
Val = record { _⊢_ = Value; ⟦_⟧ = id }

-- Variables are term-like.

Var : Term-like _
Var = record { _⊢_ = _∋_; ⟦_⟧ = lookup }

------------------------------------------------------------------------
-- Families of functions which, on the semantic side, correspond to
-- the application of a given context morphism

record [_⟶_] {t₁ t₂} (T₁ : Term-like t₁) (T₂ : Term-like t₂)
             {Γ Δ : Ctxt} (ρ̂ : Γ ⇨̂ Δ) : Set (u ⊔ e ⊔ t₁ ⊔ t₂) where
  open Term-like T₁ renaming (_⊢_ to _⊢₁_; ⟦_⟧ to ⟦_⟧₁)
  open Term-like T₂ renaming (_⊢_ to _⊢₂_; ⟦_⟧ to ⟦_⟧₂)
  field
    function    : ∀ σ → Γ ⊢₁ σ → Δ ⊢₂ σ /̂ ρ̂
    corresponds :
      ∀ σ (t : Γ ⊢₁ σ) → ⟦ t ⟧₁ /̂Val ρ̂ ≅-Value ⟦ function σ t ⟧₂

-- Functions which do not change the context or type.

[_⟶⁼_] : ∀ {t₁ t₂} → Term-like t₁ → Term-like t₂ → Set _
[ T₁ ⟶⁼ T₂ ] = ∀ {Γ} → [ T₁ ⟶ T₂ ] îd[ Γ ]

-- Projections. (The fields above have explicit σ's to avoid some
-- problems; the projections below have implicit σ's.)

infixl 9 _·_

_·_ : ∀ {t₁ t₂} {T₁ : Term-like t₁} {T₂ : Term-like t₂} →
      let open Term-like T₁ renaming (_⊢_ to _⊢₁_)
          open Term-like T₂ renaming (_⊢_ to _⊢₂_) in
      ∀ {Γ Δ σ} {ρ̂ : Γ ⇨̂ Δ} →
      [ T₁ ⟶ T₂ ] ρ̂ → Γ ⊢₁ σ → Δ ⊢₂ σ /̂ ρ̂
_·_ f = [_⟶_].function f _

corresponds :
  ∀ {t₁ t₂} {T₁ : Term-like t₁} {T₂ : Term-like t₂} →
  let open Term-like T₁ renaming (_⊢_ to _⊢₁_; ⟦_⟧ to ⟦_⟧₁)
      open Term-like T₂ renaming (⟦_⟧ to ⟦_⟧₂) in
  ∀ {Γ Δ : Ctxt} {ρ̂ : Γ ⇨̂ Δ} {σ}
  (f : [ T₁ ⟶ T₂ ] ρ̂) (t : Γ ⊢₁ σ) →
  ⟦ t ⟧₁ /̂Val ρ̂ ≅-Value ⟦ f · t ⟧₂
corresponds f = [_⟶_].corresponds f _

-- Equality.

record [⟶] {t₁ t₂} (T₁ : Term-like t₁) (T₂ : Term-like t₂)
           : Set (u ⊔ e ⊔ t₁ ⊔ t₂) where
  constructor [_]
  field
    {Γ Δ} : Ctxt
    {ρ̂}   : Γ ⇨̂ Δ
    f     : [ T₁ ⟶ T₂ ] ρ̂

infix 4 _≅-⟶_

_≅-⟶_ :
  ∀ {t₁ t₂} {T₁ : Term-like t₁} {T₂ : Term-like t₂} →
  let open Term-like T₁ renaming (_⊢_ to _⊢₁_; ⟦_⟧ to ⟦_⟧₁)
      open Term-like T₂ renaming (⟦_⟧ to ⟦_⟧₂) in
  ∀ {Γ₁ Δ₁ : Ctxt} {ρ̂₁ : Γ₁ ⇨̂ Δ₁} (f₁ : [ T₁ ⟶ T₂ ] ρ̂₁)
    {Γ₂ Δ₂ : Ctxt} {ρ̂₂ : Γ₂ ⇨̂ Δ₂} (f₂ : [ T₁ ⟶ T₂ ] ρ̂₂) → Set _
f₁ ≅-⟶ f₂ = [⟶].[_] f₁ ≡ [ f₂ ]

-- Weakening of variables (the successor function).

weaken∋ : ∀ {Γ} {σ : Type Γ} → [ Var ⟶ Var ] ŵk[ σ ]
weaken∋ = record
  { function    = λ _ → suc
  ; corresponds = λ _ _ → P.refl
  }

weaken∋[_] : ∀ {Γ} (σ : Type Γ) → [ Var ⟶ Var ] ŵk[ σ ]
weaken∋[ _ ] = weaken∋

-- Some congruence lemmas.

record [function] {t₁ t₂} (T₁ : Term-like t₁) (T₂ : Term-like t₂)
                  : Set (u ⊔ e ⊔ t₁ ⊔ t₂) where
  constructor [_]
  open Term-like T₁ renaming (_⊢_ to _⊢₁_)
  open Term-like T₂ renaming (_⊢_ to _⊢₂_)
  field
    {Γ Δ} : Ctxt
    {ρ̂}   : Γ ⇨̂ Δ
    f     : ∀ σ → Γ ⊢₁ σ → Δ ⊢₂ σ /̂ ρ̂

record [corresponds] {t₁ t₂} (T₁ : Term-like t₁) (T₂ : Term-like t₂)
                     : Set (u ⊔ e ⊔ t₁ ⊔ t₂) where
  constructor [_]
  open Term-like T₁ renaming (_⊢_ to _⊢₁_; ⟦_⟧ to ⟦_⟧₁)
  open Term-like T₂ renaming (_⊢_ to _⊢₂_; ⟦_⟧ to ⟦_⟧₂)
  field
    {Γ Δ} : Ctxt
    {ρ̂}   : Γ ⇨̂ Δ
    {f}   : ∀ σ → Γ ⊢₁ σ → Δ ⊢₂ σ /̂ ρ̂
    corr  : ∀ σ (t : Γ ⊢₁ σ) → ⟦ t ⟧₁ /̂Val ρ̂ ≅-Value ⟦ f σ t ⟧₂

function-corresponds-cong :
  ∀ {t₁ t₂} {T₁ : Term-like t₁} {T₂ : Term-like t₂} →
  let open Term-like T₁ renaming (_⊢_ to _⊢₁_; ⟦_⟧ to ⟦_⟧₁)
      open Term-like T₂ renaming (_⊢_ to _⊢₂_; ⟦_⟧ to ⟦_⟧₂) in
  ∀ {Γ₁ Δ₁} {ρ̂₁ : Γ₁ ⇨̂ Δ₁}
    {function₁ : ∀ σ → Γ₁ ⊢₁ σ → Δ₁ ⊢₂ σ /̂ ρ̂₁}
    {corresponds₁ : ∀ σ (t : Γ₁ ⊢₁ σ) →
                    ⟦ t ⟧₁ /̂Val ρ̂₁ ≅-Value ⟦ function₁ σ t ⟧₂}
    {Γ₂ Δ₂} {ρ̂₂ : Γ₂ ⇨̂ Δ₂}
    {function₂ : ∀ σ → Γ₂ ⊢₁ σ → Δ₂ ⊢₂ σ /̂ ρ̂₂}
    {corresponds₂ : ∀ σ (t : Γ₂ ⊢₁ σ) →
                    ⟦ t ⟧₁ /̂Val ρ̂₂ ≅-Value ⟦ function₂ σ t ⟧₂} →
  ρ̂₁ ≅-⇨̂ ρ̂₂ →
  [function].[_] {T₁ = T₁} {T₂ = T₂} function₁ ≡
             [_]                     function₂ →
  [corresponds].[_] {T₁ = T₁} {T₂ = T₂} corresponds₁ ≡
                [_]                     corresponds₂ →
  _≅-⟶_ {T₁ = T₁} {T₂ = T₂}
        (record { function = function₁; corresponds = corresponds₁ })
        (record { function = function₂; corresponds = corresponds₂ })
function-corresponds-cong P.refl P.refl P.refl = P.refl

·-cong :
  ∀ {t₁ t₂} {T₁ : Term-like t₁} {T₂ : Term-like t₂} →
  let open Term-like T₁ renaming (_⊢_ to _⊢₁_; _≅-⊢_ to _≅-⊢₁_)
      open Term-like T₂ renaming (_⊢_ to _⊢₂_; _≅-⊢_ to _≅-⊢₂_) in
  ∀ {Γ₁ Δ₁ σ₁} {ρ̂₁ : Γ₁ ⇨̂ Δ₁} {f₁ : [ T₁ ⟶ T₂ ] ρ̂₁} {t₁ : Γ₁ ⊢₁ σ₁}
    {Γ₂ Δ₂ σ₂} {ρ̂₂ : Γ₂ ⇨̂ Δ₂} {f₂ : [ T₁ ⟶ T₂ ] ρ̂₂} {t₂ : Γ₂ ⊢₁ σ₂} →
  f₁ ≅-⟶ f₂ → t₁ ≅-⊢₁ t₂ → f₁ · t₁ ≅-⊢₂ f₂ · t₂
·-cong P.refl P.refl = P.refl

------------------------------------------------------------------------
-- Term-like t and [_⟶_] form a category

-- At least if we ignore the context morphism index.

-- Identity.

[id] : ∀ {t} {T : Term-like t} {Γ} → [ T ⟶ T ] îd[ Γ ]
[id] = record { function = λ _ → id; corresponds = λ _ _ → P.refl }

-- Composition.

infixl 9 _[∘]_

_[∘]_ : ∀ {t₁ t₂ t₃}
          {T₁ : Term-like t₁} {T₂ : Term-like t₂} {T₃ : Term-like t₃}
          {Γ Δ Ε} {ρ̂₁ : Γ ⇨̂ Δ} {ρ̂₂ : Δ ⇨̂ Ε} →
        [ T₂ ⟶ T₃ ] ρ̂₂ → [ T₁ ⟶ T₂ ] ρ̂₁ → [ T₁ ⟶ T₃ ] (ρ̂₁ ∘̂ ρ̂₂)
_[∘]_ {T₁ = T₁} {T₂} {T₃} {ρ̂₁ = ρ̂₁} {ρ̂₂} f g = record
  { function    = λ _ → _·_ f ∘ _·_ g
  ; corresponds = corr
  }
  where
  open P.≡-Reasoning
  open Term-like T₁ renaming (⟦_⟧ to ⟦_⟧₁; _⊢_ to _⊢₁_)
  open Term-like T₂ renaming (⟦_⟧ to ⟦_⟧₂)
  open Term-like T₃ renaming (⟦_⟧ to ⟦_⟧₃)

  abstract
    corr : ∀ σ (t : _ ⊢₁ σ) →
           ⟦ t ⟧₁ /̂Val ρ̂₁ ∘̂ ρ̂₂ ≅-Value ⟦ f · (g · t) ⟧₃
    corr = λ σ t → begin
      [ ⟦ t ⟧₁ /̂Val ρ̂₁ ∘̂ ρ̂₂ ]  ≡⟨ /̂Val-cong (corresponds g t) P.refl ⟩
      [ ⟦ g · t ⟧₂ /̂Val ρ̂₂  ]  ≡⟨ corresponds f (g · t) ⟩
      [ ⟦ f · (g · t) ⟧₃    ]  ∎

abstract

  -- If we assume extensionality, then [id] is a left and right
  -- identity of _[∘]_, which is associative.

  private
   module Dummy
     {t₁ t₂} {T₁ : Term-like t₁} {T₂ : Term-like t₂}
     (ext : P.Extensionality (u ⊔ e ⊔ t₁) (u ⊔ e ⊔ t₁))
     where

    -- Some derived instances of extensionality.

    private
      ext₁ : P.Extensionality (u ⊔ e) (u ⊔ e ⊔ t₁)
      ext₁ = P.extensionality-for-lower-levels t₁ Level.zero ext

      ext₂ : P.Extensionality t₁ (u ⊔ e)
      ext₂ = P.extensionality-for-lower-levels (u ⊔ e) t₁ ext

    -- The uses of P.proof-irrelevance below can probably be replaced
    -- by direct proofs if the definition of _[∘]_ is made fully
    -- transparent.

    [id]-[∘] : ∀ {Γ Δ} {ρ̂ : Γ ⇨̂ Δ}
               (f : [ T₁ ⟶ T₂ ] ρ̂) → [id] [∘] f ≅-⟶ f
    [id]-[∘] f =
      function-corresponds-cong P.refl P.refl
        (P.cong [_] (ext₁ λ _ → ext₂ λ _ → P.proof-irrelevance _ _))

    [∘]-[id] : ∀ {Γ Δ} {ρ̂ : Γ ⇨̂ Δ}
               (f : [ T₁ ⟶ T₂ ] ρ̂) → f [∘] [id] ≅-⟶ f
    [∘]-[id] f =
      function-corresponds-cong P.refl P.refl
        (P.cong [_] (ext₁ λ _ → ext₂ λ _ → P.proof-irrelevance _ _))

    [∘]-[∘] :
      ∀ {t₃ t₄} {T₃ : Term-like t₃} {T₄ : Term-like t₄}
        {Γ Δ Ε Ζ} {ρ̂₁ : Γ ⇨̂ Δ} {ρ̂₂ : Δ ⇨̂ Ε} {ρ̂₃ : Ε ⇨̂ Ζ}
      (f₃ : [ T₃ ⟶ T₄ ] ρ̂₃) (f₂ : [ T₂ ⟶ T₃ ] ρ̂₂)
      (f₁ : [ T₁ ⟶ T₂ ] ρ̂₁) →
      f₃ [∘] (f₂ [∘] f₁) ≅-⟶ (f₃ [∘] f₂) [∘] f₁
    [∘]-[∘] f₃ f₂ f₁ =
      function-corresponds-cong P.refl P.refl
        (P.cong [_] (ext₁ λ _ → ext₂ λ _ → P.proof-irrelevance _ _))

  open Dummy public
