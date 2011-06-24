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
open import Relation.Binary.HeterogeneousEquality as H using (_≅_)
open import Relation.Binary.PropositionalEquality as P using (_≡_)

open Context Uni

------------------------------------------------------------------------
-- Term-like things

record Term-like ℓ : Set (u ⊔ e ⊔ Level.suc ℓ) where
  infix 4 _⊢_
  field
    _⊢_ : (Γ : Ctxt) → Type Γ → Set ℓ
    ⟦_⟧ : ∀ {Γ σ} → Γ ⊢ σ → Value Γ σ

  -- A congruence lemma.

  ⟦⟧-cong : ∀ {Γ₁ σ₁} {t₁ : Γ₁ ⊢ σ₁}
              {Γ₂ σ₂} {t₂ : Γ₂ ⊢ σ₂} →
            Γ₁ ≡ Γ₂ → σ₁ ≅ σ₂ → t₁ ≅ t₂ → ⟦ t₁ ⟧ ≅ ⟦ t₂ ⟧
  ⟦⟧-cong P.refl H.refl H.refl = H.refl

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
    corresponds : ∀ σ (t : Γ ⊢₁ σ) → ⟦ t ⟧₁ /Val ρ̂ ≡ ⟦ function σ t ⟧₂

-- Functions which do not change the context or type.

[_⟶⁼_] : ∀ {t₁ t₂} → Term-like t₁ → Term-like t₂ → Set _
[ T₁ ⟶⁼ T₂ ] = ∀ {Γ} → [ T₁ ⟶ T₂ ] (îd {Γ = Γ})

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
  ⟦ t ⟧₁ /Val ρ̂ ≡ ⟦ f · t ⟧₂
corresponds f = [_⟶_].corresponds f _

-- Weakening of variables (the successor function).

weaken∋ : ∀ {Γ} {σ : Type Γ} → [ Var ⟶ Var ] (ŵk {σ = σ})
weaken∋ = record
  { function    = λ _ → suc
  ; corresponds = λ _ _ → P.refl
  }

-- Lifts a function on variables, f, to a function which leaves a
-- prefix of the context unchanged and otherwise behaves as f.

lift : ∀ {Γ Δ} {ρ̂ : Γ ⇨̂ Δ} →
       [ Var ⟶ Var ] ρ̂ → ∀ Γ⁺ → [ Var ⟶ Var ] (ρ̂ ↑̂⁺ Γ⁺)
lift             f ε        = f
lift {Γ} {Δ} {ρ̂} f (Γ⁺ ▻ σ) = record
  { function    = function
  ; corresponds = corr
  }
  where
  function : ∀ τ → Γ ++ Γ⁺ ▻ σ ∋ τ →
             Δ ++ (Γ⁺ ▻ σ) /̂⁺ ρ̂ ∋ τ /̂ ρ̂ ↑̂⁺ (Γ⁺ ▻ σ)
  function ._ zero    = zero
  function ._ (suc x) = suc (lift f Γ⁺ · x)

  abstract
    corr : ∀ τ (x : Γ ++ Γ⁺ ▻ σ ∋ τ) →
           lookup x /Val ρ̂ ↑̂⁺ (Γ⁺ ▻ σ) ≡ lookup (function _ x)
    corr ._ zero    = P.refl
    corr ._ (suc x) = begin
      lookup x /Val ρ̂ ↑̂⁺ Γ⁺ /Val ŵk   ≅⟨ /Val-cong P.refl P.refl H.refl
                                           (H.≡-to-≅ $ corresponds (lift f Γ⁺) x)
                                           (H.refl {x = ŵk}) ⟩
      lookup (lift f Γ⁺ · x) /Val ŵk  ≡⟨ P.refl ⟩
      lookup (suc (lift f Γ⁺ · x))    ∎
      where open P.≡-Reasoning

-- Some congruence lemmas.

function-corresponds-cong :
  ∀ {t₁ t₂} {T₁ : Term-like t₁} {T₂ : Term-like t₂} →
  let open Term-like T₁ renaming (_⊢_ to _⊢₁_; ⟦_⟧ to ⟦_⟧₁)
      open Term-like T₂ renaming (_⊢_ to _⊢₂_; ⟦_⟧ to ⟦_⟧₂) in
  ∀ {Γ₁ Δ₁} {ρ̂₁ : Γ₁ ⇨̂ Δ₁}
    {function₁ : ∀ σ → Γ₁ ⊢₁ σ → Δ₁ ⊢₂ σ /̂ ρ̂₁}
    {corresponds₁ : ∀ σ (t : Γ₁ ⊢₁ σ) →
                    ⟦ t ⟧₁ /Val ρ̂₁ ≡ ⟦ function₁ σ t ⟧₂}
    {Γ₂ Δ₂} {ρ̂₂ : Γ₂ ⇨̂ Δ₂}
    {function₂ : ∀ σ → Γ₂ ⊢₁ σ → Δ₂ ⊢₂ σ /̂ ρ̂₂}
    {corresponds₂ : ∀ σ (t : Γ₂ ⊢₁ σ) →
                    ⟦ t ⟧₁ /Val ρ̂₂ ≡ ⟦ function₂ σ t ⟧₂} →
  Γ₁ ≡ Γ₂ → Δ₁ ≡ Δ₂ → ρ̂₁ ≅ ρ̂₂ →
  function₁ ≅ function₂ → corresponds₁ ≅ corresponds₂ →
  _≅_ {A = [ T₁ ⟶ T₂ ] ρ̂₁}
      (record { function = function₁; corresponds = corresponds₁ })
      {B = [ T₁ ⟶ T₂ ] ρ̂₂}
      (record { function = function₂; corresponds = corresponds₂ })
function-corresponds-cong P.refl P.refl H.refl H.refl H.refl = H.refl

·-cong :
  ∀ {t₁ t₂} {T₁ : Term-like t₁} {T₂ : Term-like t₂} →
  let open Term-like T₁ renaming (_⊢_ to _⊢₁_)
      open Term-like T₂ renaming (_⊢_ to _⊢₂_) in
  ∀ {Γ₁ Δ₁ σ₁} {ρ̂₁ : Γ₁ ⇨̂ Δ₁} {f₁ : [ T₁ ⟶ T₂ ] ρ̂₁} {t₁ : Γ₁ ⊢₁ σ₁}
    {Γ₂ Δ₂ σ₂} {ρ̂₂ : Γ₂ ⇨̂ Δ₂} {f₂ : [ T₁ ⟶ T₂ ] ρ̂₂} {t₂ : Γ₂ ⊢₁ σ₂} →
  Γ₁ ≡ Γ₂ → Δ₁ ≡ Δ₂ → σ₁ ≅ σ₂ → ρ̂₁ ≅ ρ̂₂ → f₁ ≅ f₂ → t₁ ≅ t₂ →
  f₁ · t₁ ≅ f₂ · t₂
·-cong P.refl P.refl H.refl H.refl H.refl H.refl = H.refl

abstract

  -- lift ∘ weaken∋ sort of commutes with a lifted version of itself.

  lift-weaken∋-lift-lift-weaken∋ :
    ∀ {Γ} σ Γ⁺ τ Γ⁺⁺ {υ} (x : Γ ++ Γ⁺ ++ Γ⁺⁺ ∋ υ) →
    lift (weaken∋ {σ = τ /̂ ŵk ↑̂⁺ Γ⁺}) (Γ⁺⁺ /̂⁺ ŵk ↑̂⁺ Γ⁺) ·
         (lift (lift (weaken∋ {σ = σ}) Γ⁺) Γ⁺⁺ · x) ≅
    lift (lift (weaken∋ {σ = σ}) (Γ⁺ ▻ τ)) (Γ⁺⁺ /̂⁺ ŵk) ·
         (lift (weaken∋ {σ = τ}) Γ⁺⁺ · x)
  lift-weaken∋-lift-lift-weaken∋ σ Γ⁺ τ ε         x    = H.refl
  lift-weaken∋-lift-lift-weaken∋ σ Γ⁺ τ (Γ⁺⁺ ▻ υ) zero =
    zero-cong (▻-/̂-++-/̂⁺-/̂⁺-ŵk τ (ŵk ↑̂⁺ Γ⁺) Γ⁺⁺)
              (/̂-↑̂⁺-/̂-ŵk-↑̂⁺ τ (ŵk ↑̂⁺ Γ⁺) Γ⁺⁺ υ)
  lift-weaken∋-lift-lift-weaken∋ σ Γ⁺ τ (Γ⁺⁺ ▻ υ) (suc {τ = τ′} x) =
    suc-cong (▻-/̂-++-/̂⁺-/̂⁺-ŵk τ (ŵk ↑̂⁺ Γ⁺) Γ⁺⁺)
             (/̂-↑̂⁺-/̂-ŵk-↑̂⁺ τ (ŵk ↑̂⁺ Γ⁺) Γ⁺⁺ υ)
             (/̂-↑̂⁺-/̂-ŵk-↑̂⁺ τ (ŵk ↑̂⁺ Γ⁺) Γ⁺⁺ τ′)
             (lift-weaken∋-lift-lift-weaken∋ σ Γ⁺ τ Γ⁺⁺ x)

------------------------------------------------------------------------
-- Term-like t and [_⟶_] form a category

-- At least if we ignore the context morphism index.

-- Identity.

[id] : ∀ {t} {T : Term-like t} {Γ} → [ T ⟶ T ] (îd {Γ = Γ})
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
    corr : ∀ σ (t : _ ⊢₁ σ) → ⟦ t ⟧₁ /Val ρ̂₁ ∘̂ ρ̂₂ ≡ ⟦ f · (g · t) ⟧₃
    corr = λ σ t → begin
      ⟦ t ⟧₁ /Val ρ̂₁ ∘̂ ρ̂₂  ≅⟨ /Val-cong P.refl P.refl H.refl
                                        (H.≡-to-≅ $ corresponds g t) H.refl ⟩
      ⟦ g · t ⟧₂ /Val ρ̂₂   ≡⟨ corresponds f (g · t) ⟩
      ⟦ f · (g · t) ⟧₃     ∎

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
               (f : [ T₁ ⟶ T₂ ] ρ̂) → [id] [∘] f ≡ f
    [id]-[∘] f = H.≅-to-≡ $
      function-corresponds-cong P.refl P.refl H.refl H.refl
        (H.≡-to-≅ $ ext₁ λ _ → ext₂ λ _ → P.proof-irrelevance _ _)

    [∘]-[id] : ∀ {Γ Δ} {ρ̂ : Γ ⇨̂ Δ}
               (f : [ T₁ ⟶ T₂ ] ρ̂) → f [∘] [id] ≡ f
    [∘]-[id] f = H.≅-to-≡ $
      function-corresponds-cong P.refl P.refl H.refl H.refl
        (H.≡-to-≅ $ ext₁ λ _ → ext₂ λ _ → P.proof-irrelevance _ _)

    [∘]-[∘] :
      ∀ {t₃ t₄} {T₃ : Term-like t₃} {T₄ : Term-like t₄}
        {Γ Δ Ε Ζ} {ρ̂₁ : Γ ⇨̂ Δ} {ρ̂₂ : Δ ⇨̂ Ε} {ρ̂₃ : Ε ⇨̂ Ζ}
      (f₃ : [ T₃ ⟶ T₄ ] ρ̂₃) (f₂ : [ T₂ ⟶ T₃ ] ρ̂₂)
      (f₁ : [ T₁ ⟶ T₂ ] ρ̂₁) →
      f₃ [∘] (f₂ [∘] f₁) ≡ (f₃ [∘] f₂) [∘] f₁
    [∘]-[∘] f₃ f₂ f₁ = H.≅-to-≡ $
      function-corresponds-cong P.refl P.refl H.refl H.refl
        (H.≡-to-≅ $ ext₁ λ _ → ext₂ λ _ → P.proof-irrelevance _ _)

  open Dummy public
