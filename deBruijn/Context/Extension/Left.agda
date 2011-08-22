------------------------------------------------------------------------
-- Context extensions with the leftmost element in the outermost
-- position
------------------------------------------------------------------------

{-# OPTIONS --universe-polymorphism #-}

open import Universe

module deBruijn.Context.Extension.Left
  {i u e} (Uni : Indexed-universe i u e) where

import deBruijn.Context.Basics          as Basics
import deBruijn.Context.Extension.Right as Right
open import Function
open import Level using (_⊔_)
open import Relation.Binary.PropositionalEquality as P using (_≡_)

open Basics Uni
open Right  Uni
open P.≡-Reasoning

------------------------------------------------------------------------
-- Context extensions along with various operations making use of them

-- Context extensions.

infixr 5 _◅_

data Ctxt₊ (Γ : Ctxt) : Set (i ⊔ u ⊔ e) where
  ε   : Ctxt₊ Γ
  _◅_ : (σ : Type Γ) (Γ₊ : Ctxt₊ (Γ ▻ σ)) → Ctxt₊ Γ

-- A synonym.

ε₊[_] : (Γ : Ctxt) → Ctxt₊ Γ
ε₊[ _ ] = ε

-- Appends a context extension to a context.

infixl 5 _++₊_

_++₊_ : (Γ : Ctxt) → Ctxt₊ Γ → Ctxt
Γ ++₊ ε        = Γ
Γ ++₊ (σ ◅ Γ₊) = Γ ▻ σ ++₊ Γ₊

-- The following operations append a context extension to a context
-- extension.

infixl 5 _₊++₊_ _⁺++₊_

_₊++₊_ : ∀ {Γ} Γ₊ → Ctxt₊ (Γ ++₊ Γ₊) → Ctxt₊ Γ
ε        ₊++₊ Γ₊₊ = Γ₊₊
(σ ◅ Γ₊) ₊++₊ Γ₊₊ = σ ◅ (Γ₊ ₊++₊ Γ₊₊)

_⁺++₊_ : ∀ {Γ} Γ⁺ → Ctxt₊ (Γ ++⁺ Γ⁺) → Ctxt₊ Γ
ε      ⁺++₊ Γ₊ = Γ₊
Γ⁺ ▻ σ ⁺++₊ Γ₊ = Γ⁺ ⁺++₊ (σ ◅ Γ₊)

-- Application of context morphisms to context extensions.

infixl 8 _/̂₊_

_/̂₊_ : ∀ {Γ Δ} → Ctxt₊ Γ → Γ ⇨̂ Δ → Ctxt₊ Δ
ε        /̂₊ ρ̂ = ε
(σ ◅ Γ₊) /̂₊ ρ̂ = σ /̂ ρ̂ ◅ Γ₊ /̂₊ ρ̂ ↑̂

-- N-ary lifting of context morphisms.

infixl 10 _↑̂₊_

_↑̂₊_ : ∀ {Γ Δ} (ρ̂ : Γ ⇨̂ Δ) Γ₊ → Γ ++₊ Γ₊ ⇨̂ Δ ++₊ Γ₊ /̂₊ ρ̂
ρ̂ ↑̂₊ ε        = ρ̂
ρ̂ ↑̂₊ (σ ◅ Γ₊) = ρ̂ ↑̂ ↑̂₊ Γ₊

-- N-ary weakening.

ŵk₊ : ∀ {Γ} Γ₊ → Γ ⇨̂ Γ ++₊ Γ₊
ŵk₊ ε        = îd
ŵk₊ (σ ◅ Γ₊) = ŵk[ σ ] ∘̂ ŵk₊ Γ₊

------------------------------------------------------------------------
-- Equality

-- Equality of context extensions.

record [Ctxt₊] : Set (i ⊔ u ⊔ e) where
  constructor [_]
  field
    {Γ} : Ctxt
    Γ₊  : Ctxt₊ Γ

infix 4 _≅-Ctxt₊_

_≅-Ctxt₊_ : ∀ {Γ₁} (Γ₊₁ : Ctxt₊ Γ₁)
              {Γ₂} (Γ₊₂ : Ctxt₊ Γ₂) → Set _
Γ₊₁ ≅-Ctxt₊ Γ₊₂ = [Ctxt₊].[_] Γ₊₁ ≡ [ Γ₊₂ ]

≅-Ctxt₊-⇒-≡ : ∀ {Γ} {Γ₊₁ Γ₊₂ : Ctxt₊ Γ} →
              Γ₊₁ ≅-Ctxt₊ Γ₊₂ → Γ₊₁ ≡ Γ₊₂
≅-Ctxt₊-⇒-≡ P.refl = P.refl

-- Certain uses of substitutivity can be removed.

drop-subst-Ctxt₊ : ∀ {a} {A : Set a} {x₁ x₂}
                   (f : A → Ctxt) {Γ₊} (x₁≡x₂ : x₁ ≡ x₂) →
                   P.subst (λ x → Ctxt₊ (f x)) x₁≡x₂ Γ₊ ≅-Ctxt₊ Γ₊
drop-subst-Ctxt₊ f P.refl = P.refl

------------------------------------------------------------------------
-- Some congruences

ε₊-cong : ∀ {Γ₁ Γ₂} → Γ₁ ≅-Ctxt Γ₂ → ε₊[ Γ₁ ] ≅-Ctxt₊ ε₊[ Γ₂ ]
ε₊-cong P.refl = P.refl

◅-cong : ∀ {Γ₁ σ₁} {Γ₊₁ : Ctxt₊ (Γ₁ ▻ σ₁)}
           {Γ₂ σ₂} {Γ₊₂ : Ctxt₊ (Γ₂ ▻ σ₂)} →
         Γ₊₁ ≅-Ctxt₊ Γ₊₂ → σ₁ ◅ Γ₊₁ ≅-Ctxt₊ σ₂ ◅ Γ₊₂
◅-cong P.refl = P.refl

++₊-cong : ∀ {Γ₁} {Γ₊₁ : Ctxt₊ Γ₁} {Γ₂} {Γ₊₂ : Ctxt₊ Γ₂} →
           Γ₊₁ ≅-Ctxt₊ Γ₊₂ → Γ₁ ++₊ Γ₊₁ ≅-Ctxt Γ₂ ++₊ Γ₊₂
++₊-cong P.refl = P.refl

₊++₊-cong : ∀ {Γ₁ Γ₊₁} {Γ₊₊₁ : Ctxt₊ (Γ₁ ++₊ Γ₊₁)}
              {Γ₂ Γ₊₂} {Γ₊₊₂ : Ctxt₊ (Γ₂ ++₊ Γ₊₂)} →
            Γ₊₁ ≅-Ctxt₊ Γ₊₂ → Γ₊₊₁ ≅-Ctxt₊ Γ₊₊₂ →
            Γ₊₁ ₊++₊ Γ₊₊₁ ≅-Ctxt₊ Γ₊₂ ₊++₊ Γ₊₊₂
₊++₊-cong P.refl P.refl = P.refl

⁺++₊-cong : ∀ {Γ₁ Γ⁺₁} {Γ₊₁ : Ctxt₊ (Γ₁ ++⁺ Γ⁺₁)}
              {Γ₂ Γ⁺₂} {Γ₊₂ : Ctxt₊ (Γ₂ ++⁺ Γ⁺₂)} →
            Γ⁺₁ ≅-Ctxt⁺ Γ⁺₂ → Γ₊₁ ≅-Ctxt₊ Γ₊₂ →
            Γ⁺₁ ⁺++₊ Γ₊₁ ≅-Ctxt₊ Γ⁺₂ ⁺++₊ Γ₊₂
⁺++₊-cong P.refl P.refl = P.refl

/̂₊-cong : ∀ {Γ₁ Δ₁} {Γ₊₁ : Ctxt₊ Γ₁} {ρ̂₁ : Γ₁ ⇨̂ Δ₁}
            {Γ₂ Δ₂} {Γ₊₂ : Ctxt₊ Γ₂} {ρ̂₂ : Γ₂ ⇨̂ Δ₂} →
          Γ₊₁ ≅-Ctxt₊ Γ₊₂ → ρ̂₁ ≅-⇨̂ ρ̂₂ → Γ₊₁ /̂₊ ρ̂₁ ≅-Ctxt₊ Γ₊₂ /̂₊ ρ̂₂
/̂₊-cong P.refl P.refl = P.refl

↑̂₊-cong : ∀ {Γ₁ Δ₁} {ρ̂₁ : Γ₁ ⇨̂ Δ₁} {Γ₊₁ : Ctxt₊ Γ₁}
            {Γ₂ Δ₂} {ρ̂₂ : Γ₂ ⇨̂ Δ₂} {Γ₊₂ : Ctxt₊ Γ₂} →
          ρ̂₁ ≅-⇨̂ ρ̂₂ → Γ₊₁ ≅-Ctxt₊ Γ₊₂ → ρ̂₁ ↑̂₊ Γ₊₁ ≅-⇨̂ ρ̂₂ ↑̂₊ Γ₊₂
↑̂₊-cong P.refl P.refl = P.refl

ŵk₊-cong : ∀ {Γ₁} {Γ₊₁ : Ctxt₊ Γ₁} {Γ₂} {Γ₊₂ : Ctxt₊ Γ₂} →
           Γ₊₁ ≅-Ctxt₊ Γ₊₂ → ŵk₊ Γ₊₁ ≅-⇨̂ ŵk₊ Γ₊₂
ŵk₊-cong P.refl = P.refl

------------------------------------------------------------------------
-- Some properties

abstract

  -- Γ ++₊_ has at most one right identity.

  private

    ++₊-right-identity-unique′ :
      ∀ {Γ} Γ⁺ Γ₊ → Γ ≅-Ctxt Γ ++⁺ Γ⁺ ++₊ Γ₊ → Γ₊ ≅-Ctxt₊ ε₊[ Γ ++⁺ Γ⁺ ]
    ++₊-right-identity-unique′ Γ⁺ ε        _  = P.refl
    ++₊-right-identity-unique′ Γ⁺ (σ ◅ Γ₊) eq
      with ++₊-right-identity-unique′ (Γ⁺ ▻ σ) Γ₊ eq
    ++₊-right-identity-unique′ Γ⁺ (σ ◅ .ε) eq | P.refl
      with ++⁺-right-identity-unique (Γ⁺ ▻ σ) eq
    ... | ()

  ++₊-right-identity-unique :
    ∀ {Γ} Γ₊ → Γ ≅-Ctxt Γ ++₊ Γ₊ → Γ₊ ≅-Ctxt₊ ε₊[ Γ ]
  ++₊-right-identity-unique Γ₊ = ++₊-right-identity-unique′ ε Γ₊

  -- Γ ++₊_ is left cancellative.

  private

    cancel-++₊-left′ : ∀ {Γ} Γ⁺₁ Γ₊₁ Γ⁺₂ Γ₊₂ →
                       Γ ++⁺ Γ⁺₁ ++₊ Γ₊₁ ≅-Ctxt Γ ++⁺ Γ⁺₂ ++₊ Γ₊₂ →
                       Γ⁺₁ ⁺++₊ Γ₊₁ ≅-Ctxt₊ Γ⁺₂ ⁺++₊ Γ₊₂
    cancel-++₊-left′ Γ⁺₁ ε          Γ⁺₂ ε          eq = ⁺++₊-cong (cancel-++⁺-left Γ⁺₁ Γ⁺₂ eq) (ε₊-cong eq)
    cancel-++₊-left′ Γ⁺₁ (σ₁ ◅ Γ₊₁) Γ⁺₂ (σ₂ ◅ Γ₊₂) eq = cancel-++₊-left′ (Γ⁺₁ ▻ σ₁) Γ₊₁ (Γ⁺₂ ▻ σ₂) Γ₊₂ eq
    cancel-++₊-left′ Γ⁺₁ ε          Γ⁺₂ (σ₂ ◅ Γ₊₂) eq = cancel-++₊-left′  Γ⁺₁       ε   (Γ⁺₂ ▻ σ₂) Γ₊₂ eq
    cancel-++₊-left′ Γ⁺₁ (σ₁ ◅ Γ₊₁) Γ⁺₂ ε          eq = cancel-++₊-left′ (Γ⁺₁ ▻ σ₁) Γ₊₁  Γ⁺₂       ε   eq

  cancel-++₊-left : ∀ {Γ} (Γ₊₁ Γ₊₂ : Ctxt₊ Γ) →
                    Γ ++₊ Γ₊₁ ≅-Ctxt Γ ++₊ Γ₊₂ → Γ₊₁ ≅-Ctxt₊ Γ₊₂
  cancel-++₊-left Γ₊₁ Γ₊₂ = cancel-++₊-left′ ε Γ₊₁ ε Γ₊₂

  -- _++₊_/_₊++₊_ are associative.

  ++₊-++₊ : ∀ {Γ} Γ₊ Γ₊₊ → Γ ++₊ Γ₊ ++₊ Γ₊₊ ≅-Ctxt Γ ++₊ (Γ₊ ₊++₊ Γ₊₊)
  ++₊-++₊ ε        Γ₊₊ = P.refl
  ++₊-++₊ (σ ◅ Γ₊) Γ₊₊ = ++₊-++₊ Γ₊ Γ₊₊

  -- The identity substitution has no effect.

  /̂₊-îd : ∀ {Γ} (Γ₊ : Ctxt₊ Γ) → Γ₊ /̂₊ îd ≅-Ctxt₊ Γ₊
  /̂₊-îd ε        = P.refl
  /̂₊-îd (σ ◅ Γ₊) = ◅-cong (/̂₊-îd Γ₊)

  -- The n-ary lifting of the identity substitution is the identity
  -- substitution.

  îd-↑̂₊ : ∀ {Γ} (Γ₊ : Ctxt₊ Γ) → îd ↑̂₊ Γ₊ ≅-⇨̂ îd[ Γ ++₊ Γ₊ ]
  îd-↑̂₊ ε        = P.refl
  îd-↑̂₊ (σ ◅ Γ₊) = begin
    [ îd ↑̂ ↑̂₊ Γ₊ ]  ≡⟨ P.refl ⟩
    [ îd ↑̂₊ Γ₊   ]  ≡⟨ îd-↑̂₊ Γ₊ ⟩
    [ îd         ]  ∎

  -- The identity substitution has no effect even if lifted.

  /̂-îd-↑̂₊ : ∀ {Γ} Γ₊ (σ : Type (Γ ++₊ Γ₊)) → σ /̂ îd ↑̂₊ Γ₊ ≅-Type σ
  /̂-îd-↑̂₊ Γ₊ σ = begin
    [ σ /̂ îd ↑̂₊ Γ₊ ]  ≡⟨ /̂-cong (P.refl {x = [ σ ]}) (îd-↑̂₊ Γ₊) ⟩
    [ σ /̂ îd       ]  ≡⟨ P.refl ⟩
    [ σ            ]  ∎

  -- Applying two substitutions is equivalent to applying their
  -- composition.

  /̂₊-∘̂ : ∀ {Γ Δ Ε} Γ₊ (ρ̂₁ : Γ ⇨̂ Δ) (ρ̂₂ : Δ ⇨̂ Ε) →
         Γ₊ /̂₊ ρ̂₁ ∘̂ ρ̂₂ ≅-Ctxt₊ Γ₊ /̂₊ ρ̂₁ /̂₊ ρ̂₂
  /̂₊-∘̂ ε        ρ̂₁ ρ̂₂ = P.refl
  /̂₊-∘̂ (σ ◅ Γ₊) ρ̂₁ ρ̂₂ = ◅-cong (/̂₊-∘̂ Γ₊ (ρ̂₁ ↑̂) (ρ̂₂ ↑̂))

  -- _↑̂₊_ distributes over _∘̂_.

  ∘̂-↑̂₊ : ∀ {Γ Δ Ε} (ρ̂₁ : Γ ⇨̂ Δ) (ρ̂₂ : Δ ⇨̂ Ε) Γ₊ →
         (ρ̂₁ ∘̂ ρ̂₂) ↑̂₊ Γ₊ ≅-⇨̂ ρ̂₁ ↑̂₊ Γ₊ ∘̂ ρ̂₂ ↑̂₊ (Γ₊ /̂₊ ρ̂₁)
  ∘̂-↑̂₊ ρ̂₁ ρ̂₂ ε        = P.refl
  ∘̂-↑̂₊ ρ̂₁ ρ̂₂ (σ ◅ Γ₊) = begin
    [ (ρ̂₁ ∘̂ ρ̂₂) ↑̂ ↑̂₊ Γ₊                     ]  ≡⟨ P.refl ⟩
    [ (ρ̂₁ ↑̂ ∘̂ ρ̂₂ ↑̂) ↑̂₊ Γ₊                   ]  ≡⟨ ∘̂-↑̂₊ (ρ̂₁ ↑̂) (ρ̂₂ ↑̂) Γ₊ ⟩
    [ (ρ̂₁ ↑̂ ↑̂₊ Γ₊) ∘̂ (ρ̂₂ ↑̂ ↑̂₊ (Γ₊ /̂₊ ρ̂₁ ↑̂)) ]  ∎

  -- A corollary.

  /̂-↑̂₊-/̂-ŵk-↑̂₊ : ∀ {Γ Δ} σ (ρ̂ : Γ ⇨̂ Δ) (Γ₊ : Ctxt₊ Γ) τ →
                 τ /̂ ρ̂ ↑̂₊ Γ₊ /̂ ŵk[ σ /̂ ρ̂ ] ↑̂₊ (Γ₊ /̂₊ ρ̂) ≅-Type
                 τ /̂ ŵk[ σ ] ↑̂₊ Γ₊ /̂ ρ̂ ↑̂ ↑̂₊ (Γ₊ /̂₊ ŵk)
  /̂-↑̂₊-/̂-ŵk-↑̂₊ σ ρ̂ Γ₊ τ = /̂-cong (P.refl {x = [ τ ]}) (begin
    [ ρ̂ ↑̂₊ Γ₊ ∘̂ ŵk ↑̂₊ (Γ₊ /̂₊ ρ̂)         ]  ≡⟨ P.sym $ ∘̂-↑̂₊ ρ̂ ŵk Γ₊ ⟩
    [ (ρ̂ ∘̂ ŵk) ↑̂₊ Γ₊                    ]  ≡⟨ P.refl ⟩
    [ (ŵk[ σ ] ∘̂ ρ̂ ↑̂) ↑̂₊ Γ₊             ]  ≡⟨ ∘̂-↑̂₊ ŵk[ σ ] (ρ̂ ↑̂) Γ₊ ⟩
    [ ŵk[ σ ] ↑̂₊ Γ₊ ∘̂ ρ̂ ↑̂ ↑̂₊ (Γ₊ /̂₊ ŵk) ]  ∎)

  -- ŵk₊ commutes (modulo lifting) with arbitrary context morphisms.

  ∘̂-ŵk₊ : ∀ {Γ Δ} (ρ̂ : Γ ⇨̂ Δ) Γ₊ →
          ρ̂ ∘̂ ŵk₊ (Γ₊ /̂₊ ρ̂) ≅-⇨̂ ŵk₊ Γ₊ ∘̂ ρ̂ ↑̂₊ Γ₊
  ∘̂-ŵk₊ ρ̂ ε        = P.refl
  ∘̂-ŵk₊ ρ̂ (σ ◅ Γ₊) = begin
    [ ρ̂ ∘̂ ŵk ∘̂ ŵk₊ (Γ₊ /̂₊ ρ̂ ↑̂)         ]  ≡⟨ P.refl ⟩
    [ ŵk[ σ ] ∘̂ ρ̂ ↑̂ ∘̂ ŵk₊ (Γ₊ /̂₊ ρ̂ ↑̂)  ]  ≡⟨ ∘̂-cong (P.refl {x = [ ŵk ]}) (∘̂-ŵk₊ (ρ̂ ↑̂) Γ₊) ⟩
    [ ŵk ∘̂ ŵk₊ Γ₊ ∘̂ ρ̂ ↑̂ ↑̂₊ Γ₊          ]  ∎

  -- ŵk₊ is homomorphic with respect to _₊++₊_/_∘̂_.

  ŵk₊-₊++₊ : ∀ {Γ} (Γ₊ : Ctxt₊ Γ) (Γ₊₊ : Ctxt₊ (Γ ++₊ Γ₊)) →
             ŵk₊ (Γ₊ ₊++₊ Γ₊₊) ≅-⇨̂ ŵk₊ Γ₊ ∘̂ ŵk₊ Γ₊₊
  ŵk₊-₊++₊ ε        Γ₊₊ = P.refl
  ŵk₊-₊++₊ (σ ◅ Γ₊) Γ₊₊ = ∘̂-cong (P.refl {x = [ ŵk ]}) (ŵk₊-₊++₊ Γ₊ Γ₊₊)

  -- Two n-ary liftings can be merged into one.

  ↑̂₊-₊++₊ : ∀ {Γ Δ} (ρ̂ : Γ ⇨̂ Δ) Γ₊ Γ₊₊ →
            ρ̂ ↑̂₊ (Γ₊ ₊++₊ Γ₊₊) ≅-⇨̂ ρ̂ ↑̂₊ Γ₊ ↑̂₊ Γ₊₊
  ↑̂₊-₊++₊ ρ̂ ε        Γ₊₊ = P.refl
  ↑̂₊-₊++₊ ρ̂ (σ ◅ Γ₊) Γ₊₊ = ↑̂₊-₊++₊ (ρ̂ ↑̂) Γ₊ Γ₊₊

  -- _/̂₊_ distributes over _₊++₊_ (sort of).

  ++₊-₊++₊-/̂₊ :
    ∀ {Γ Δ} (ρ̂ : Γ ⇨̂ Δ) Γ₊ Γ₊₊ →
    Δ ++₊ (Γ₊ ₊++₊ Γ₊₊) /̂₊ ρ̂ ≅-Ctxt Δ ++₊ Γ₊ /̂₊ ρ̂ ++₊ Γ₊₊ /̂₊ ρ̂ ↑̂₊ Γ₊
  ++₊-₊++₊-/̂₊         ρ̂ ε        Γ₊₊ = P.refl
  ++₊-₊++₊-/̂₊ {Δ = Δ} ρ̂ (σ ◅ Γ₊) Γ₊₊ = ++₊-₊++₊-/̂₊ (ρ̂ ↑̂) Γ₊ Γ₊₊
