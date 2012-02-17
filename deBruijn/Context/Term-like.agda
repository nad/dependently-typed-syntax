------------------------------------------------------------------------
-- An abstraction: term-like things
------------------------------------------------------------------------

open import Universe

module deBruijn.Context.Term-like
  {i u e} (Uni : Indexed-universe i u e) where

open import Data.Product
import deBruijn.Context.Basics          as Basics
import deBruijn.Context.Extension.Right as Right
open import Function
open import Level using (_⊔_)
open import Relation.Binary using (Setoid)
open import Relation.Binary.PropositionalEquality as P using (_≡_)

open Basics Uni
open Right  Uni
open P.≡-Reasoning

------------------------------------------------------------------------
-- Term-like things

record Term-like ℓ : Set (i ⊔ u ⊔ e ⊔ Level.suc ℓ) where
  infix 4 _⊢_
  field
    _⊢_ : (Γ : Ctxt) → Type Γ → Set ℓ
    ⟦_⟧ : ∀ {Γ σ} → Γ ⊢ σ → Value Γ σ

  -- Equality of term-like things.

  record [⊢] : Set (i ⊔ u ⊔ e ⊔ ℓ) where
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
             {Γ Δ : Ctxt} (ρ̂ : Γ ⇨̂ Δ) : Set (i ⊔ u ⊔ e ⊔ t₁ ⊔ t₂) where
  constructor _,_

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

-- Weakening of variables (the successor function).

weaken∋ : ∀ {Γ} {σ : Type Γ} → [ Var ⟶ Var ] ŵk[ σ ]
weaken∋ = record
  { function    = λ _ → suc
  ; corresponds = λ _ _ → P.refl
  }

weaken∋[_] : ∀ {Γ} (σ : Type Γ) → [ Var ⟶ Var ] ŵk[ σ ]
weaken∋[ _ ] = weaken∋

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
  function : ∀ τ → Γ ++⁺ Γ⁺ ▻ σ ∋ τ →
             Δ ++⁺ (Γ⁺ ▻ σ) /̂⁺ ρ̂ ∋ τ /̂ ρ̂ ↑̂⁺ (Γ⁺ ▻ σ)
  function ._ zero    = zero
  function ._ (suc x) = suc (lift f Γ⁺ · x)

  abstract
    corr : ∀ τ (x : Γ ++⁺ Γ⁺ ▻ σ ∋ τ) →
           lookup x /̂Val ρ̂ ↑̂⁺ (Γ⁺ ▻ σ) ≅-Value lookup (function _ x)
    corr ._ zero    = P.refl
    corr ._ (suc x) = begin
      [ lookup x /̂Val ρ̂ ↑̂⁺ Γ⁺ /̂Val ŵk  ]  ≡⟨ /̂Val-cong (corresponds (lift f Γ⁺) x) P.refl ⟩
      [ lookup (lift f Γ⁺ · x) /̂Val ŵk ]  ≡⟨ P.refl ⟩
      [ lookup (suc (lift f Γ⁺ · x))   ]  ∎

------------------------------------------------------------------------
-- Equality for the functions introduced above

-- Note that the definition of equality does not take the
-- "corresponds" proof into account.

record [⟶] {t₁ t₂} (T₁ : Term-like t₁) (T₂ : Term-like t₂)
           : Set (i ⊔ u ⊔ e ⊔ t₁ ⊔ t₂) where
  constructor [_]
  open Term-like T₁ renaming (_⊢_ to _⊢₁_)
  open Term-like T₂ renaming (_⊢_ to _⊢₂_)
  field
    {Γ Δ} : Ctxt
    {ρ̂}   : Γ ⇨̂ Δ
    f     : ∀ σ → Γ ⊢₁ σ → Δ ⊢₂ σ /̂ ρ̂

[_]⟶ : ∀ {t₁ t₂} {T₁ : Term-like t₁} {T₂ : Term-like t₂}
         {Γ Δ} {ρ̂ : Γ ⇨̂ Δ} →
       [ T₁ ⟶ T₂ ] ρ̂ → [⟶] T₁ T₂
[ f ]⟶ = [ [_⟶_].function f ]

-- Equality is defined as a record type to make it possible to infer
-- ρ₁ and ρ₂ from a value of type ρ₁ ≅-⟶ ρ₂.

infix 4 _≅-⟶_

record _≅-⟶_
  {t₁ t₂} {T₁ : Term-like t₁} {T₂ : Term-like t₂}
  {Γ₁ Δ₁ : Ctxt} {ρ̂₁ : Γ₁ ⇨̂ Δ₁} (f₁ : [ T₁ ⟶ T₂ ] ρ̂₁)
  {Γ₂ Δ₂ : Ctxt} {ρ̂₂ : Γ₂ ⇨̂ Δ₂} (f₂ : [ T₁ ⟶ T₂ ] ρ̂₂)
  : Set (i ⊔ u ⊔ e ⊔ t₁ ⊔ t₂) where
  constructor [_]
  field
    [f₁]⟶≡[f₂]⟶ : [ f₁ ]⟶ ≡ [ f₂ ]⟶

-- Some equational reasoning combinators.

module ≅-⟶-Reasoning
  {t₁ t₂} {T₁ : Term-like t₁} {T₂ : Term-like t₂}
  where

  infix  2 _∎-⟶
  infixr 2 _≅-⟶⟨_⟩_

  _≅-⟶⟨_⟩_ : ∀ {Γ₁ Δ₁} {ρ̂₁ : Γ₁ ⇨̂ Δ₁}
               {Γ₂ Δ₂} {ρ̂₂ : Γ₂ ⇨̂ Δ₂}
               {Γ₃ Δ₃} {ρ̂₃ : Γ₃ ⇨̂ Δ₃}
             (f₁ : [ T₁ ⟶ T₂ ] ρ̂₁) {f₂ : [ T₁ ⟶ T₂ ] ρ̂₂}
                                   {f₃ : [ T₁ ⟶ T₂ ] ρ̂₃} →
             f₁ ≅-⟶ f₂ → f₂ ≅-⟶ f₃ → f₁ ≅-⟶ f₃
  _ ≅-⟶⟨ [ f₁≅f₂ ] ⟩ [ f₂≅f₃ ] = [ P.trans f₁≅f₂ f₂≅f₃ ]

  _∎-⟶ : ∀ {Γ Δ} {ρ̂ : Γ ⇨̂ Δ} (f : [ T₁ ⟶ T₂ ] ρ̂) → f ≅-⟶ f
  _ ∎-⟶ = [ P.refl ]

  sym-⟶ : ∀ {Γ₁ Δ₁} {ρ̂₁ : Γ₁ ⇨̂ Δ₁} {f₁ : [ T₁ ⟶ T₂ ] ρ̂₁}
            {Γ₂ Δ₂} {ρ̂₂ : Γ₂ ⇨̂ Δ₂} {f₂ : [ T₁ ⟶ T₂ ] ρ̂₂} →
          f₁ ≅-⟶ f₂ → f₂ ≅-⟶ f₁
  sym-⟶ [ f₁≅f₂ ] = [ P.sym f₁≅f₂ ]

open ≅-⟶-Reasoning public

-- A setoid for [_⟶_].

[_⟶_]-setoid : ∀ {t₁ t₂} (T₁ : Term-like t₁) (T₂ : Term-like t₂) →
             ∀ {Γ Δ} → Γ ⇨̂ Δ → Setoid _ _
[ T₁ ⟶ T₂ ]-setoid ρ̂ = record
  { Carrier       = [ T₁ ⟶ T₂ ] ρ̂
  ; _≈_           = λ f₁ f₂ → f₁ ≅-⟶ f₂
  ; isEquivalence = record
    { refl  = _ ∎-⟶
    ; sym   = sym-⟶
    ; trans = λ p q → _ ≅-⟶⟨ p ⟩ q
    }
  }

-- A congruence lemma.

·-cong :
  ∀ {t₁ t₂} {T₁ : Term-like t₁} {T₂ : Term-like t₂} →
  let open Term-like T₁ renaming (_⊢_ to _⊢₁_; _≅-⊢_ to _≅-⊢₁_)
      open Term-like T₂ renaming (_⊢_ to _⊢₂_; _≅-⊢_ to _≅-⊢₂_) in
  ∀ {Γ₁ Δ₁ σ₁} {ρ̂₁ : Γ₁ ⇨̂ Δ₁} {f₁ : [ T₁ ⟶ T₂ ] ρ̂₁} {t₁ : Γ₁ ⊢₁ σ₁}
    {Γ₂ Δ₂ σ₂} {ρ̂₂ : Γ₂ ⇨̂ Δ₂} {f₂ : [ T₁ ⟶ T₂ ] ρ̂₂} {t₂ : Γ₂ ⊢₁ σ₂} →
  f₁ ≅-⟶ f₂ → t₁ ≅-⊢₁ t₂ → f₁ · t₁ ≅-⊢₂ f₂ · t₂
·-cong {f₁ = _ , _} {f₂ = ._ , _} [ P.refl ] P.refl = P.refl

abstract

  -- Two variants of extensional equality (assuming ordinary
  -- extensional equality).

  extensional-equality₁ :
    ∀ {t₁ t₂} {T₁ : Term-like t₁} {T₂ : Term-like t₂} →
    let open Term-like T₁ renaming (_⊢_ to _⊢₁_)
        open Term-like T₂ renaming (_≅-⊢_ to _≅-⊢₂_)
    in
    P.Extensionality (i ⊔ u ⊔ e ⊔ t₁) (t₁ ⊔ t₂) →
    ∀ {Γ Δ₁} {ρ̂₁ : Γ ⇨̂ Δ₁} {f₁ : [ T₁ ⟶ T₂ ] ρ̂₁}
        {Δ₂} {ρ̂₂ : Γ ⇨̂ Δ₂} {f₂ : [ T₁ ⟶ T₂ ] ρ̂₂} →
    ρ̂₁ ≅-⇨̂ ρ̂₂ → (∀ {σ} (t : Γ ⊢₁ σ) → f₁ · t ≅-⊢₂ f₂ · t) →
    f₁ ≅-⟶ f₂
  extensional-equality₁ {t₁} {t₂} {T₂ = T₂} ext P.refl f₁≅f₂ =
    [ P.cong [_] (ext₁ λ σ → ext₂ λ t → ≅-⊢₂-⇒-≡ (f₁≅f₂ t)) ]
    where
    open Term-like T₂ using () renaming (≅-⊢-⇒-≡ to ≅-⊢₂-⇒-≡)

    ext₁ : P.Extensionality (i ⊔ u ⊔ e) (t₁ ⊔ t₂)
    ext₁ = P.extensionality-for-lower-levels t₁ Level.zero ext

    ext₂ : P.Extensionality t₁ t₂
    ext₂ = P.extensionality-for-lower-levels (i ⊔ u ⊔ e) t₁ ext

  extensional-equality₂ :
    ∀ {t₁ t₂} {T₁ : Term-like t₁} {T₂ : Term-like t₂} →
    let open Term-like T₁ renaming (_≅-⊢_ to _≅-⊢₁_; _⊢_ to _⊢₁_)
        open Term-like T₂ renaming (_≅-⊢_ to _≅-⊢₂_)
    in
    P.Extensionality (i ⊔ u ⊔ e ⊔ t₁) (t₁ ⊔ t₂) →
    ∀ {Γ₁ Δ₁} {ρ̂₁ : Γ₁ ⇨̂ Δ₁} {f₁ : [ T₁ ⟶ T₂ ] ρ̂₁}
      {Γ₂ Δ₂} {ρ̂₂ : Γ₂ ⇨̂ Δ₂} {f₂ : [ T₁ ⟶ T₂ ] ρ̂₂} →
    ρ̂₁ ≅-⇨̂ ρ̂₂ →
    (∀ {σ₁} {t₁ : Γ₁ ⊢₁ σ₁} {σ₂} {t₂ : Γ₂ ⊢₁ σ₂} →
       t₁ ≅-⊢₁ t₂ → f₁ · t₁ ≅-⊢₂ f₂ · t₂) →
    f₁ ≅-⟶ f₂
  extensional-equality₂ {T₁ = T₁} ext P.refl f₁≅f₂ =
    extensional-equality₁ ext P.refl (λ t → f₁≅f₂ (P.refl {x = [ t ]}))
    where open Term-like T₁ using ([_])

  -- lift ∘ weaken∋ sort of commutes with a lifted version of itself.

  lift-weaken∋-lift-lift-weaken∋ :
    ∀ {Γ} σ Γ⁺ τ Γ⁺⁺ {υ} (x : Γ ++⁺ Γ⁺ ++⁺ Γ⁺⁺ ∋ υ) →
    lift weaken∋[ τ /̂ ŵk ↑̂⁺ Γ⁺ ] (Γ⁺⁺ /̂⁺ ŵk ↑̂⁺ Γ⁺) ·
         (lift (lift weaken∋[ σ ] Γ⁺) Γ⁺⁺ · x) ≅-∋
    lift (lift weaken∋[ σ ] (Γ⁺ ▻ τ)) (Γ⁺⁺ /̂⁺ ŵk) ·
         (lift weaken∋[ τ ] Γ⁺⁺ · x)
  lift-weaken∋-lift-lift-weaken∋ σ Γ⁺ τ ε         x       = P.refl
  lift-weaken∋-lift-lift-weaken∋ σ Γ⁺ τ (Γ⁺⁺ ▻ υ) zero    =
    zero-cong (/̂-↑̂⁺-/̂-ŵk-↑̂⁺ τ (ŵk ↑̂⁺ Γ⁺) Γ⁺⁺ υ)
  lift-weaken∋-lift-lift-weaken∋ σ Γ⁺ τ (Γ⁺⁺ ▻ υ) (suc x) =
    suc-cong (/̂-↑̂⁺-/̂-ŵk-↑̂⁺ τ (ŵk ↑̂⁺ Γ⁺) Γ⁺⁺ υ)
             (lift-weaken∋-lift-lift-weaken∋ σ Γ⁺ τ Γ⁺⁺ x)

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

-- [id] and _[∘]_ preserve equality.

[id]-cong :
  ∀ {t} {T : Term-like t} {Γ₁ Γ₂} →
  Γ₁ ≅-Ctxt Γ₂ → [id] {T = T} {Γ = Γ₁} ≅-⟶ [id] {T = T} {Γ = Γ₂}
[id]-cong P.refl = [ P.refl ]

private
 module Dummy {t₁ t₂} {T₁ : Term-like t₁} {T₂ : Term-like t₂} where

  [∘]-cong : ∀ {t₃} {T₃ : Term-like t₃}
               {Γ₁ Δ₁ Ε₁} {ρ̂₁₁ : Γ₁ ⇨̂ Δ₁} {ρ̂₂₁ : Δ₁ ⇨̂ Ε₁}
               {f₁₁ : [ T₁ ⟶ T₂ ] ρ̂₁₁} {f₂₁ : [ T₂ ⟶ T₃ ] ρ̂₂₁}
               {Γ₂ Δ₂ Ε₂} {ρ̂₁₂ : Γ₂ ⇨̂ Δ₂} {ρ̂₂₂ : Δ₂ ⇨̂ Ε₂}
               {f₁₂ : [ T₁ ⟶ T₂ ] ρ̂₁₂} {f₂₂ : [ T₂ ⟶ T₃ ] ρ̂₂₂} →
             f₁₁ ≅-⟶ f₁₂ → f₂₁ ≅-⟶ f₂₂ → f₂₁ [∘] f₁₁ ≅-⟶ f₂₂ [∘] f₁₂
  [∘]-cong {f₁₁ = _ , _} {f₂₁ = _ , _} {f₁₂ = ._ , _} {f₂₂ = ._ , _}
           [ P.refl ] [ P.refl ] = [ P.refl ]

  -- [id] is a left and right identity of _[∘]_, which is associative.

  [id]-[∘] : ∀ {Γ Δ} {ρ̂ : Γ ⇨̂ Δ}
             (f : [ T₁ ⟶ T₂ ] ρ̂) → [id] [∘] f ≅-⟶ f
  [id]-[∘] f = [ P.refl ]

  [∘]-[id] : ∀ {Γ Δ} {ρ̂ : Γ ⇨̂ Δ}
             (f : [ T₁ ⟶ T₂ ] ρ̂) → f [∘] [id] ≅-⟶ f
  [∘]-[id] f = [ P.refl ]

  [∘]-[∘] :
    ∀ {t₃ t₄} {T₃ : Term-like t₃} {T₄ : Term-like t₄}
      {Γ Δ Ε Ζ} {ρ̂₁ : Γ ⇨̂ Δ} {ρ̂₂ : Δ ⇨̂ Ε} {ρ̂₃ : Ε ⇨̂ Ζ}
    (f₃ : [ T₃ ⟶ T₄ ] ρ̂₃) (f₂ : [ T₂ ⟶ T₃ ] ρ̂₂)
    (f₁ : [ T₁ ⟶ T₂ ] ρ̂₁) →
    f₃ [∘] (f₂ [∘] f₁) ≅-⟶ (f₃ [∘] f₂) [∘] f₁
  [∘]-[∘] f₃ f₂ f₁ = [ P.refl ]

open Dummy public
