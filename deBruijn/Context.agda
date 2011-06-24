------------------------------------------------------------------------
-- Contexts, variables, substitutions, etc.
------------------------------------------------------------------------

{-# OPTIONS --universe-polymorphism #-}

-- Based on Conor McBride's "Outrageous but Meaningful Coincidences:
-- Dependent type-safe syntax and evaluation".

-- The contexts and variables are parametrised by a universe.

open import Universe

module deBruijn.Context {u e} (Uni : Universe u e) where

open Universe.Universe Uni

open import Data.Empty
open import Data.Product as Prod
open import Data.Unit
open import Function hiding (type-signature)
open import Level using (_⊔_; Lift)
open import Relation.Binary.PropositionalEquality as P using (_≡_)

open P.≡-Reasoning

------------------------------------------------------------------------
-- Contexts and "types"

mutual

  -- Contexts.

  infixl 5 _▻_

  data Ctxt : Set (u ⊔ e) where
    ε   : Ctxt
    _▻_ : (Γ : Ctxt) (σ : Type Γ) → Ctxt

  -- Semantic types: maps from environments to universe codes.

  Type : Ctxt → Set (u ⊔ e)
  Type Γ = Env Γ → U

  -- Interpretation of contexts: environments.

  Env : Ctxt → Set e
  Env ε       = Lift ⊤
  Env (Γ ▻ σ) = Σ (Env Γ) λ γ → El (σ γ)

-- Semantic values: maps from environments to universe values.

Value : (Γ : Ctxt) → Type Γ → Set _
Value Γ σ = (γ : Env Γ) → El (σ γ)

------------------------------------------------------------------------
-- Context morphisms

-- Context morphisms or "semantic substitutions": maps from
-- environments to environments. Note the arrow's direction.

infixr 4 _⇨̂_

_⇨̂_ : Ctxt → Ctxt → Set _
Γ ⇨̂ Δ = Env Δ → Env Γ

-- The identity morphism.

îd : ∀ {Γ} → Γ ⇨̂ Γ
îd = id

-- Reverse composition of context morphisms.

infixl 9 _∘̂_

_∘̂_ : ∀ {Γ Δ Ε} → Γ ⇨̂ Δ → Δ ⇨̂ Ε → Γ ⇨̂ Ε
σ ∘̂ ρ̂ = σ ∘ ρ̂

-- Application of context morphisms to types.

infixl 8 _/̂_

_/̂_ : ∀ {Γ Δ} → Type Γ → Γ ⇨̂ Δ → Type Δ
σ /̂ ρ̂ = σ ∘ ρ̂

-- Application of context morphisms to values.

infixl 8 _/̂Val_

_/̂Val_ : ∀ {Γ Δ σ} → Value Γ σ → (ρ̂ : Γ ⇨̂ Δ) → Value Δ (σ /̂ ρ̂)
v /̂Val ρ̂ = v ∘ ρ̂

-- Weakening.

ŵk : ∀ {Γ σ} → Γ ⇨̂ Γ ▻ σ
ŵk = proj₁

-- Empty context morphism.

ε̂ : ∀ {Δ} → ε ⇨̂ Δ
ε̂ = λ _ → _

-- Extends a context morphism with another value.

infixl 5 _▻̂_

_▻̂_ : ∀ {Γ Δ σ} (ρ̂ : Γ ⇨̂ Δ) → Value Δ (σ /̂ ρ̂) → Γ ▻ σ ⇨̂ Δ
_▻̂_ = <_,_>

-- A context morphism which only modifies the last "variable".

ŝub : ∀ {Γ σ} → Value Γ σ → Γ ▻ σ ⇨̂ Γ
ŝub v = îd ▻̂ v

-- The "tail" of a "nonempty" context morphism.

t̂ail : ∀ {Γ Δ σ} → Γ ▻ σ ⇨̂ Δ → Γ ⇨̂ Δ
t̂ail ρ̂ = ŵk ∘̂ ρ̂

-- The "head" of a "nonempty" context morphism.

ĥead : ∀ {Γ Δ σ} (ρ̂ : Γ ▻ σ ⇨̂ Δ) → Value Δ (σ /̂ t̂ail ρ̂)
ĥead ρ̂ = proj₂ ∘ ρ̂

-- Maps between types.

infixr 4 _⇨̂₁_

_⇨̂₁_ : ∀ {Γ} → Type Γ → Type Γ → Set _
σ ⇨̂₁ τ = ∀ {γ} → El (τ γ) → El (σ γ)

-- One can construct a context morphism between two non-empty contexts
-- by supplying two functions, one which turns the old tail into the
-- new one, and one which turns the old head into the new one.

infixl 10 _↑̂_

_↑̂_ : ∀ {Γ Δ σ τ} (ρ̂ : Γ ⇨̂ Δ) → σ /̂ ρ̂ ⇨̂₁ τ → Γ ▻ σ ⇨̂ Δ ▻ τ
_↑̂_ = Prod.map

-- Lifting.

infix 10 _↑̂

_↑̂ : ∀ {Γ Δ σ} (ρ̂ : Γ ⇨̂ Δ) → Γ ▻ σ ⇨̂ Δ ▻ σ /̂ ρ̂
ρ̂ ↑̂ = ρ̂ ↑̂ id

------------------------------------------------------------------------
-- Variables

-- Variables (de Bruijn indices).

infix 4 _∋_

data _∋_ : (Γ : Ctxt) → Type Γ → Set (u ⊔ e) where
  zero : ∀ {Γ σ}               → Γ ▻ σ ∋ σ /̂ ŵk
  suc  : ∀ {Γ σ τ} (x : Γ ∋ τ) → Γ ▻ σ ∋ τ /̂ ŵk

-- Interpretation of variables: a lookup function.

lookup : ∀ {Γ σ} → Γ ∋ σ → Value Γ σ
lookup zero    (γ , v) = v
lookup (suc x) (γ , v) = lookup x γ

-- Application of context morphisms to variables.

infixl 8 _/̂∋_

_/̂∋_ : ∀ {Γ Δ σ} → Γ ∋ σ → (ρ̂ : Γ ⇨̂ Δ) → Value Δ (σ /̂ ρ̂)
x /̂∋ ρ̂ = lookup x /̂Val ρ̂

------------------------------------------------------------------------
-- Context extensions

mutual

  -- Context extensions.

  infixl 5 _▻_

  data Ctxt⁺ (Γ : Ctxt) : Set (u ⊔ e) where
    ε   : Ctxt⁺ Γ
    _▻_ : (Γ⁺ : Ctxt⁺ Γ) (σ : Type (Γ ++ Γ⁺)) → Ctxt⁺ Γ

  -- Appends a context extension to a context.

  infixl 5 _++_

  _++_ : (Γ : Ctxt) → Ctxt⁺ Γ → Ctxt
  Γ ++ ε        = Γ
  Γ ++ (Γ⁺ ▻ σ) = (Γ ++ Γ⁺) ▻ σ

------------------------------------------------------------------------
-- Equality

infix 4 _≅-Ctxt_ _≅-Type_ _≅-Curried-Type_
        _≅-Value_ _≅-⇨̂_ _≅-∋_ _≅-Ctxt⁺_

-- Equality of contexts.

_≅-Ctxt_ : Ctxt → Ctxt → Set _
Γ₁ ≅-Ctxt Γ₂ = Γ₁ ≡ Γ₂

-- Equality of types.
--
-- This library uses propositional equality, including the K rule.
--
-- Two types are defined to be equal if their corresponding telescopes
-- are equal. The constructor [_] turns a type into a telescope.
--
-- At first two types (or context morphisms, or…) were defined to be
-- equal if they were equal according to the heterogeneous equality.
-- However, this led to a problem. Consider the old and new
-- definitions of /̂-cong:
--
-- Old:
--
--   /̂-cong : ∀ {Γ₁ Δ₁ σ₁} {ρ̂₁ : Γ₁ ⇨̂ Δ₁}
--              {Γ₂ Δ₂ σ₂} {ρ̂₂ : Γ₂ ⇨̂ Δ₂} →
--            Γ₁ ≡ Γ₂ → Δ₁ ≡ Δ₂ → σ₁ ≅ σ₂ → ρ̂₁ ≅ ρ̂₂ → σ₁ /̂ ρ̂₁ ≅ σ₂ /̂ ρ̂₂
--   /̂-cong P.refl P.refl H.refl H.refl = H.refl
--
-- New:
--
--   /̂-cong : ∀ {Γ₁ Δ₁ σ₁} {ρ̂₁ : Γ₁ ⇨̂ Δ₁}
--              {Γ₂ Δ₂ σ₂} {ρ̂₂ : Γ₂ ⇨̂ Δ₂} →
--            σ₁ ≅-Type σ₂ → ρ̂₁ ≅-⇨̂ ρ̂₂ → σ₁ /̂ ρ̂₁ ≅-Type σ₂ /̂ ρ̂₂
--   /̂-cong P.refl P.refl = P.refl
--
-- Notice that the old definition required more assumptions than the
-- new one. This meant that proofs using various congruences became
-- unnecessarily large and complicated.

record [Type] : Set (u ⊔ e) where
  constructor [_]
  field
    {Γ} : Ctxt
    σ   : Type Γ

_≅-Type_ : ∀ {Γ₁} (σ₁ : Type Γ₁)
             {Γ₂} (σ₂ : Type Γ₂) → Set _
σ₁ ≅-Type σ₂ = [ σ₁ ] ≡ [ σ₂ ]

-- If the indices are equal, then _≅-Type_ coincides with _≡_.

≅-Type-⇒-≡ : ∀ {Γ} {σ₁ σ₂ : Type Γ} →
             σ₁ ≅-Type σ₂ → σ₁ ≡ σ₂
≅-Type-⇒-≡ P.refl = P.refl

-- Certain uses of substitutivity can be removed.

drop-subst-Type : ∀ {a} {A : Set a} {x₁ x₂}
                  (f : A → Ctxt) {σ} (x₁≡x₂ : x₁ ≡ x₂) →
                  P.subst (λ x → Type (f x)) x₁≡x₂ σ ≅-Type σ
drop-subst-Type f P.refl = P.refl

-- TODO: Should functions like ≅-Type-⇒-≡ and drop-subst-Type be
-- included for all types?

-- Equality of "curried" types.
--
-- TODO: Remove?

record [Curried-Type] : Set (u ⊔ e) where
  constructor [_]
  field
    {Γ} : Ctxt
    {σ} : Type Γ
    τ   : (γ : Env Γ) → El (σ γ) → U

_≅-Curried-Type_ :
  ∀ {Γ₁} {σ₁ : Type Γ₁} (τ₁ : (γ : Env Γ₁) → El (σ₁ γ) → U)
    {Γ₂} {σ₂ : Type Γ₂} (τ₂ : (γ : Env Γ₂) → El (σ₂ γ) → U) → Set _
τ₁ ≅-Curried-Type τ₂ = [Curried-Type].[_] τ₁ ≡ [ τ₂ ]

≅-Curried-Type-⇒-≡ :
  ∀ {Γ} {σ : Type Γ} {τ₁ τ₂ : (γ : Env Γ) → El (σ γ) → U} →
  τ₁ ≅-Curried-Type τ₂ → τ₁ ≡ τ₂
≅-Curried-Type-⇒-≡ P.refl = P.refl

-- Equality of values.

record [Value] : Set (u ⊔ e) where
  constructor [_]
  field
    {Γ} : Ctxt
    {σ} : Type Γ
    v   : Value Γ σ

_≅-Value_ : ∀ {Γ₁ σ₁} (v₁ : Value Γ₁ σ₁)
              {Γ₂ σ₂} (v₂ : Value Γ₂ σ₂) → Set _
v₁ ≅-Value v₂ = [Value].[_] v₁ ≡ [ v₂ ]

≅-Value-⇒-≡ : ∀ {Γ σ} {v₁ v₂ : Value Γ σ} →
              v₁ ≅-Value v₂ → v₁ ≡ v₂
≅-Value-⇒-≡ P.refl = P.refl

-- Equality of "curried" values.
--
-- TODO: Remove?

record [Curried-Value] : Set (u ⊔ e) where
  constructor [_]
  field
    {Γ} : Ctxt
    {σ} : Type Γ
    {τ} : Type (Γ ▻ σ)
    v   : (γ : Env Γ) (x : El (σ γ)) → El (τ (γ , x))

≅-Curried-Value :
  ∀ {Γ₁ σ₁} (τ₁ : Type (Γ₁ ▻ σ₁))
    (v₁ : (γ : Env Γ₁) (x : El (σ₁ γ)) → El (τ₁ (γ , x)))
    {Γ₂ σ₂} (τ₂ : Type (Γ₂ ▻ σ₂))
    (v₂ : (γ : Env Γ₂) (x : El (σ₂ γ)) → El (τ₂ (γ , x))) → Set _
≅-Curried-Value τ₁ v₁ τ₂ v₂ =
  [Curried-Value].[_] {τ = τ₁} v₁ ≡ [_] {τ = τ₂} v₂

≅-Curried-Value-⇒-≡ :
  ∀ {Γ σ} (τ : Type (Γ ▻ σ))
    {v₁ v₂ : (γ : Env Γ) (x : El (σ γ)) → El (τ (γ , x))} →
  ≅-Curried-Value τ v₁ τ v₂ → v₁ ≡ v₂
≅-Curried-Value-⇒-≡ _ P.refl = P.refl

-- Equality of context morphisms.

record [⇨̂] : Set (u ⊔ e) where
  constructor [_]
  field
    {Γ Δ} : Ctxt
    ρ̂     : Γ ⇨̂ Δ

_≅-⇨̂_ : ∀ {Γ₁ Δ₁} (ρ̂₁ : Γ₁ ⇨̂ Δ₁)
          {Γ₂ Δ₂} (ρ̂₂ : Γ₂ ⇨̂ Δ₂) → Set _
ρ̂₁ ≅-⇨̂ ρ̂₂ = [⇨̂].[_] ρ̂₁ ≡ [ ρ̂₂ ]

≅-⇨̂-⇒-≡ : ∀ {Γ Δ} {ρ̂₁ ρ̂₂ : Γ ⇨̂ Δ} →
          ρ̂₁ ≅-⇨̂ ρ̂₂ → ρ̂₁ ≡ ρ̂₂
≅-⇨̂-⇒-≡ P.refl = P.refl

-- Equality of variables.

record [∋] : Set (u ⊔ e) where
  constructor [_]
  field
    {Γ} : Ctxt
    {σ} : Type Γ
    x   : Γ ∋ σ

_≅-∋_ : ∀ {Γ₁ σ₁} (x₁ : Γ₁ ∋ σ₁)
          {Γ₂ σ₂} (x₂ : Γ₂ ∋ σ₂) → Set _
x₁ ≅-∋ x₂ = [∋].[_] x₁ ≡ [ x₂ ]

≅-∋-⇒-≡ : ∀ {Γ σ} {x₁ x₂ : Γ ∋ σ} →
          x₁ ≅-∋ x₂ → x₁ ≡ x₂
≅-∋-⇒-≡ P.refl = P.refl

-- Equality of context extensions.

record [Ctxt⁺] : Set (u ⊔ e) where
  constructor [_]
  field
    {Γ} : Ctxt
    Γ⁺  : Ctxt⁺ Γ

_≅-Ctxt⁺_ : ∀ {Γ₁} (Γ⁺₁ : Ctxt⁺ Γ₁)
              {Γ₂} (Γ⁺₂ : Ctxt⁺ Γ₂) → Set _
Γ⁺₁ ≅-Ctxt⁺ Γ⁺₂ = [Ctxt⁺].[_] Γ⁺₁ ≡ [ Γ⁺₂ ]

≅-Ctxt⁺-⇒-≡ : ∀ {Γ} {Γ⁺₁ Γ⁺₂ : Ctxt⁺ Γ} →
              Γ⁺₁ ≅-Ctxt⁺ Γ⁺₂ → Γ⁺₁ ≡ Γ⁺₂
≅-Ctxt⁺-⇒-≡ P.refl = P.refl

------------------------------------------------------------------------
-- Some lemmas

-- A congruence lemma.

▻-cong : ∀ {Γ₁ Γ₂ σ₁ σ₂} → σ₁ ≅-Type σ₂ → Γ₁ ▻ σ₁ ≅-Ctxt Γ₂ ▻ σ₂
▻-cong P.refl = P.refl

------------------------------------------------------------------------
-- More definitions related to context extensions

mutual

  -- Appends a context extension to a context extension.

  infixl 5 _++⁺_

  _++⁺_ : ∀ {Γ} (Γ⁺ : Ctxt⁺ Γ) → Ctxt⁺ (Γ ++ Γ⁺) → Ctxt⁺ Γ
  Γ⁺ ++⁺ ε         = Γ⁺
  Γ⁺ ++⁺ (Γ⁺⁺ ▻ σ) = (Γ⁺ ++⁺ Γ⁺⁺) ▻ P.subst Type (++-assoc Γ⁺ Γ⁺⁺) σ

  abstract

    -- _++_/_++⁺_ are associative.

    ++-assoc : ∀ {Γ} Γ⁺ Γ⁺⁺ → Γ ++ Γ⁺ ++ Γ⁺⁺ ≅-Ctxt Γ ++ (Γ⁺ ++⁺ Γ⁺⁺)
    ++-assoc Γ⁺ ε         = P.refl
    ++-assoc Γ⁺ (Γ⁺⁺ ▻ σ) =
      ▻-cong (P.sym $ drop-subst-Type id (++-assoc Γ⁺ Γ⁺⁺))

mutual

  -- Application of context morphisms to context extensions.

  infixl 8 _/̂⁺_

  _/̂⁺_ : ∀ {Γ Δ} → Ctxt⁺ Γ → Γ ⇨̂ Δ → Ctxt⁺ Δ
  ε        /̂⁺ ρ̂ = ε
  (Γ⁺ ▻ σ) /̂⁺ ρ̂ = Γ⁺ /̂⁺ ρ̂ ▻ σ /̂ ρ̂ ↑̂⁺ Γ⁺

  -- N-ary lifting of context morphisms.

  infixl 10 _↑̂⁺_

  _↑̂⁺_ : ∀ {Γ Δ} (ρ̂ : Γ ⇨̂ Δ) Γ⁺ → Γ ++ Γ⁺ ⇨̂ Δ ++ Γ⁺ /̂⁺ ρ̂
  ρ̂ ↑̂⁺ ε        = ρ̂
  ρ̂ ↑̂⁺ (Γ⁺ ▻ σ) = (ρ̂ ↑̂⁺ Γ⁺) ↑̂

-- N-ary weakening.

ŵk⁺ : ∀ {Γ} Γ⁺ → Γ ⇨̂ Γ ++ Γ⁺
ŵk⁺ ε        = îd
ŵk⁺ (Γ⁺ ▻ σ) = ŵk⁺ Γ⁺ ∘̂ ŵk

------------------------------------------------------------------------
-- More congruence lemmas

îd-cong : ∀ {Γ₁ Γ₂} → Γ₁ ≅-Ctxt Γ₂ → îd {Γ = Γ₁} ≅-⇨̂ îd {Γ = Γ₂}
îd-cong P.refl = P.refl

∘̂-cong : ∀ {Γ₁ Δ₁ Ε₁} {ρ̂₁₁ : Γ₁ ⇨̂ Δ₁} {ρ̂₂₁ : Δ₁ ⇨̂ Ε₁}
           {Γ₂ Δ₂ Ε₂} {ρ̂₁₂ : Γ₂ ⇨̂ Δ₂} {ρ̂₂₂ : Δ₂ ⇨̂ Ε₂} →
         ρ̂₁₁ ≅-⇨̂ ρ̂₁₂ → ρ̂₂₁ ≅-⇨̂ ρ̂₂₂ → ρ̂₁₁ ∘̂ ρ̂₂₁ ≅-⇨̂ ρ̂₁₂ ∘̂ ρ̂₂₂
∘̂-cong P.refl P.refl = P.refl

/̂-cong : ∀ {Γ₁ Δ₁ σ₁} {ρ̂₁ : Γ₁ ⇨̂ Δ₁}
           {Γ₂ Δ₂ σ₂} {ρ̂₂ : Γ₂ ⇨̂ Δ₂} →
         σ₁ ≅-Type σ₂ → ρ̂₁ ≅-⇨̂ ρ̂₂ → σ₁ /̂ ρ̂₁ ≅-Type σ₂ /̂ ρ̂₂
/̂-cong P.refl P.refl = P.refl

/̂Val-cong : ∀ {Γ₁ Δ₁ σ₁} {v₁ : Value Γ₁ σ₁} {ρ̂₁ : Γ₁ ⇨̂ Δ₁}
              {Γ₂ Δ₂ σ₂} {v₂ : Value Γ₂ σ₂} {ρ̂₂ : Γ₂ ⇨̂ Δ₂} →
            v₁ ≅-Value v₂ → ρ̂₁ ≅-⇨̂ ρ̂₂ → v₁ /̂Val ρ̂₁ ≅-Value v₂ /̂Val ρ̂₂
/̂Val-cong P.refl P.refl = P.refl

ŵk-cong : ∀ {Γ₁} {σ₁ : Type Γ₁} {Γ₂} {σ₂ : Type Γ₂} →
          σ₁ ≅-Type σ₂ → ŵk {σ = σ₁} ≅-⇨̂ ŵk {σ = σ₂}
ŵk-cong P.refl = P.refl

ε̂-cong : ∀ {Δ₁ Δ₂} → Δ₁ ≅-Ctxt Δ₂ → ε̂ {Δ = Δ₁} ≅-⇨̂ ε̂ {Δ = Δ₂}
ε̂-cong P.refl = P.refl

▻̂-cong : ∀ {Γ₁ Δ₁ σ₁} {ρ̂₁ : Γ₁ ⇨̂ Δ₁} {v₁ : Value Δ₁ (σ₁ /̂ ρ̂₁)}
           {Γ₂ Δ₂ σ₂} {ρ̂₂ : Γ₂ ⇨̂ Δ₂} {v₂ : Value Δ₂ (σ₂ /̂ ρ̂₂)} →
         σ₁ ≅-Type σ₂ → ρ̂₁ ≅-⇨̂ ρ̂₂ → v₁ ≅-Value v₂ →
         _▻̂_ {σ = σ₁} ρ̂₁ v₁ ≅-⇨̂ _▻̂_ {σ = σ₂} ρ̂₂ v₂
▻̂-cong P.refl P.refl P.refl = P.refl

ŝub-cong : ∀ {Γ₁ σ₁} {v₁ : Value Γ₁ σ₁} {Γ₂ σ₂} {v₂ : Value Γ₂ σ₂} →
           v₁ ≅-Value v₂ → ŝub v₁ ≅-⇨̂ ŝub v₂
ŝub-cong P.refl = P.refl

t̂ail-cong : ∀ {Γ₁ Δ₁ σ₁} {ρ̂₁ : Γ₁ ▻ σ₁ ⇨̂ Δ₁}
              {Γ₂ Δ₂ σ₂} {ρ̂₂ : Γ₂ ▻ σ₂ ⇨̂ Δ₂} →
            ρ̂₁ ≅-⇨̂ ρ̂₂ → t̂ail ρ̂₁ ≅-⇨̂ t̂ail ρ̂₂
t̂ail-cong P.refl = P.refl

ĥead-cong : ∀ {Γ₁ Δ₁ σ₁} {ρ̂₁ : Γ₁ ▻ σ₁ ⇨̂ Δ₁}
              {Γ₂ Δ₂ σ₂} {ρ̂₂ : Γ₂ ▻ σ₂ ⇨̂ Δ₂} →
            ρ̂₁ ≅-⇨̂ ρ̂₂ → ĥead ρ̂₁ ≅-Value ĥead ρ̂₂
ĥead-cong P.refl = P.refl

↑̂-cong : ∀ {Γ₁ Δ₁} {ρ̂₁ : Γ₁ ⇨̂ Δ₁} {σ₁}
           {Γ₂ Δ₂} {ρ̂₂ : Γ₂ ⇨̂ Δ₂} {σ₂} →
         ρ̂₁ ≅-⇨̂ ρ̂₂ → σ₁ ≅-Type σ₂ → _↑̂ {σ = σ₁} ρ̂₁ ≅-⇨̂ _↑̂ {σ = σ₂} ρ̂₂
↑̂-cong P.refl P.refl = P.refl

▻⁺-cong : ∀ {Γ₁} {Γ⁺₁ : Ctxt⁺ Γ₁} {σ₁}
            {Γ₂} {Γ⁺₂ : Ctxt⁺ Γ₂} {σ₂} →
          Γ⁺₁ ≅-Ctxt⁺ Γ⁺₂ → σ₁ ≅-Type σ₂ →
          Γ⁺₁ ▻ σ₁ ≅-Ctxt⁺ Γ⁺₂ ▻ σ₂
▻⁺-cong P.refl P.refl = P.refl

++-cong : ∀ {Γ₁} {Γ⁺₁ : Ctxt⁺ Γ₁} {Γ₂} {Γ⁺₂ : Ctxt⁺ Γ₂} →
          Γ⁺₁ ≅-Ctxt⁺ Γ⁺₂ → Γ₁ ++ Γ⁺₁ ≅-Ctxt Γ₂ ++ Γ⁺₂
++-cong P.refl = P.refl

++⁺-cong : ∀ {Γ₁ Γ⁺₁} {Γ⁺⁺₁ : Ctxt⁺ (Γ₁ ++ Γ⁺₁)}
             {Γ₂ Γ⁺₂} {Γ⁺⁺₂ : Ctxt⁺ (Γ₂ ++ Γ⁺₂)} →
           Γ⁺₁ ≅-Ctxt⁺ Γ⁺₂ → Γ⁺⁺₁ ≅-Ctxt⁺ Γ⁺⁺₂ →
           Γ⁺₁ ++⁺ Γ⁺⁺₁ ≅-Ctxt⁺ Γ⁺₂ ++⁺ Γ⁺⁺₂
++⁺-cong P.refl P.refl = P.refl

ŵk⁺-cong : ∀ {Γ₁} {Γ⁺₁ : Ctxt⁺ Γ₁} {Γ₂} {Γ⁺₂ : Ctxt⁺ Γ₂} →
           Γ⁺₁ ≅-Ctxt⁺ Γ⁺₂ → ŵk⁺ Γ⁺₁ ≅-⇨̂ ŵk⁺ Γ⁺₂
ŵk⁺-cong P.refl = P.refl

/̂⁺-cong : ∀ {Γ₁ Δ₁} {Γ⁺₁ : Ctxt⁺ Γ₁} {ρ̂₁ : Γ₁ ⇨̂ Δ₁}
            {Γ₂ Δ₂} {Γ⁺₂ : Ctxt⁺ Γ₂} {ρ̂₂ : Γ₂ ⇨̂ Δ₂} →
          Γ⁺₁ ≅-Ctxt⁺ Γ⁺₂ → ρ̂₁ ≅-⇨̂ ρ̂₂ → Γ⁺₁ /̂⁺ ρ̂₁ ≅-Ctxt⁺ Γ⁺₂ /̂⁺ ρ̂₂
/̂⁺-cong P.refl P.refl = P.refl

↑̂⁺-cong : ∀ {Γ₁ Δ₁} {ρ̂₁ : Γ₁ ⇨̂ Δ₁} {Γ⁺₁ : Ctxt⁺ Γ₁}
            {Γ₂ Δ₂} {ρ̂₂ : Γ₂ ⇨̂ Δ₂} {Γ⁺₂ : Ctxt⁺ Γ₂} →
          ρ̂₁ ≅-⇨̂ ρ̂₂ → Γ⁺₁ ≅-Ctxt⁺ Γ⁺₂ → ρ̂₁ ↑̂⁺ Γ⁺₁ ≅-⇨̂ ρ̂₂ ↑̂⁺ Γ⁺₂
↑̂⁺-cong P.refl P.refl = P.refl

zero-cong : ∀ {Γ₁} {σ₁ : Type Γ₁}
              {Γ₂} {σ₂ : Type Γ₂} →
            σ₁ ≅-Type σ₂ → zero {σ = σ₁} ≅-∋ zero {σ = σ₂}
zero-cong P.refl = P.refl

suc-cong :
  ∀ {Γ₁ σ₁ τ₁} {x₁ : Γ₁ ∋ τ₁}
    {Γ₂ σ₂ τ₂} {x₂ : Γ₂ ∋ τ₂} →
  σ₁ ≅-Type σ₂ → x₁ ≅-∋ x₂ → suc {σ = σ₁} x₁ ≅-∋ suc {σ = σ₂} x₂
suc-cong P.refl P.refl = P.refl

/̂∋-cong : ∀ {Γ₁ Δ₁ σ₁} {x₁ : Γ₁ ∋ σ₁} {ρ̂₁ : Γ₁ ⇨̂ Δ₁}
            {Γ₂ Δ₂ σ₂} {x₂ : Γ₂ ∋ σ₂} {ρ̂₂ : Γ₂ ⇨̂ Δ₂} →
          x₁ ≅-∋ x₂ → ρ̂₁ ≅-⇨̂ ρ̂₂ → x₁ /̂∋ ρ̂₁ ≅-Value x₂ /̂∋ ρ̂₂
/̂∋-cong P.refl P.refl = P.refl

curry-cong-Type : ∀ {Γ₁ σ₁} {τ₁ : Type (Γ₁ ▻ σ₁)}
                    {Γ₂ σ₂} {τ₂ : Type (Γ₂ ▻ σ₂)} →
                  τ₁ ≅-Type τ₂ → curry τ₁ ≅-Curried-Type curry τ₂
curry-cong-Type P.refl = P.refl

curry-cong-Value :
  ∀ {Γ₁ σ₁ τ₁} {v₁ : Value (Γ₁ ▻ σ₁) τ₁}
    {Γ₂ σ₂ τ₂} {v₂ : Value (Γ₂ ▻ σ₂) τ₂} →
  v₁ ≅-Value v₂ → ≅-Curried-Value τ₁ (curry v₁) τ₂ (curry v₂)
curry-cong-Value P.refl = P.refl

ˢ-cong :
  ∀ {Γ₁ σ₁} {τ₁ : Type (Γ₁ ▻ σ₁)}
    {f₁ : (γ : Env Γ₁) (v : El (σ₁ γ)) → El (τ₁ (γ , v))}
    {v₁ : Value Γ₁ σ₁}
    {Γ₂ σ₂} {τ₂ : Type (Γ₂ ▻ σ₂)}
    {f₂ : (γ : Env Γ₂) (v : El (σ₂ γ)) → El (τ₂ (γ , v))}
    {v₂ : Value Γ₂ σ₂} →
  ≅-Curried-Value τ₁ f₁ τ₂ f₂ → v₁ ≅-Value v₂ →
  f₁ ˢ v₁ ≅-Value f₂ ˢ v₂
ˢ-cong P.refl P.refl = P.refl

------------------------------------------------------------------------
-- Some properties which hold definitionally

-- îd and _∘̂_ form a monoid.

îd-∘̂ : ∀ {Γ Δ} (ρ̂ : Γ ⇨̂ Δ) → ρ̂ ∘̂ îd ≅-⇨̂ ρ̂
îd-∘̂ ρ̂ = P.refl

∘̂-îd : ∀ {Γ Δ} (ρ̂ : Γ ⇨̂ Δ) → îd ∘̂ ρ̂ ≅-⇨̂ ρ̂
∘̂-îd ρ̂ = P.refl

∘̂-assoc : ∀ {Γ Δ Ε Ζ} (ρ̂₁ : Γ ⇨̂ Δ) (ρ̂₂ : Δ ⇨̂ Ε) (ρ̂₃ : Ε ⇨̂ Ζ) →
          ρ̂₁ ∘̂ (ρ̂₂ ∘̂ ρ̂₃) ≅-⇨̂ (ρ̂₁ ∘̂ ρ̂₂) ∘̂ ρ̂₃
∘̂-assoc ρ̂₁ ρ̂₂ ρ̂₃ = P.refl

-- The lifting of the identity substitution is the identity
-- substitution.

îd-↑̂ : ∀ {Γ} (σ : Type Γ) → _↑̂ {σ = σ} îd ≅-⇨̂ îd {Γ = Γ ▻ σ}
îd-↑̂ σ = P.refl

-- _↑̂ distributes over _∘̂_.

↑̂-distrib : ∀ {Γ Δ Ε} (ρ̂₁ : Γ ⇨̂ Δ) (ρ̂₂ : Δ ⇨̂ Ε) σ →
            _↑̂ {σ = σ} (ρ̂₁ ∘̂ ρ̂₂) ≅-⇨̂ _↑̂ {σ = σ} ρ̂₁ ∘̂ ρ̂₂ ↑̂
↑̂-distrib ρ̂₁ ρ̂₂ σ = P.refl

-- ŵk is a left inverse of ŝub.

ŵk-∘̂-ŝub : ∀ {Γ σ} (v : Value Γ σ) → ŵk ∘̂ ŝub v ≅-⇨̂ îd
ŵk-∘̂-ŝub v = P.refl

-- First weakening under the head, and then replacing the head with
-- the new head, is the same as doing nothing.

ŵk-↑̂-∘̂-ŝub : ∀ {Γ} σ → ŵk ↑̂ ∘̂ ŝub proj₂ ≅-⇨̂ îd {Γ = Γ ▻ σ}
ŵk-↑̂-∘̂-ŝub σ = P.refl

-- ŵk commutes with arbitrary context morphisms (modulo lifting).

∘̂-ŵk : ∀ {Γ Δ} (ρ̂ : Γ ⇨̂ Δ) σ → ρ̂ ∘̂ ŵk {σ = σ /̂ ρ̂} ≅-⇨̂ ŵk {σ = σ} ∘̂ ρ̂ ↑̂
∘̂-ŵk ρ̂ σ = P.refl

-- ŝub commutes with arbitrary context morphisms (modulo lifting).

ŝub-∘̂ : ∀ {Γ Δ σ} (ρ̂ : Γ ⇨̂ Δ) (v : Value Γ σ) →
        ŝub v ∘̂ ρ̂ ≅-⇨̂ ρ̂ ↑̂ ∘̂ ŝub (v /̂Val ρ̂)
ŝub-∘̂ ρ̂ v = P.refl

-- Laws relating _▻̂_, ĥead and t̂ail.

ĥead-▻̂ : ∀ {Γ Δ σ} (ρ̂ : Γ ⇨̂ Δ) (v : Value Δ (σ /̂ ρ̂)) →
         ĥead {σ = σ} (ρ̂ ▻̂ v) ≅-Value v
ĥead-▻̂ ρ̂ v = P.refl

t̂ail-▻̂ : ∀ {Γ Δ σ} (ρ̂ : Γ ⇨̂ Δ) (v : Value Δ (σ /̂ ρ̂)) →
         t̂ail {σ = σ} (ρ̂ ▻̂ v) ≅-⇨̂ ρ̂
t̂ail-▻̂ ρ̂ v = P.refl

t̂ail-▻̂-ĥead : ∀ {Γ Δ σ} (ρ̂ : Γ ▻ σ ⇨̂ Δ) → t̂ail ρ̂ ▻̂ ĥead ρ̂ ≅-⇨̂ ρ̂
t̂ail-▻̂-ĥead ρ̂ = P.refl

-- Law relating _▻̂_ and _∘̂_.

▻̂-∘̂ : ∀ {Γ Δ Ε σ} (ρ̂₁ : Γ ⇨̂ Δ) (ρ̂₂ : Δ ⇨̂ Ε) (v : Value Δ (σ /̂ ρ̂₁)) →
      (_▻̂_ {σ = σ} ρ̂₁ v) ∘̂ ρ̂₂ ≅-⇨̂ (ρ̂₁ ∘̂ ρ̂₂) ▻̂ v /̂Val ρ̂₂
▻̂-∘̂ ρ̂₁ ρ̂₂ v = P.refl

-- The identity substitution has no effect.

/̂-îd : ∀ {Γ} (σ : Type Γ) → σ /̂ îd ≅-Type σ
/̂-îd σ = P.refl

/̂Val-îd : ∀ {Γ σ} (v : Value Γ σ) → v /̂Val îd ≅-Value v
/̂Val-îd v = P.refl

-- Applying two substitutions is equivalent to applying their
-- composition.

/̂-∘̂ : ∀ {Γ Δ Ε} (ρ̂₁ : Γ ⇨̂ Δ) (ρ̂₂ : Δ ⇨̂ Ε) σ →
      σ /̂ ρ̂₁ ∘̂ ρ̂₂ ≅-Type σ /̂ ρ̂₁ /̂ ρ̂₂
/̂-∘̂ ρ̂₁ ρ̂₂ σ = P.refl

/̂Val-∘̂ : ∀ {Γ Δ Ε σ} (ρ̂₁ : Γ ⇨̂ Δ) (ρ̂₂ : Δ ⇨̂ Ε) (v : Value Γ σ) →
         v /̂Val ρ̂₁ ∘̂ ρ̂₂ ≅-Value v /̂Val ρ̂₁ /̂Val ρ̂₂
/̂Val-∘̂ ρ̂₁ ρ̂₂ v = P.refl

------------------------------------------------------------------------
-- Some properties which do not hold definitionally

abstract

  mutual

    -- The identity substitution has no effect.

    /̂⁺-îd : ∀ {Γ} (Γ⁺ : Ctxt⁺ Γ) → Γ⁺ /̂⁺ îd ≅-Ctxt⁺ Γ⁺
    /̂⁺-îd ε        = P.refl
    /̂⁺-îd (Γ⁺ ▻ σ) = ▻⁺-cong (/̂⁺-îd Γ⁺) (/̂-cong P.refl (îd-↑̂⁺ Γ⁺))

    -- The n-ary lifting of the identity substitution is the identity
    -- substitution.

    îd-↑̂⁺ : ∀ {Γ} (Γ⁺ : Ctxt⁺ Γ) → îd ↑̂⁺ Γ⁺ ≅-⇨̂ îd[ Γ ++ Γ⁺ ]
    îd-↑̂⁺ ε        = P.refl
    îd-↑̂⁺ (Γ⁺ ▻ σ) = begin
      [ (îd ↑̂⁺ Γ⁺) ↑̂ ]  ≡⟨ ↑̂-cong (îd-↑̂⁺ Γ⁺) P.refl ⟩
      [ îd ↑̂         ]  ≡⟨ P.refl ⟩
      [ îd           ]  ∎

  -- The identity substitution has no effect even if lifted.

  /̂-îd-↑̂⁺ : ∀ {Γ} Γ⁺ (σ : Type (Γ ++ Γ⁺)) → σ /̂ îd ↑̂⁺ Γ⁺ ≅-Type σ
  /̂-îd-↑̂⁺ Γ⁺ σ = begin
    [ σ /̂ îd ↑̂⁺ Γ⁺ ]  ≡⟨ /̂-cong (P.refl {x = [ σ ]}) (îd-↑̂⁺ Γ⁺) ⟩
    [ σ /̂ îd       ]  ≡⟨ P.refl ⟩
    [ σ            ]  ∎

  mutual

    -- Applying two substitutions is equivalent to applying their
    -- composition.

    /̂⁺-∘̂ : ∀ {Γ Δ Ε} Γ⁺ (ρ̂₁ : Γ ⇨̂ Δ) (ρ̂₂ : Δ ⇨̂ Ε) →
           Γ⁺ /̂⁺ ρ̂₁ ∘̂ ρ̂₂ ≅-Ctxt⁺ Γ⁺ /̂⁺ ρ̂₁ /̂⁺ ρ̂₂
    /̂⁺-∘̂ ε        ρ̂₁ ρ̂₂ = P.refl
    /̂⁺-∘̂ (Γ⁺ ▻ σ) ρ̂₁ ρ̂₂ =
      ▻⁺-cong (/̂⁺-∘̂ Γ⁺ ρ̂₁ ρ̂₂) (/̂-cong (P.refl {x = [ σ ]}) (∘̂-↑̂⁺ ρ̂₁ ρ̂₂ Γ⁺))

    -- _↑̂⁺_ distributes over _∘̂_.

    ∘̂-↑̂⁺ : ∀ {Γ Δ Ε} (ρ̂₁ : Γ ⇨̂ Δ) (ρ̂₂ : Δ ⇨̂ Ε) Γ⁺ →
           (ρ̂₁ ∘̂ ρ̂₂) ↑̂⁺ Γ⁺ ≅-⇨̂ ρ̂₁ ↑̂⁺ Γ⁺ ∘̂ ρ̂₂ ↑̂⁺ (Γ⁺ /̂⁺ ρ̂₁)
    ∘̂-↑̂⁺ ρ̂₁ ρ̂₂ ε        = P.refl
    ∘̂-↑̂⁺ ρ̂₁ ρ̂₂ (Γ⁺ ▻ σ) = begin
      [ ((ρ̂₁ ∘̂ ρ̂₂) ↑̂⁺ Γ⁺) ↑̂                          ]  ≡⟨ ↑̂-cong (∘̂-↑̂⁺ ρ̂₁ ρ̂₂ Γ⁺) P.refl ⟩
      [ (ρ̂₁ ↑̂⁺ Γ⁺ ∘̂ ρ̂₂ ↑̂⁺ (Γ⁺ /̂⁺ ρ̂₁)) ↑̂              ]  ≡⟨ P.refl ⟩
      [ _↑̂ {σ = σ} (ρ̂₁ ↑̂⁺ Γ⁺) ∘̂ (ρ̂₂ ↑̂⁺ (Γ⁺ /̂⁺ ρ̂₁)) ↑̂ ]  ∎

  -- Two corollaries.
  --
  -- TODO: Remove if unused.

  ▻-/̂-++-/̂⁺-/̂⁺-ŵk : ∀ {Γ Δ} σ (ρ̂ : Γ ⇨̂ Δ) (Γ⁺ : Ctxt⁺ Γ) →
                    Δ ▻ σ /̂ ρ̂ ++ Γ⁺ /̂⁺ ρ̂ /̂⁺ ŵk ≅-Ctxt
                    Δ ▻ σ /̂ ρ̂ ++ Γ⁺ /̂⁺ ŵk {σ = σ} /̂⁺ ρ̂ ↑̂
  ▻-/̂-++-/̂⁺-/̂⁺-ŵk σ ρ̂ Γ⁺ = ++-cong (begin
    [ Γ⁺ /̂⁺ ρ̂ /̂⁺ ŵk           ]  ≡⟨ P.sym $ /̂⁺-∘̂ Γ⁺ ρ̂ ŵk ⟩
    [ Γ⁺ /̂⁺ ρ̂ ∘̂ ŵk            ]  ≡⟨ P.refl ⟩
    [ Γ⁺ /̂⁺ ŵk {σ = σ} ∘̂ ρ̂ ↑̂  ]  ≡⟨ /̂⁺-∘̂ Γ⁺ (ŵk {σ = σ}) (ρ̂ ↑̂) ⟩
    [ Γ⁺ /̂⁺ ŵk {σ = σ} /̂⁺ ρ̂ ↑̂ ]  ∎)

  /̂-↑̂⁺-/̂-ŵk-↑̂⁺ : ∀ {Γ Δ} σ (ρ̂ : Γ ⇨̂ Δ) (Γ⁺ : Ctxt⁺ Γ) τ →
                 τ /̂ ρ̂ ↑̂⁺ Γ⁺ /̂ ŵk {σ = σ /̂ ρ̂} ↑̂⁺ (Γ⁺ /̂⁺ ρ̂) ≅-Type
                 τ /̂ ŵk {σ = σ} ↑̂⁺ Γ⁺ /̂ ρ̂ ↑̂ ↑̂⁺ (Γ⁺ /̂⁺ ŵk)
  /̂-↑̂⁺-/̂-ŵk-↑̂⁺ σ ρ̂ Γ⁺ τ = /̂-cong (P.refl {x = [ τ ]}) (begin
    [ ρ̂ ↑̂⁺ Γ⁺ ∘̂ ŵk ↑̂⁺ (Γ⁺ /̂⁺ ρ̂)            ]  ≡⟨ P.sym $ ∘̂-↑̂⁺ ρ̂ ŵk Γ⁺ ⟩
    [ (ρ̂ ∘̂ ŵk) ↑̂⁺ Γ⁺                       ]  ≡⟨ P.refl ⟩
    [ (ŵk {σ = σ} ∘̂ ρ̂ ↑̂) ↑̂⁺ Γ⁺             ]  ≡⟨ ∘̂-↑̂⁺ (ŵk {σ = σ}) (ρ̂ ↑̂) Γ⁺ ⟩
    [ ŵk {σ = σ} ↑̂⁺ Γ⁺ ∘̂ ρ̂ ↑̂ ↑̂⁺ (Γ⁺ /̂⁺ ŵk) ]  ∎)

  -- ŵk⁺ commutes (modulo lifting) with arbitrary context morphisms.

  ∘̂-ŵk⁺ : ∀ {Γ Δ} (ρ̂ : Γ ⇨̂ Δ) Γ⁺ →
          ρ̂ ∘̂ ŵk⁺ (Γ⁺ /̂⁺ ρ̂) ≅-⇨̂ ŵk⁺ Γ⁺ ∘̂ ρ̂ ↑̂⁺ Γ⁺
  ∘̂-ŵk⁺ ρ̂ ε        = P.refl
  ∘̂-ŵk⁺ ρ̂ (Γ⁺ ▻ σ) = begin
    [ ρ̂ ∘̂ ŵk⁺ (Γ⁺ /̂⁺ ρ̂) ∘̂ ŵk            ]  ≡⟨ ∘̂-cong (∘̂-ŵk⁺ ρ̂ Γ⁺) P.refl ⟩
    [ ŵk⁺ Γ⁺ ∘̂ ρ̂ ↑̂⁺ Γ⁺ ∘̂ ŵk             ]  ≡⟨ P.refl ⟩
    [ ŵk⁺ Γ⁺ ∘̂ ŵk {σ = σ} ∘̂ (ρ̂ ↑̂⁺ Γ⁺) ↑̂ ]  ∎

  -- ŵk⁺ is homomorphic with respect to _++⁺_/_∘̂_.

  ŵk⁺-++⁺ : ∀ {Γ} (Γ⁺ : Ctxt⁺ Γ) (Γ⁺⁺ : Ctxt⁺ (Γ ++ Γ⁺)) →
            ŵk⁺ (Γ⁺ ++⁺ Γ⁺⁺) ≅-⇨̂ ŵk⁺ Γ⁺ ∘̂ ŵk⁺ Γ⁺⁺
  ŵk⁺-++⁺ Γ⁺ ε         = P.refl
  ŵk⁺-++⁺ Γ⁺ (Γ⁺⁺ ▻ σ) =
    ∘̂-cong (ŵk⁺-++⁺ Γ⁺ Γ⁺⁺)
           (ŵk-cong (drop-subst-Type id (++-assoc Γ⁺ Γ⁺⁺)))

  -- Two n-ary liftings can be merged into one.

  ↑̂⁺-++⁺ : ∀ {Γ Δ} (ρ̂ : Γ ⇨̂ Δ) Γ⁺ Γ⁺⁺ →
           ρ̂ ↑̂⁺ (Γ⁺ ++⁺ Γ⁺⁺) ≅-⇨̂ ρ̂ ↑̂⁺ Γ⁺ ↑̂⁺ Γ⁺⁺
  ↑̂⁺-++⁺ ρ̂ Γ⁺ ε         = P.refl
  ↑̂⁺-++⁺ ρ̂ Γ⁺ (Γ⁺⁺ ▻ σ) = begin
    [ (ρ̂ ↑̂⁺ (Γ⁺ ++⁺ Γ⁺⁺)) ↑̂ ]  ≡⟨ ↑̂-cong (↑̂⁺-++⁺ ρ̂ Γ⁺ Γ⁺⁺) (drop-subst-Type id (++-assoc Γ⁺ Γ⁺⁺)) ⟩
    [ (ρ̂ ↑̂⁺ Γ⁺ ↑̂⁺ Γ⁺⁺) ↑̂    ]  ∎

  -- _/̂⁺_ distributes over _++⁺_ (sort of).

  ++-++⁺-/̂⁺ :
    ∀ {Γ Δ} (ρ̂ : Γ ⇨̂ Δ) Γ⁺ Γ⁺⁺ →
    Δ ++ (Γ⁺ ++⁺ Γ⁺⁺) /̂⁺ ρ̂ ≅-Ctxt Δ ++ Γ⁺ /̂⁺ ρ̂ ++ Γ⁺⁺ /̂⁺ ρ̂ ↑̂⁺ Γ⁺
  ++-++⁺-/̂⁺         ρ̂ Γ⁺ ε         = P.refl
  ++-++⁺-/̂⁺ {Δ = Δ} ρ̂ Γ⁺ (Γ⁺⁺ ▻ σ) = begin
    Δ ++ (Γ⁺ ++⁺ Γ⁺⁺) /̂⁺ ρ̂ ▻
      P.subst Type (++-assoc Γ⁺ Γ⁺⁺) σ /̂ ρ̂ ↑̂⁺ (Γ⁺ ++⁺ Γ⁺⁺)  ≡⟨ ▻-cong (/̂-cong (drop-subst-Type id (++-assoc Γ⁺ Γ⁺⁺))
                                                                              (↑̂⁺-++⁺ ρ̂ Γ⁺ Γ⁺⁺)) ⟩
    Δ ++ Γ⁺ /̂⁺ ρ̂ ++ Γ⁺⁺ /̂⁺ ρ̂ ↑̂⁺ Γ⁺ ▻ σ /̂ ρ̂ ↑̂⁺ Γ⁺ ↑̂⁺ Γ⁺⁺     ∎