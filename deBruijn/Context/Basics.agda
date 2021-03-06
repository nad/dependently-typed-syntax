------------------------------------------------------------------------
-- Contexts, variables, context morphisms, etc.
------------------------------------------------------------------------

-- Based on Conor McBride's "Outrageous but Meaningful Coincidences:
-- Dependent type-safe syntax and evaluation".

-- The contexts and variables are parametrised by a universe.

open import Data.Universe.Indexed

module deBruijn.Context.Basics
  {i u e} (Uni : IndexedUniverse i u e) where

open IndexedUniverse Uni

open import Data.Product as Prod
open import Data.Unit
open import Function hiding (_∋_)
open import Level using (_⊔_; Lift)
open import Relation.Binary.PropositionalEquality as P using (_≡_)
open import Relation.Nullary
import Relation.Nullary.Decidable as Dec

open P.≡-Reasoning

------------------------------------------------------------------------
-- Contexts and "types"

mutual

  -- Contexts.

  infixl 5 _▻_

  data Ctxt : Set (i ⊔ u ⊔ e) where
    ε   : Ctxt
    _▻_ : (Γ : Ctxt) (σ : Type Γ) → Ctxt

  -- Semantic types: maps from environments to universe codes. The
  -- semantic types come in two flavours: indexed and unindexed
  -- (paired up with an index).

  IType : Ctxt → I → Set (u ⊔ e)
  IType Γ i = Env Γ → U i

  Type : Ctxt → Set (i ⊔ u ⊔ e)
  Type Γ = ∃ λ i → IType Γ i

  -- Extracts the index from an unindexed type.

  index : ∀ {Γ} → Type Γ → I
  index = proj₁

  -- Converts a type to an indexed type.

  indexed-type : ∀ {Γ} (σ : Type Γ) → IType Γ (index σ)
  indexed-type = proj₂

  -- Interpretation of contexts: environments.

  Env : Ctxt → Set e
  Env ε       = Lift _ ⊤
  Env (Γ ▻ σ) = Σ (Env Γ) λ γ → El (indexed-type σ γ)

-- Semantic values: maps from environments to universe values.

Value : (Γ : Ctxt) → Type Γ → Set _
Value Γ σ = (γ : Env Γ) → El (indexed-type σ γ)

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

-- If the context cannot be inferred the following variant can be used
-- instead.

îd[_] : ∀ Γ → Γ ⇨̂ Γ
îd[ _ ] = îd

-- Reverse composition of context morphisms.

infixl 9 _∘̂_

_∘̂_ : ∀ {Γ Δ Ε} → Γ ⇨̂ Δ → Δ ⇨̂ Ε → Γ ⇨̂ Ε
ρ̂₁ ∘̂ ρ̂₂ = ρ̂₁ ∘ ρ̂₂

-- Application of context morphisms to indexed types.

infixl 8 _/̂I_

_/̂I_ : ∀ {Γ Δ i} → IType Γ i → Γ ⇨̂ Δ → IType Δ i
σ /̂I ρ̂ = σ ∘ ρ̂

-- Application of context morphisms to types.

infixl 8 _/̂_

_/̂_ : ∀ {Γ Δ} → Type Γ → Γ ⇨̂ Δ → Type Δ
(i , σ) /̂ ρ̂ = (i , σ /̂I ρ̂)

-- Application of context morphisms to values.

infixl 8 _/̂Val_

_/̂Val_ : ∀ {Γ Δ σ} → Value Γ σ → (ρ̂ : Γ ⇨̂ Δ) → Value Δ (σ /̂ ρ̂)
v /̂Val ρ̂ = v ∘ ρ̂

-- Weakening.

ŵk : ∀ {Γ σ} → Γ ⇨̂ Γ ▻ σ
ŵk = proj₁

ŵk[_] : ∀ {Γ} σ → Γ ⇨̂ Γ ▻ σ
ŵk[ _ ] = ŵk

-- Empty context morphism.

ε̂ : ∀ {Δ} → ε ⇨̂ Δ
ε̂ = λ _ → _

ε̂[_] : ∀ Δ → ε ⇨̂ Δ
ε̂[ _ ] = ε̂

-- Extends a context morphism with another value.

infixl 5 _▻̂_ _▻̂[_]_

_▻̂_ : ∀ {Γ Δ σ} (ρ̂ : Γ ⇨̂ Δ) → Value Δ (σ /̂ ρ̂) → Γ ▻ σ ⇨̂ Δ
_▻̂_ = <_,_>

_▻̂[_]_ : ∀ {Γ Δ} (ρ̂ : Γ ⇨̂ Δ) σ → Value Δ (σ /̂ ρ̂) → Γ ▻ σ ⇨̂ Δ
ρ̂ ▻̂[ _ ] v = ρ̂ ▻̂ v

-- A context morphism which only modifies the last "variable".

ŝub : ∀ {Γ σ} → Value Γ σ → Γ ▻ σ ⇨̂ Γ
ŝub v = îd ▻̂ v

-- The "tail" of a "nonempty" context morphism.

t̂ail : ∀ {Γ Δ σ} → Γ ▻ σ ⇨̂ Δ → Γ ⇨̂ Δ
t̂ail ρ̂ = ŵk ∘̂ ρ̂

-- The "head" of a "nonempty" context morphism.

ĥead : ∀ {Γ Δ σ} (ρ̂ : Γ ▻ σ ⇨̂ Δ) → Value Δ (σ /̂ t̂ail ρ̂)
ĥead ρ̂ = proj₂ ∘ ρ̂

-- Lifting.

infixl 10 _↑̂_
infix  10 _↑̂

_↑̂_ : ∀ {Γ Δ} (ρ̂ : Γ ⇨̂ Δ) σ → Γ ▻ σ ⇨̂ Δ ▻ σ /̂ ρ̂
ρ̂ ↑̂ _ = Prod.map ρ̂ id

_↑̂ : ∀ {Γ Δ σ} (ρ̂ : Γ ⇨̂ Δ) → Γ ▻ σ ⇨̂ Δ ▻ σ /̂ ρ̂
ρ̂ ↑̂ = ρ̂ ↑̂ _

------------------------------------------------------------------------
-- Variables

-- Variables (de Bruijn indices).

infix 3 _∋_

data _∋_ : (Γ : Ctxt) → Type Γ → Set (i ⊔ u ⊔ e) where
  zero : ∀ {Γ σ}               → Γ ▻ σ ∋ σ /̂ ŵk
  suc  : ∀ {Γ σ τ} (x : Γ ∋ τ) → Γ ▻ σ ∋ τ /̂ ŵk

zero[_] : ∀ {Γ} σ → Γ ▻ σ ∋ σ /̂ ŵk
zero[ _ ] = zero

suc[_] : ∀ {Γ} σ {τ} → Γ ∋ τ → Γ ▻ σ ∋ τ /̂ ŵk
suc[ _ ] = suc

-- Interpretation of variables: a lookup function.

lookup : ∀ {Γ σ} → Γ ∋ σ → Value Γ σ
lookup zero    (γ , v) = v
lookup (suc x) (γ , v) = lookup x γ

-- Application of context morphisms to variables.

infixl 8 _/̂∋_

_/̂∋_ : ∀ {Γ Δ σ} → Γ ∋ σ → (ρ̂ : Γ ⇨̂ Δ) → Value Δ (σ /̂ ρ̂)
x /̂∋ ρ̂ = lookup x /̂Val ρ̂

------------------------------------------------------------------------
-- Equality

infix 4 _≅-Ctxt_ _≅-Type_ _≅-IType_ _≅-Value_ _≅-⇨̂_ _≅-∋_

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

record [Type] : Set (i ⊔ u ⊔ e) where
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

record [IType] : Set (i ⊔ u ⊔ e) where
  constructor [_]
  field
    {Γ}   : Ctxt
    {idx} : I
    σ     : IType Γ idx

_≅-IType_ : ∀ {Γ₁ i₁} (σ₁ : IType Γ₁ i₁)
              {Γ₂ i₂} (σ₂ : IType Γ₂ i₂) → Set _
σ₁ ≅-IType σ₂ = _≡_ {A = [IType]} [ σ₁ ] [ σ₂ ]

-- If the indices are equal, then _≅-IType_ coincides with _≡_.

≅-IType-⇒-≡ : ∀ {Γ i} {σ₁ σ₂ : IType Γ i} →
              σ₁ ≅-IType σ₂ → σ₁ ≡ σ₂
≅-IType-⇒-≡ P.refl = P.refl

-- Equality of values.

record [Value] : Set (i ⊔ u ⊔ e) where
  constructor [_]
  field
    {Γ} : Ctxt
    {σ} : Type Γ
    v   : Value Γ σ

_≅-Value_ : ∀ {Γ₁ σ₁} (v₁ : Value Γ₁ σ₁)
              {Γ₂ σ₂} (v₂ : Value Γ₂ σ₂) → Set _
v₁ ≅-Value v₂ = _≡_ {A = [Value]} [ v₁ ] [ v₂ ]

≅-Value-⇒-≡ : ∀ {Γ σ} {v₁ v₂ : Value Γ σ} →
              v₁ ≅-Value v₂ → v₁ ≡ v₂
≅-Value-⇒-≡ P.refl = P.refl

-- Equality of context morphisms.

record [⇨̂] : Set (i ⊔ u ⊔ e) where
  constructor [_]
  field
    {Γ Δ} : Ctxt
    ρ̂     : Γ ⇨̂ Δ

_≅-⇨̂_ : ∀ {Γ₁ Δ₁} (ρ̂₁ : Γ₁ ⇨̂ Δ₁)
          {Γ₂ Δ₂} (ρ̂₂ : Γ₂ ⇨̂ Δ₂) → Set _
ρ̂₁ ≅-⇨̂ ρ̂₂ = _≡_ {A = [⇨̂]} [ ρ̂₁ ] [ ρ̂₂ ]

≅-⇨̂-⇒-≡ : ∀ {Γ Δ} {ρ̂₁ ρ̂₂ : Γ ⇨̂ Δ} →
          ρ̂₁ ≅-⇨̂ ρ̂₂ → ρ̂₁ ≡ ρ̂₂
≅-⇨̂-⇒-≡ P.refl = P.refl

-- Equality of variables.

record [∋] : Set (i ⊔ u ⊔ e) where
  constructor [_]
  field
    {Γ} : Ctxt
    {σ} : Type Γ
    x   : Γ ∋ σ

_≅-∋_ : ∀ {Γ₁ σ₁} (x₁ : Γ₁ ∋ σ₁)
          {Γ₂ σ₂} (x₂ : Γ₂ ∋ σ₂) → Set _
x₁ ≅-∋ x₂ = _≡_ {A = [∋]} [ x₁ ] [ x₂ ]

≅-∋-⇒-≡ : ∀ {Γ σ} {x₁ x₂ : Γ ∋ σ} →
          x₁ ≅-∋ x₂ → x₁ ≡ x₂
≅-∋-⇒-≡ P.refl = P.refl

------------------------------------------------------------------------
-- Some congruence lemmas

▻-cong : ∀ {Γ₁ Γ₂ σ₁ σ₂} → σ₁ ≅-Type σ₂ → Γ₁ ▻ σ₁ ≅-Ctxt Γ₂ ▻ σ₂
▻-cong P.refl = P.refl

indexed-type-cong :
  ∀ {Γ₁} {σ₁ : Type Γ₁}
    {Γ₂} {σ₂ : Type Γ₂} →
  σ₁ ≅-Type σ₂ → indexed-type σ₁ ≅-IType indexed-type σ₂
indexed-type-cong P.refl = P.refl

îd-cong : ∀ {Γ₁ Γ₂} → Γ₁ ≅-Ctxt Γ₂ → îd[ Γ₁ ] ≅-⇨̂ îd[ Γ₂ ]
îd-cong P.refl = P.refl

∘̂-cong : ∀ {Γ₁ Δ₁ Ε₁} {ρ̂₁₁ : Γ₁ ⇨̂ Δ₁} {ρ̂₂₁ : Δ₁ ⇨̂ Ε₁}
           {Γ₂ Δ₂ Ε₂} {ρ̂₁₂ : Γ₂ ⇨̂ Δ₂} {ρ̂₂₂ : Δ₂ ⇨̂ Ε₂} →
         ρ̂₁₁ ≅-⇨̂ ρ̂₁₂ → ρ̂₂₁ ≅-⇨̂ ρ̂₂₂ → ρ̂₁₁ ∘̂ ρ̂₂₁ ≅-⇨̂ ρ̂₁₂ ∘̂ ρ̂₂₂
∘̂-cong P.refl P.refl = P.refl

/̂I-cong : ∀ {Γ₁ Δ₁ i₁} {σ₁ : IType Γ₁ i₁} {ρ̂₁ : Γ₁ ⇨̂ Δ₁}
            {Γ₂ Δ₂ i₂} {σ₂ : IType Γ₂ i₂} {ρ̂₂ : Γ₂ ⇨̂ Δ₂} →
          σ₁ ≅-IType σ₂ → ρ̂₁ ≅-⇨̂ ρ̂₂ → σ₁ /̂I ρ̂₁ ≅-IType σ₂ /̂I ρ̂₂
/̂I-cong P.refl P.refl = P.refl

/̂-cong : ∀ {Γ₁ Δ₁ σ₁} {ρ̂₁ : Γ₁ ⇨̂ Δ₁}
           {Γ₂ Δ₂ σ₂} {ρ̂₂ : Γ₂ ⇨̂ Δ₂} →
         σ₁ ≅-Type σ₂ → ρ̂₁ ≅-⇨̂ ρ̂₂ → σ₁ /̂ ρ̂₁ ≅-Type σ₂ /̂ ρ̂₂
/̂-cong P.refl P.refl = P.refl

/̂Val-cong : ∀ {Γ₁ Δ₁ σ₁} {v₁ : Value Γ₁ σ₁} {ρ̂₁ : Γ₁ ⇨̂ Δ₁}
              {Γ₂ Δ₂ σ₂} {v₂ : Value Γ₂ σ₂} {ρ̂₂ : Γ₂ ⇨̂ Δ₂} →
            v₁ ≅-Value v₂ → ρ̂₁ ≅-⇨̂ ρ̂₂ → v₁ /̂Val ρ̂₁ ≅-Value v₂ /̂Val ρ̂₂
/̂Val-cong P.refl P.refl = P.refl

ŵk-cong : ∀ {Γ₁} {σ₁ : Type Γ₁} {Γ₂} {σ₂ : Type Γ₂} →
          σ₁ ≅-Type σ₂ → ŵk[ σ₁ ] ≅-⇨̂ ŵk[ σ₂ ]
ŵk-cong P.refl = P.refl

ε̂-cong : ∀ {Δ₁ Δ₂} → Δ₁ ≅-Ctxt Δ₂ → ε̂[ Δ₁ ] ≅-⇨̂ ε̂[ Δ₂ ]
ε̂-cong P.refl = P.refl

▻̂-cong : ∀ {Γ₁ Δ₁ σ₁} {ρ̂₁ : Γ₁ ⇨̂ Δ₁} {v₁ : Value Δ₁ (σ₁ /̂ ρ̂₁)}
           {Γ₂ Δ₂ σ₂} {ρ̂₂ : Γ₂ ⇨̂ Δ₂} {v₂ : Value Δ₂ (σ₂ /̂ ρ̂₂)} →
         σ₁ ≅-Type σ₂ → ρ̂₁ ≅-⇨̂ ρ̂₂ → v₁ ≅-Value v₂ →
         ρ̂₁ ▻̂[ σ₁ ] v₁ ≅-⇨̂ ρ̂₂ ▻̂[ σ₂ ] v₂
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
         ρ̂₁ ≅-⇨̂ ρ̂₂ → σ₁ ≅-Type σ₂ → ρ̂₁ ↑̂ σ₁ ≅-⇨̂ ρ̂₂ ↑̂ σ₂
↑̂-cong P.refl P.refl = P.refl

zero-cong : ∀ {Γ₁} {σ₁ : Type Γ₁}
              {Γ₂} {σ₂ : Type Γ₂} →
            σ₁ ≅-Type σ₂ → zero[ σ₁ ] ≅-∋ zero[ σ₂ ]
zero-cong P.refl = P.refl

suc-cong :
  ∀ {Γ₁ σ₁ τ₁} {x₁ : Γ₁ ∋ τ₁}
    {Γ₂ σ₂ τ₂} {x₂ : Γ₂ ∋ τ₂} →
  σ₁ ≅-Type σ₂ → x₁ ≅-∋ x₂ → suc[ σ₁ ] x₁ ≅-∋ suc[ σ₂ ] x₂
suc-cong P.refl P.refl = P.refl

/̂∋-cong : ∀ {Γ₁ Δ₁ σ₁} {x₁ : Γ₁ ∋ σ₁} {ρ̂₁ : Γ₁ ⇨̂ Δ₁}
            {Γ₂ Δ₂ σ₂} {x₂ : Γ₂ ∋ σ₂} {ρ̂₂ : Γ₂ ⇨̂ Δ₂} →
          x₁ ≅-∋ x₂ → ρ̂₁ ≅-⇨̂ ρ̂₂ → x₁ /̂∋ ρ̂₁ ≅-Value x₂ /̂∋ ρ̂₂
/̂∋-cong P.refl P.refl = P.refl

------------------------------------------------------------------------
-- Some properties, all of which hold definitionally

-- _/̂_ preserves the index.

index-/̂ : ∀ {Γ Δ} (σ : Type Γ) (ρ̂ : Γ ⇨̂ Δ) →
          index (σ /̂ ρ̂) ≡ index σ
index-/̂ σ ρ̂ = P.refl

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

îd-↑̂ : ∀ {Γ} (σ : Type Γ) → îd ↑̂ σ ≅-⇨̂ îd[ Γ ▻ σ ]
îd-↑̂ σ = P.refl

-- _↑̂ distributes over _∘̂_.

↑̂-distrib : ∀ {Γ Δ Ε} (ρ̂₁ : Γ ⇨̂ Δ) (ρ̂₂ : Δ ⇨̂ Ε) σ →
            (ρ̂₁ ∘̂ ρ̂₂) ↑̂ σ ≅-⇨̂ ρ̂₁ ↑̂ σ ∘̂ ρ̂₂ ↑̂
↑̂-distrib ρ̂₁ ρ̂₂ σ = P.refl

-- ŵk is a left inverse of ŝub.

ŵk-∘̂-ŝub : ∀ {Γ σ} (v : Value Γ σ) → ŵk ∘̂ ŝub v ≅-⇨̂ îd
ŵk-∘̂-ŝub v = P.refl

-- First weakening under the head, and then replacing the head with
-- the new head, is the same as doing nothing.

ŵk-↑̂-∘̂-ŝub : ∀ {Γ} σ → ŵk ↑̂ ∘̂ ŝub proj₂ ≅-⇨̂ îd[ Γ ▻ σ ]
ŵk-↑̂-∘̂-ŝub σ = P.refl

-- ŵk commutes with arbitrary context morphisms (modulo lifting).

∘̂-ŵk : ∀ {Γ Δ} (ρ̂ : Γ ⇨̂ Δ) σ → ρ̂ ∘̂ ŵk[ σ /̂ ρ̂ ] ≅-⇨̂ ŵk[ σ ] ∘̂ ρ̂ ↑̂
∘̂-ŵk ρ̂ σ = P.refl

-- ŝub commutes with arbitrary context morphisms (modulo lifting).

ŝub-∘̂ : ∀ {Γ Δ σ} (ρ̂ : Γ ⇨̂ Δ) (v : Value Γ σ) →
        ŝub v ∘̂ ρ̂ ≅-⇨̂ ρ̂ ↑̂ ∘̂ ŝub (v /̂Val ρ̂)
ŝub-∘̂ ρ̂ v = P.refl

-- Laws relating _▻̂_, ĥead and t̂ail.

ĥead-▻̂ : ∀ {Γ Δ σ} (ρ̂ : Γ ⇨̂ Δ) (v : Value Δ (σ /̂ ρ̂)) →
         ĥead (ρ̂ ▻̂[ σ ] v) ≅-Value v
ĥead-▻̂ ρ̂ v = P.refl

t̂ail-▻̂ : ∀ {Γ Δ σ} (ρ̂ : Γ ⇨̂ Δ) (v : Value Δ (σ /̂ ρ̂)) →
         t̂ail (ρ̂ ▻̂[ σ ] v) ≅-⇨̂ ρ̂
t̂ail-▻̂ ρ̂ v = P.refl

t̂ail-▻̂-ĥead : ∀ {Γ Δ σ} (ρ̂ : Γ ▻ σ ⇨̂ Δ) → t̂ail ρ̂ ▻̂ ĥead ρ̂ ≅-⇨̂ ρ̂
t̂ail-▻̂-ĥead ρ̂ = P.refl

-- Law relating _▻̂_ and _∘̂_.

▻̂-∘̂ : ∀ {Γ Δ Ε σ} (ρ̂₁ : Γ ⇨̂ Δ) (ρ̂₂ : Δ ⇨̂ Ε) (v : Value Δ (σ /̂ ρ̂₁)) →
      (ρ̂₁ ▻̂[ σ ] v) ∘̂ ρ̂₂ ≅-⇨̂ (ρ̂₁ ∘̂ ρ̂₂) ▻̂ v /̂Val ρ̂₂
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
-- More properties

-- _▻_ is injective.

▻-injective : ∀ {Γ₁ σ₁ Γ₂ σ₂} →
              Γ₁ ▻ σ₁ ≅-Ctxt Γ₂ ▻ σ₂ → Γ₁ ≅-Ctxt Γ₂ × σ₁ ≅-Type σ₂
▻-injective P.refl = P.refl , P.refl

-- Equality of variables is decidable (if they refer to the same
-- context).

infix 4 _≟-∋_

_≟-∋_ : ∀ {Γ σ₁} (x₁ : Γ ∋ σ₁) {σ₂} (x₂ : Γ ∋ σ₂) →
        Dec (x₁ ≅-∋ x₂)
zero   ≟-∋ zero   = yes P.refl
zero   ≟-∋ suc _  = no λ ()
suc _  ≟-∋ zero   = no λ ()
suc x₁ ≟-∋ suc x₂ = Dec.map′ (suc-cong P.refl) helper (x₁ ≟-∋ x₂)
  where
  helper : ∀ {Γ₁ σ₁ τ₁} {x₁ : Γ₁ ∋ τ₁}
             {Γ₂ σ₂ τ₂} {x₂ : Γ₂ ∋ τ₂} →
           suc[ σ₁ ] x₁ ≅-∋ suc[ σ₂ ] x₂ → x₁ ≅-∋ x₂
  helper P.refl = P.refl
