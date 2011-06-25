------------------------------------------------------------------------
-- A well-typed representation of a dependently typed language
------------------------------------------------------------------------

{-# OPTIONS --universe-polymorphism #-}

-- The code is parametrised by an arbitrary (small) universe.

import Level
open import Universe

module README.DependentlyTyped.Term
  (Uni₀ : Universe Level.zero Level.zero)
  where

open import Data.Product renaming (curry to c; uncurry to uc)
import deBruijn.Context
import deBruijn.TermLike
open import Function renaming (const to k)
open import Relation.Binary.PropositionalEquality as P using (_≡_)

------------------------------------------------------------------------
-- Wrapper types

-- Used to make El "constructor-headed", which in turn makes Agda
-- infer more types for us.

record U₀ : Set where
  field a : Universe.U Uni₀

record El₀ (a : U₀) : Set where
  field El : Universe.El Uni₀ (U₀.a a)

------------------------------------------------------------------------
-- Some universes

-- The first universe contains the universe above and is closed under
-- Π-types.

mutual

  data U₁ : Set where
    ⋆   : U₁
    el₀ : (a : U₀) → U₁
    π   : (a : U₁) (b : El₁ a → U₁) → U₁

  El₁ : U₁ → Set
  El₁ ⋆       = U₀
  El₁ (el₀ a) = El₀ a
  El₁ (π a b) = (x : El₁ a) → El₁ (b x)

-- The second universe also contains the first.

data U₂ : Set where
  u₁  : U₂
  el₁ : (a : U₁) → U₂

El₂ : U₂ → Set
El₂ u₁      = U₁
El₂ (el₁ a) = El₁ a

-- The second universe is the basis of the language below.

Uni : Universe _ _
Uni = record { U = U₂; El = El₂ }

------------------------------------------------------------------------
-- Contexts and variables

-- We get these for free.

open deBruijn.Context Uni public
open deBruijn.TermLike Uni hiding (_·_; ·-cong)

------------------------------------------------------------------------
-- Well-typed terms

mutual

  infixl 9 _·_
  infix  4 _⊢_type _⊢_

  -- Types.

  data _⊢_type (Γ : Ctxt) : Type Γ → Set where
    ⋆  : Γ ⊢ k u₁ type
    el : (t : Γ ⊢ k (el₁ ⋆)) → Γ ⊢ k (el₁ ∘ el₀) ˢ ⟦ t ⟧ type
    π  : ∀ {σ τ}
         (σ′ : Γ ⊢ k el₁ ˢ σ type)
         (τ′ : Γ ▻ k el₁ ˢ σ ⊢ k el₁ ˢ τ type) →
         Γ ⊢ k el₁ ˢ (k π ˢ σ ˢ c τ) type

  -- Terms.

  data _⊢_ (Γ : Ctxt) : Type Γ → Set where
    var  : ∀ {σ} (x : Γ ∋ σ) → Γ ⊢ σ
    ƛ    : ∀ {σ τ}
           (σ′ : Γ ⊢ k el₁ ˢ σ type)
           (t : Γ ▻ k el₁ ˢ σ ⊢ k el₁ ˢ τ) →
           Γ ⊢ k el₁ ˢ (k U₁.π ˢ σ ˢ c τ)
    _·_  : ∀ {σ τ}
           (t₁ : Γ ⊢ k el₁ ˢ (k U₁.π ˢ σ ˢ τ))
           (t₂ : Γ ⊢ k el₁ ˢ σ) →
           Γ ⊢ k el₁ ˢ (τ ˢ ⟦ t₂ ⟧)
           -- Γ ⊢ _/̂_ {Γ = _ ▻ k el₁ ˢ σ}
           --         (k el₁ ˢ uc τ)
           --         (ŝub {σ = k el₁ ˢ σ} ⟦ t₂ ⟧)
    ty   : ∀ {σ} (σ′ : Γ ⊢ k el₁ ˢ σ type) → Γ ⊢ k u₁

  -- Semantics of terms.

  ⟦_⟧ : ∀ {Γ σ} → Γ ⊢ σ → Value Γ σ
  ⟦ var x        ⟧ = lookup x
  ⟦ ƛ _ t        ⟧ = c ⟦ t ⟧
  ⟦ t₁ · t₂      ⟧ = ⟦ t₁ ⟧ ˢ ⟦ t₂ ⟧
  ⟦ ty {σ = σ} _ ⟧ = σ

-- Turns a syntactic type into a semantic type.

⟦_⟧type : ∀ {Γ σ} → Γ ⊢ σ type → Type Γ
⟦_⟧type {σ = σ} _ = σ

-- Terms are "term-like".

Tm : Term-like _
Tm = record { _⊢_ = _⊢_; ⟦_⟧ = ⟦_⟧ }

open Term-like Tm public hiding (_⊢_; ⟦_⟧)

------------------------------------------------------------------------
-- Examples

-- The identity function.

identity :
  ∀ {Γ} →
  Γ ▻ k (el₁ ⋆) ⊢
  ⟦ π (el (var zero[ k (el₁ ⋆) ])) (el (var (suc zero))) ⟧type
identity = ƛ (el (var zero)) (var zero)

-- The identity function applied to some variable from the context.

identity· :
  ∀ {Γ} →
  Γ ▻ k (el₁ ⋆) ▻ ⟦ el (var zero[ k (el₁ ⋆) ]) ⟧type ⊢
  ⟦ el (var (suc[ ⟦ el (var zero[ k (el₁ ⋆) ]) ⟧type ]
             zero[ k (el₁ ⋆) ])) ⟧type
identity· = ƛ (el (var (suc zero))) (var zero) · var zero

-- In "Outrageous but Meaningful Coincidences" Conor McBride suggests
-- that ƛ should be defined with a curried τ (here an uncurried τ is
-- used). However, with a curried τ the definition of identity·
-- contains unsolved meta-variables (when a certain version of Agda is
-- used).

------------------------------------------------------------------------
-- Equality

-- Syntactic type telescopes.

record [type] : Set where
  constructor [_]
  field
    {Γ} : Ctxt
    {σ} : Type Γ
    σ′  : Γ ⊢ σ type

-- Equality of syntactic types.

infix 4 _≅-type_

_≅-type_ : ∀ {Γ₁ σ₁} (σ′₁ : Γ₁ ⊢ σ₁ type)
             {Γ₂ σ₂} (σ′₂ : Γ₂ ⊢ σ₂ type) → Set
σ′₁ ≅-type σ′₂ = [type].[_] σ′₁ ≡ [ σ′₂ ]

-- If the indices are equal, then _≅-type_ coincides with _≡_.

≅-type-⇒-≡ : ∀ {Γ σ} {σ′₁ σ′₂ : Γ ⊢ σ type} →
             σ′₁ ≅-type σ′₂ → σ′₁ ≡ σ′₂
≅-type-⇒-≡ P.refl = P.refl

-- Certain uses of substitutivity can be removed.

drop-subst-⊢-type :
  ∀ {a} {A : Set a} {x₁ x₂ : A} {Γ}
  (f : A → Type Γ) {σ′} (eq : x₁ ≡ x₂) →
  P.subst (λ x → Γ ⊢ f x type) eq σ′ ≅-type σ′
drop-subst-⊢-type f P.refl = P.refl

-- -- Some congruence lemmas.

-- -- Note that _ˢ_ and curry are the semantic counterparts of
-- -- application and abstraction.

-- ˢ-cong :
--   ∀ {Γ₁ σ₁ τ₁} {f₁ : Value Γ₁ (k U.π ˢ σ₁ ˢ c τ₁)} {v₁ : Value Γ₁ σ₁}
--     {Γ₂ σ₂ τ₂} {f₂ : Value Γ₂ (k U.π ˢ σ₂ ˢ c τ₂)} {v₂ : Value Γ₂ σ₂} →
--   τ₁ ≅-Type τ₂ → f₁ ≅-Value f₂ → v₁ ≅-Value v₂ →
--   f₁ ˢ v₁ ≅-Value f₂ ˢ v₂
-- ˢ-cong P.refl P.refl P.refl = P.refl

-- curry-cong :
--   ∀ {Γ₁ σ₁ τ₁} {v₁ : Value (Γ₁ ▻ σ₁) τ₁}
--     {Γ₂ σ₂ τ₂} {v₂ : Value (Γ₂ ▻ σ₂) τ₂} →
--   v₁ ≅-Value v₂ → c v₁ ≅-Value c v₂
-- curry-cong P.refl = P.refl

-- ⋆-cong : {Γ₁ Γ₂ : Ctxt} →
--          Γ₁ ≅-Ctxt Γ₂ → ⋆ {Γ = Γ₁} ≅-type ⋆ {Γ = Γ₂}
-- ⋆-cong P.refl = P.refl

-- el-cong : ∀ {Γ₁} {t₁ : Γ₁ ⊢ k ⋆}
--             {Γ₂} {t₂ : Γ₂ ⊢ k ⋆} →
--           t₁ ≅-⊢ t₂ → el t₁ ≅-type el t₂
-- el-cong P.refl = P.refl

-- π-cong : ∀ {Γ₁ σ₁ τ₁} {σ′₁ : Γ₁ ⊢ σ₁ type} {τ′₁ : Γ₁ ▻ σ₁ ⊢ τ₁ type}
--            {Γ₂ σ₂ τ₂} {σ′₂ : Γ₂ ⊢ σ₂ type} {τ′₂ : Γ₂ ▻ σ₂ ⊢ τ₂ type} →
--          σ′₁ ≅-type σ′₂ → τ′₁ ≅-type τ′₂ → π σ′₁ τ′₁ ≅-type π σ′₂ τ′₂
-- π-cong P.refl P.refl = P.refl

-- var-cong : ∀ {Γ₁ σ₁} {x₁ : Γ₁ ∋ σ₁}
--              {Γ₂ σ₂} {x₂ : Γ₂ ∋ σ₂} →
--            x₁ ≅-∋ x₂ → var x₁ ≅-⊢ var x₂
-- var-cong P.refl = P.refl

-- ƛ-cong : ∀ {Γ₁ σ₁ τ₁} {σ′₁ : Γ₁ ⊢ σ₁ type} {t₁ : Γ₁ ▻ σ₁ ⊢ τ₁}
--            {Γ₂ σ₂ τ₂} {σ′₂ : Γ₂ ⊢ σ₂ type} {t₂ : Γ₂ ▻ σ₂ ⊢ τ₂} →
--          σ′₁ ≅-type σ′₂ → t₁ ≅-⊢ t₂ → ƛ σ′₁ t₁ ≅-⊢ ƛ σ′₂ t₂
-- ƛ-cong P.refl P.refl = P.refl

-- -- Previously the following lemma was more general, with heterogeneous
-- -- input equalities, at the cost of an extra input equality of type
-- -- τ₁ ≅-Curried-Type τ₂. (_≅-Curried-Type_ has been removed.)

-- ·-cong : ∀ {Γ σ τ} {t₁₁ t₁₂ : Γ ⊢ k U.π ˢ σ ˢ τ} {t₂₁ t₂₂ : Γ ⊢ σ} →
--          t₁₁ ≅-⊢ t₁₂ → t₂₁ ≅-⊢ t₂₂ → t₁₁ · t₂₁ ≅-⊢ t₁₂ · t₂₂
-- ·-cong P.refl P.refl = P.refl
