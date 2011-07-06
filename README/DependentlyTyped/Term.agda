------------------------------------------------------------------------
-- A well-typed representation of a dependently typed language
------------------------------------------------------------------------

{-# OPTIONS --universe-polymorphism #-}

-- The code is parametrised by an arbitrary (small, unindexed)
-- universe.

import Level
open import Universe

module README.DependentlyTyped.Term
  (Uni₀ : Universe Level.zero Level.zero)
  where

open import Data.Product as Prod renaming (curry to c; uncurry to uc)
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
-- An indexed universe

-- A type which represents the "spine" of a universe code (or type).

data Spine : Set where
  ⋆ el : Spine
  π    : (sp₁ sp₂ : Spine) → Spine

-- The universe contains the universe above and is closed under
-- Π-types.

mutual

  data U : Spine → Set where
    ⋆  : U ⋆
    el : (a : U₀) → U el
    π  : ∀ {sp₁ sp₂} (a : U sp₁) (b : El a → U sp₂) → U (π sp₁ sp₂)

  El : ∀ {sp} → U sp → Set
  El ⋆       = U₀
  El (el a)  = El₀ a
  El (π a b) = (x : El a) → El (b x)

Uni : Indexed-universe _ _ _
Uni = record { I = Spine; U = U; El = El }

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
    ⋆  : Γ ⊢ , k ⋆ type
    el : (t : Γ ⊢ , k ⋆) → Γ ⊢ , k U.el ˢ ⟦ t ⟧ type
    π  : ∀ {sp₁ sp₂ σ τ}
         (σ′ : Γ ⊢ sp₁ , σ type) (τ′ : Γ ▻ (, σ) ⊢ sp₂ , τ type) →
         Γ ⊢ , k U.π ˢ σ ˢ c τ type

  -- Terms.
  --
  -- Note that the lambda is annotated with the (syntactic) type of
  -- its domain. Reason: Without this annotation closed terms are not
  -- guaranteed to have any syntactic type. Example (assuming
  -- nat : U₀):
  --
  --   ƛ (var zero) : ε ⊢ , k (U.π (U.el nat) (k (U.el nat)))
  --
  -- There is no corresponding syntactic type, because there is no
  -- term t : ε ⊢ , k U.⋆ such that ⟦ t ⟧ _ = nat.

  data _⊢_ (Γ : Ctxt) : Type Γ → Set where
    var : ∀ {σ} (x : Γ ∋ σ) → Γ ⊢ σ
    ƛ   : ∀ {σ τ}
          (σ′ : Γ ⊢ σ type) (t : Γ ▻ σ ⊢ τ) →
          Γ ⊢ , k U.π ˢ indexed-type σ ˢ c (indexed-type τ)
    _·_ : ∀ {σ τ}
          (t₁ : Γ ⊢ , k U.π ˢ indexed-type σ ˢ proj₂ τ) (t₂ : Γ ⊢ σ) →
          Γ ⊢ Prod.map id uc τ /̂ ŝub ⟦ t₂ ⟧

  -- Semantics of terms.

  ⟦_⟧ : ∀ {Γ σ} → Γ ⊢ σ → Value Γ σ
  ⟦ var x   ⟧ γ = lookup x γ
  ⟦ ƛ _ t   ⟧ γ = λ v → ⟦ t ⟧ (γ , v)
  ⟦ t₁ · t₂ ⟧ γ = (⟦ t₁ ⟧ γ) (⟦ t₂ ⟧ γ)

-- Semantics of types.

⟦_⟧type : ∀ {Γ σ} → Γ ⊢ σ type → Type Γ
⟦_⟧type {σ = σ} _ = σ

-- Terms are "term-like".

Tm : Term-like _
Tm = record { _⊢_ = _⊢_; ⟦_⟧ = ⟦_⟧ }

open Term-like Tm public hiding (_⊢_; ⟦_⟧)

------------------------------------------------------------------------
-- Examples

-- The polymorphic identity function.

identity : ∀ {Γ} →
           Γ ⊢ ⟦ π ⋆ (π (el (var zero)) (el (var (suc zero)))) ⟧type
identity = ƛ ⋆ (ƛ (el (var zero)) (var zero))

-- The polymorphic identity function, with the type written in a less
-- compact way.

identity′ : ∀ {Γ} →
            Γ ⊢ , k U.π ˢ k U.⋆ ˢ
                          c (k U.π ˢ (k U.el ˢ ⟦ var zero ⟧) ˢ
                                     c (k U.el ˢ ⟦ var (suc zero) ⟧))
identity′ = ƛ ⋆ (ƛ (el (var zero)) (var zero))

-- The polymorphic identity function applied to some variables from
-- the context.

identity· : ∀ {Γ} → Γ ▻ ⟦ ⋆ ⟧type ▻ ⟦ el (var zero) ⟧type ⊢
                    ⟦ el (var (suc zero)) ⟧type
identity· =
  ƛ ⋆ (ƛ (el (var zero)) (var zero)) · var (suc zero) · var zero

-- In "Outrageous but Meaningful Coincidences" Conor McBride suggests
-- that ƛ should be defined with a curried τ (here an uncurried τ is
-- used). However, with a curried τ the definition of identity·
-- contains unsolved meta-variables (when a certain version of Agda is
-- used).

------------------------------------------------------------------------
-- Projections

-- Types with π-spines can be split up into a first and a second part.

ifst : ∀ {Γ sp₁ sp₂} → IType Γ (π sp₁ sp₂) → IType Γ sp₁
ifst σ γ with σ γ
... | π a b = a

fst : ∀ {Γ sp₁ sp₂} → IType Γ (π sp₁ sp₂) → Type Γ
fst σ = , ifst σ

isnd : ∀ {Γ sp₁ sp₂} (σ : IType Γ (π sp₁ sp₂)) →
       IType (Γ ▻ fst σ) sp₂
isnd σ (γ , v) with σ γ
... | π a b = b v

snd : ∀ {Γ sp₁ sp₂} (σ : IType Γ (π sp₁ sp₂)) → Type (Γ ▻ fst σ)
snd σ = , isnd σ

abstract

  -- The split is correct (assuming extensionality).

  π-fst-snd :
    P.Extensionality Level.zero Level.zero →
    ∀ {Γ sp₁ sp₂} (σ : IType Γ (π sp₁ sp₂)) →
    σ ≡ k U.π ˢ ifst σ ˢ c (isnd σ)
  π-fst-snd ext σ = ext helper
    where
    helper : ∀ γ → σ γ ≡ U.π (ifst σ γ) (λ v → isnd σ (γ , v))
    helper γ with σ γ
    helper γ | π a b = P.refl

-- We can also project out the first and second components of a
-- syntactic Π-type.

fst′ : ∀ {Γ sp₁ sp₂} {σ : IType Γ (π sp₁ sp₂)} →
       Γ ⊢ , σ type → Γ ⊢ fst σ type
fst′ (π σ′ τ′) = σ′

snd′ : ∀ {Γ sp₁ sp₂} {σ : IType Γ (π sp₁ sp₂)} →
       Γ ⊢ , σ type → Γ ▻ fst σ ⊢ snd σ type
snd′ (π σ′ τ′) = τ′

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

-- Some congruence lemmas.

-- Note that _ˢ_ and curry are the semantic counterparts of
-- application and abstraction.

ˢ-cong :
  ∀ {Γ₁ σ₁ τ₁} {v₁ : Value Γ₁ σ₁}
    {f₁ : Value Γ₁ (, k U.π ˢ indexed-type σ₁ ˢ c (indexed-type τ₁))}
    {Γ₂ σ₂ τ₂} {v₂ : Value Γ₂ σ₂}
    {f₂ : Value Γ₂ (, k U.π ˢ indexed-type σ₂ ˢ c (indexed-type τ₂))} →
  τ₁ ≅-Type τ₂ → f₁ ≅-Value f₂ → v₁ ≅-Value v₂ →
  f₁ ˢ v₁ ≅-Value f₂ ˢ v₂
ˢ-cong P.refl P.refl P.refl = P.refl

curry-cong :
  ∀ {Γ₁ σ₁ τ₁} {v₁ : Value (Γ₁ ▻ σ₁) τ₁}
    {Γ₂ σ₂ τ₂} {v₂ : Value (Γ₂ ▻ σ₂) τ₂} →
  v₁ ≅-Value v₂ → c v₁ ≅-Value c v₂
curry-cong P.refl = P.refl

⋆-cong : {Γ₁ Γ₂ : Ctxt} →
         Γ₁ ≅-Ctxt Γ₂ → ⋆ {Γ = Γ₁} ≅-type ⋆ {Γ = Γ₂}
⋆-cong P.refl = P.refl

el-cong : ∀ {Γ₁} {t₁ : Γ₁ ⊢ , k ⋆}
            {Γ₂} {t₂ : Γ₂ ⊢ , k ⋆} →
          t₁ ≅-⊢ t₂ → el t₁ ≅-type el t₂
el-cong P.refl = P.refl

π-cong : ∀ {Γ₁ σ₁ τ₁} {σ′₁ : Γ₁ ⊢ σ₁ type} {τ′₁ : Γ₁ ▻ σ₁ ⊢ τ₁ type}
           {Γ₂ σ₂ τ₂} {σ′₂ : Γ₂ ⊢ σ₂ type} {τ′₂ : Γ₂ ▻ σ₂ ⊢ τ₂ type} →
         σ′₁ ≅-type σ′₂ → τ′₁ ≅-type τ′₂ → π σ′₁ τ′₁ ≅-type π σ′₂ τ′₂
π-cong P.refl P.refl = P.refl

var-cong : ∀ {Γ₁ σ₁} {x₁ : Γ₁ ∋ σ₁}
             {Γ₂ σ₂} {x₂ : Γ₂ ∋ σ₂} →
           x₁ ≅-∋ x₂ → var x₁ ≅-⊢ var x₂
var-cong P.refl = P.refl

ƛ-cong : ∀ {Γ₁ σ₁ τ₁} {σ′₁ : Γ₁ ⊢ σ₁ type} {t₁ : Γ₁ ▻ σ₁ ⊢ τ₁}
           {Γ₂ σ₂ τ₂} {σ′₂ : Γ₂ ⊢ σ₂ type} {t₂ : Γ₂ ▻ σ₂ ⊢ τ₂} →
         σ′₁ ≅-type σ′₂ → t₁ ≅-⊢ t₂ → ƛ σ′₁ t₁ ≅-⊢ ƛ σ′₂ t₂
ƛ-cong P.refl P.refl = P.refl

-- Previously the following lemma was more general, with heterogeneous
-- input equalities, at the cost of an extra input equality of type
-- τ₁ ≅-Curried-Type τ₂. (_≅-Curried-Type_ has been removed.)

·-cong :
  ∀ {Γ σ}
    {τ : ∃ λ sp → (γ : Env Γ) → El (indexed-type σ γ) → U sp}
    {t₂₁ t₂₂ : Γ ⊢ σ}
    {t₁₁ t₁₂ : Γ ⊢ , k U.π ˢ indexed-type σ ˢ proj₂ τ} →
  t₁₁ ≅-⊢ t₁₂ → t₂₁ ≅-⊢ t₂₂ → t₁₁ · t₂₁ ≅-⊢ t₁₂ · t₂₂
·-cong P.refl P.refl = P.refl
