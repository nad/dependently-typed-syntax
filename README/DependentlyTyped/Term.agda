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
open import Data.Unit
import deBruijn.Context
import deBruijn.TermLike
open import Function renaming (const to k)
open import Relation.Binary.PropositionalEquality as P using (_≡_; _≢_)
open import Relation.Nullary

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

  U : Spine → Set
  U ⋆           = ⊤
  U el          = U₀
  U (π sp₁ sp₂) = Σ (U sp₁) λ a → El a → U sp₂

  El : ∀ {sp} → U sp → Set
  El {⋆}         _       = U₀
  El {el}        a       = El₀ a
  El {π sp₁ sp₂} (a , b) = (x : El a) → El (b x)

Uni : Indexed-universe _ _ _
Uni = record { I = Spine; U = U; El = El }

-- Some synonyms/specialisations.

U-⋆ : U ⋆
U-⋆ = _

U-el : U₀ → U el
U-el = id

U-π : ∀ {sp₁} {sp₂} (a : U sp₁) → (El a → U sp₂) → U (π sp₁ sp₂)
U-π = _,_

------------------------------------------------------------------------
-- Contexts and variables

-- We get these for free.

open deBruijn.Context Uni public
open deBruijn.TermLike Uni hiding (_·_; ·-cong)

------------------------------------------------------------------------
-- Projections

-- Types with π-spines can be split up into a first and a second part.

ifst : ∀ {Γ sp₁ sp₂} → IType Γ (π sp₁ sp₂) → IType Γ sp₁
ifst σ γ = proj₁ (σ γ)

fst : ∀ {Γ sp₁ sp₂} → IType Γ (π sp₁ sp₂) → Type Γ
fst σ = , ifst σ

isnd : ∀ {Γ sp₁ sp₂} (σ : IType Γ (π sp₁ sp₂)) →
       IType (Γ ▻ fst σ) sp₂
isnd σ (γ , v) = proj₂ (σ γ) v

snd : ∀ {Γ sp₁ sp₂} (σ : IType Γ (π sp₁ sp₂)) → Type (Γ ▻ fst σ)
snd σ = , isnd σ

-- The split is correct.

π-fst-snd : ∀ {Γ sp₁ sp₂} (σ : IType Γ (π sp₁ sp₂)) →
            σ ≡ k U-π ˢ ifst σ ˢ c (isnd σ)
π-fst-snd σ = P.refl

------------------------------------------------------------------------
-- Well-typed terms

mutual

  infixl 9 _·_
  infix  4 _⊢_

  -- Terms.

  data _⊢_ (Γ : Ctxt) : Type Γ → Set where
    var : ∀ {σ} (x : Γ ∋ σ) → Γ ⊢ σ
    ƛ   : ∀ {σ τ} (t : Γ ▻ σ ⊢ τ) →
          Γ ⊢ , k U-π ˢ indexed-type σ ˢ c (indexed-type τ)
    _·_ : ∀ {sp₁ sp₂ σ}
          (t₁ : Γ ⊢ π sp₁ sp₂ , σ) (t₂ : Γ ⊢ fst σ) →
          Γ ⊢ snd σ /̂ ŝub ⟦ t₂ ⟧

  -- Semantics of terms.

  ⟦_⟧ : ∀ {Γ σ} → Γ ⊢ σ → Value Γ σ
  ⟦ var x   ⟧ γ = lookup x γ
  ⟦ ƛ t     ⟧ γ = λ v → ⟦ t ⟧ (γ , v)
  ⟦ t₁ · t₂ ⟧ γ = (⟦ t₁ ⟧ γ) (⟦ t₂ ⟧ γ)

-- Terms are "term-like".

Tm : Term-like _
Tm = record { _⊢_ = _⊢_; ⟦_⟧ = ⟦_⟧ }

open Term-like Tm public hiding (_⊢_; ⟦_⟧)

------------------------------------------------------------------------
-- Syntactic types

infix 4 _⊢_type

data _⊢_type (Γ : Ctxt) : Type Γ → Set where
  ⋆  : Γ ⊢ , k U-⋆ type
  el : (t : Γ ⊢ , k U-⋆) → Γ ⊢ , k U-el ˢ ⟦ t ⟧ type
  π  : ∀ {sp₁ sp₂ σ τ}
       (σ′ : Γ ⊢ sp₁ , σ type) (τ′ : Γ ▻ (, σ) ⊢ sp₂ , τ type) →
       Γ ⊢ , k U-π ˢ σ ˢ c τ type

-- Semantics of types.

⟦_⟧type : ∀ {Γ σ} → Γ ⊢ σ type → Type Γ
⟦_⟧type {σ = σ} _ = σ

-- We can project out the first and second components of a syntactic
-- Π-type.

fst′ : ∀ {Γ sp₁ sp₂} {σ : IType Γ (π sp₁ sp₂)} →
       Γ ⊢ , σ type → Γ ⊢ fst σ type
fst′ (π σ′ τ′) = σ′

snd′ : ∀ {Γ sp₁ sp₂} {σ : IType Γ (π sp₁ sp₂)} →
       Γ ⊢ , σ type → Γ ▻ fst σ ⊢ snd σ type
snd′ (π σ′ τ′) = τ′

------------------------------------------------------------------------
-- Examples

-- The polymorphic identity function.

identity : ∀ {Γ} →
           Γ ⊢ ⟦ π ⋆ (π (el (var zero)) (el (var (suc zero)))) ⟧type
identity = ƛ {σ = ⟦ ⋆ ⟧type} (ƛ {σ = ⟦ el (var zero) ⟧type} (var zero))

-- The polymorphic identity function, with the type written in a less
-- compact way.

identity′ : ∀ {Γ} →
            Γ ⊢ , k U-π ˢ k U-⋆ ˢ
                          c (k U-π ˢ (k U-el ˢ ⟦ var zero ⟧) ˢ
                                     c (k U-el ˢ ⟦ var (suc zero) ⟧))
identity′ = ƛ {σ = ⟦ ⋆ ⟧type} (ƛ {σ = ⟦ el (var zero) ⟧type} (var zero))

-- The polymorphic identity function applied to some variables from
-- the context.

identity· : ∀ {Γ} → Γ ▻ ⟦ ⋆ ⟧type ▻ ⟦ el (var zero) ⟧type ⊢
                    ⟦ el (var (suc zero)) ⟧type
identity· =
  ƛ {σ = ⟦ ⋆ ⟧type} (ƛ {σ = ⟦ el (var zero) ⟧type} (var zero)) ·
  var (suc zero) · var zero

------------------------------------------------------------------------
-- An observation

-- There are terms without syntactic types, assuming that U₀ is
-- inhabited and that no closed term computes to the given inhabitant.
-- (TODO: Is it possible to drop the last assumption? Can we prove
-- that no term in the empty context has type , U-⋆?)

term-without-type : (u : U₀) → ε ⊢ , k (U-π (U-el u) (k (U-el u)))
term-without-type u = ƛ (var zero)

no-type : (u : U₀) → ∄ (λ (t : ε ⊢ , k U-⋆) → ⟦ t ⟧ _ ≡ u) →
          ¬ ε ⊢ , k (U-π (U-el u) (k (U-el u))) type
no-type u ⟦t⟧≢u σ′ = helper σ′ P.refl
  where
  helper : ∀ {σ} → ε ⊢ , σ type → σ ≢ k (U-π (U-el u) (k (U-el u)))
  helper (π (el t) (el t′)) eq = ⟦t⟧≢u (t , ⟦t⟧≡u)
    where
    ⟦t⟧≡u : ⟦ t ⟧ _ ≡ u
    ⟦t⟧≡u = P.cong (λ f → proj₁ (f _)) eq

-- One could avoid this situation by annotating lambdas with the
-- (syntactic) type of their domain. I tried this, and found it to be
-- awkward. One case of the function
-- README.DependentlyTyped.Kripke-model.Definition.řeify returns a
-- lambda, and I didn't find a way to synthesise the annotation
-- without supplying a syntactic type to řeify (and hence also to
-- V̌alue).

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
  ∀ {Γ₁ sp₁₁ sp₂₁ σ₁} {v₁ : Value Γ₁ (fst σ₁)}
    {f₁ : Value Γ₁ (π sp₁₁ sp₂₁ , σ₁)}
    {Γ₂ sp₁₂ sp₂₂ σ₂} {v₂ : Value Γ₂ (fst σ₂)}
    {f₂ : Value Γ₂ (π sp₁₂ sp₂₂ , σ₂)} →
  f₁ ≅-Value f₂ → v₁ ≅-Value v₂ → f₁ ˢ v₁ ≅-Value f₂ ˢ v₂
ˢ-cong P.refl P.refl = P.refl

curry-cong :
  ∀ {Γ₁ σ₁ τ₁} {v₁ : Value (Γ₁ ▻ σ₁) τ₁}
    {Γ₂ σ₂ τ₂} {v₂ : Value (Γ₂ ▻ σ₂) τ₂} →
  v₁ ≅-Value v₂ → c v₁ ≅-Value c v₂
curry-cong P.refl = P.refl

⋆-cong : {Γ₁ Γ₂ : Ctxt} →
         Γ₁ ≅-Ctxt Γ₂ → ⋆ {Γ = Γ₁} ≅-type ⋆ {Γ = Γ₂}
⋆-cong P.refl = P.refl

el-cong : ∀ {Γ₁} {t₁ : Γ₁ ⊢ , k U-⋆}
            {Γ₂} {t₂ : Γ₂ ⊢ , k U-⋆} →
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

ƛ-cong : ∀ {Γ₁ σ₁ τ₁} {t₁ : Γ₁ ▻ σ₁ ⊢ τ₁}
           {Γ₂ σ₂ τ₂} {t₂ : Γ₂ ▻ σ₂ ⊢ τ₂} →
         t₁ ≅-⊢ t₂ → ƛ t₁ ≅-⊢ ƛ t₂
ƛ-cong P.refl = P.refl

·-cong : ∀ {Γ₁ sp₁₁ sp₂₁ σ₁}
           {t₁₁ : Γ₁ ⊢ π sp₁₁ sp₂₁ , σ₁} {t₂₁ : Γ₁ ⊢ fst σ₁}
           {Γ₂ sp₁₂ sp₂₂ σ₂}
           {t₁₂ : Γ₂ ⊢ π sp₁₂ sp₂₂ , σ₂} {t₂₂ : Γ₂ ⊢ fst σ₂} →
           t₁₁ ≅-⊢ t₁₂ → t₂₁ ≅-⊢ t₂₂ → t₁₁ · t₂₁ ≅-⊢ t₁₂ · t₂₂
·-cong P.refl P.refl = P.refl
