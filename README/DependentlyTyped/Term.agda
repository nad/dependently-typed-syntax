------------------------------------------------------------------------
-- A well-typed representation of a dependently typed language
------------------------------------------------------------------------

-- The code is parametrised by an arbitrary (small) universe.

open import Level using (zero)
open import Universe

module README.DependentlyTyped.Term (Uni₀ : Universe zero zero) where

open import Data.Product renaming (curry to c; uncurry to uc)
import deBruijn.Context
import deBruijn.TermLike
open import Function renaming (const to k)
open import Relation.Binary.HeterogeneousEquality as H using (_≅_)
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
-- A universe

-- This universe contains the universe above and is closed under
-- Π-types.

mutual

  data U : Set where
    ⋆  : U
    el : (a : U₀) → U
    π  : (a : U) (b : El a → U) → U

  El : U → Set
  El ⋆       = U₀
  El (el a)  = El₀ a
  El (π a b) = (x : El a) → El (b x)

Uni : Universe _ _
Uni = record { U = U; El = El }

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
    ⋆  : Γ ⊢ k ⋆ type
    el : (t : Γ ⊢ k ⋆) → Γ ⊢ k el ˢ ⟦ t ⟧ type
    π  : ∀ {σ τ} (σ′ : Γ ⊢ σ type) (τ′ : Γ ▻ σ ⊢ τ type) →
         Γ ⊢ k π ˢ σ ˢ c τ type

  -- Terms.

  data _⊢_ (Γ : Ctxt) : Type Γ → Set where
    var : ∀ {σ} (x : Γ ∋ σ) → Γ ⊢ σ
    ƛ   : ∀ {σ τ}
          (σ′ : Γ ⊢ σ type) (t : Γ ▻ σ ⊢ uc τ) → Γ ⊢ k U.π ˢ σ ˢ τ
    _·_ : ∀ {σ τ}
          (t₁ : Γ ⊢ k U.π ˢ σ ˢ τ) (t₂ : Γ ⊢ σ) → Γ ⊢ uc τ /̂ ŝub ⟦ t₂ ⟧

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
-- Some congruence lemmas

k-el-ˢ-cong : ∀ {Γ₁} {σ₁ : Env Γ₁ → U₀}
                {Γ₂} {σ₂ : Env Γ₂ → U₀} →
              Γ₁ ≡ Γ₂ → σ₁ ≅ σ₂ → k U.el ˢ σ₁ ≅ k U.el ˢ σ₂
k-el-ˢ-cong P.refl H.refl = H.refl

⋆-cong : {Γ₁ Γ₂ : Ctxt} →
         Γ₁ ≡ Γ₂ → _⊢_type.⋆ {Γ = Γ₁} ≅ _⊢_type.⋆ {Γ = Γ₂}
⋆-cong P.refl = H.refl

el-cong : ∀ {Γ₁} {t₁ : Γ₁ ⊢ k ⋆}
            {Γ₂} {t₂ : Γ₂ ⊢ k ⋆} →
          Γ₁ ≡ Γ₂ → t₁ ≅ t₂ → _⊢_type.el t₁ ≅ _⊢_type.el t₂
el-cong P.refl H.refl = H.refl

π-cong : ∀ {Γ₁ σ₁ τ₁} {σ′₁ : Γ₁ ⊢ σ₁ type} {τ′₁ : Γ₁ ▻ σ₁ ⊢ τ₁ type}
           {Γ₂ σ₂ τ₂} {σ′₂ : Γ₂ ⊢ σ₂ type} {τ′₂ : Γ₂ ▻ σ₂ ⊢ τ₂ type} →
         Γ₁ ≡ Γ₂ → σ₁ ≅ σ₂ → τ₁ ≅ τ₂ → σ′₁ ≅ σ′₂ → τ′₁ ≅ τ′₂ →
         _⊢_type.π σ′₁ τ′₁ ≅ _⊢_type.π σ′₂ τ′₂
π-cong P.refl H.refl H.refl H.refl H.refl = H.refl

var-cong : ∀ {Γ₁ σ₁} {x₁ : Γ₁ ∋ σ₁}
             {Γ₂ σ₂} {x₂ : Γ₂ ∋ σ₂} →
           Γ₁ ≡ Γ₂ → σ₁ ≅ σ₂ → x₁ ≅ x₂ → var x₁ ≅ var x₂
var-cong P.refl H.refl H.refl = H.refl

ƛ-cong : ∀ {Γ₁ σ₁ τ₁} {σ′₁ : Γ₁ ⊢ σ₁ type} {t₁ : Γ₁ ▻ σ₁ ⊢ uc τ₁}
           {Γ₂ σ₂ τ₂} {σ′₂ : Γ₂ ⊢ σ₂ type} {t₂ : Γ₂ ▻ σ₂ ⊢ uc τ₂} →
         Γ₁ ≡ Γ₂ → σ₁ ≅ σ₂ → τ₁ ≅ τ₂ → σ′₁ ≅ σ′₂ → t₁ ≅ t₂ →
         ƛ {τ = τ₁} σ′₁ t₁ ≅ ƛ {τ = τ₂} σ′₂ t₂
ƛ-cong P.refl H.refl H.refl H.refl H.refl = H.refl

·-cong : ∀ {Γ₁ σ₁ τ₁} {t₁₁ : Γ₁ ⊢ k U.π ˢ σ₁ ˢ τ₁} {t₂₁ : Γ₁ ⊢ σ₁}
           {Γ₂ σ₂ τ₂} {t₁₂ : Γ₂ ⊢ k U.π ˢ σ₂ ˢ τ₂} {t₂₂ : Γ₂ ⊢ σ₂} →
         Γ₁ ≡ Γ₂ → σ₁ ≅ σ₂ → τ₁ ≅ τ₂ → t₁₁ ≅ t₁₂ → t₂₁ ≅ t₂₂ →
         t₁₁ · t₂₁ ≅ t₁₂ · t₂₂
·-cong P.refl H.refl H.refl H.refl H.refl = H.refl
