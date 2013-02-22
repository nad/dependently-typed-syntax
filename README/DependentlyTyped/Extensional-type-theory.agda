------------------------------------------------------------------------
-- If the "Outrageous but Meaningful Coincidences" approach is used to
-- formalise a language, then you can end up with an extensional type
-- theory (with equality reflection)
------------------------------------------------------------------------

module README.DependentlyTyped.Extensional-type-theory where

open import Data.Empty
open import Data.Product renaming (curry to c)
open import Data.Unit
import deBruijn.Context
open import Function hiding (_∋_) renaming (const to k)
import Level
import Relation.Binary.PropositionalEquality as P
open import Universe

------------------------------------------------------------------------
-- A non-indexed universe

mutual

  data U : Set where
    empty : U
    π     : (a : U) (b : El a → U) → U

  El : U → Set
  El empty   = ⊥
  El (π a b) = (x : El a) → El (b x)

Uni : Indexed-universe _ _ _
Uni = record { I = ⊤; U = λ _ → U; El = El }

------------------------------------------------------------------------
-- Contexts and variables

-- We get these for free.

open deBruijn.Context Uni public
  renaming (_·_ to _⊙_; ·-cong to ⊙-cong)

-- Some abbreviations.

⟨empty⟩ : ∀ {Γ} → Type Γ
⟨empty⟩ = , λ _ → empty

⟨π⟩ : ∀ {Γ} (σ : Type Γ) → Type (Γ ▻ σ) → Type Γ
⟨π⟩ σ τ = , k π ˢ indexed-type σ ˢ c (indexed-type τ)

⟨π̂⟩ : ∀ {Γ} (σ : Type Γ) →
      ((γ : Env Γ) → El (indexed-type σ γ) → U) → Type Γ
⟨π̂⟩ σ τ = , k π ˢ indexed-type σ ˢ τ

------------------------------------------------------------------------
-- Well-typed terms

mutual

  infixl 9 _·_
  infix  4 _⊢_

  -- Terms.

  data _⊢_ (Γ : Ctxt) : Type Γ → Set where
    var : ∀ {σ} (x : Γ ∋ σ) → Γ ⊢ σ
    ƛ   : ∀ {σ τ} (t : Γ ▻ σ ⊢ τ) → Γ ⊢ ⟨π⟩ σ τ
    _·_ : ∀ {σ τ} (t₁ : Γ ⊢ ⟨π̂⟩ σ τ) (t₂ : Γ ⊢ σ) → Γ ⊢ (, τ ˢ ⟦ t₂ ⟧)

  -- Semantics of terms.

  ⟦_⟧ : ∀ {Γ σ} → Γ ⊢ σ → Value Γ σ
  ⟦ var x   ⟧ γ = lookup x γ
  ⟦ ƛ t     ⟧ γ = λ v → ⟦ t ⟧ (γ , v)
  ⟦ t₁ · t₂ ⟧ γ = (⟦ t₁ ⟧ γ) (⟦ t₂ ⟧ γ)

------------------------------------------------------------------------
-- We can define looping terms (assuming extensionality)

module Looping (ext : P.Extensionality Level.zero Level.zero) where

  -- The casts are examples of the use of equality reflection: the
  -- casts are meta-language constructions, not object-language
  -- constructions.

  cast₁ : ∀ {Γ} →
          Γ ▻ ⟨empty⟩ ⊢ ⟨π⟩ ⟨empty⟩ ⟨empty⟩ → Γ ▻ ⟨empty⟩ ⊢ ⟨empty⟩
  cast₁ t = P.subst (_⊢_ _) (P.cong (_,_ tt) (ext (⊥-elim ∘ proj₂))) t

  cast₂ : ∀ {Γ} →
          Γ ▻ ⟨empty⟩ ⊢ ⟨empty⟩ → Γ ▻ ⟨empty⟩ ⊢ ⟨π⟩ ⟨empty⟩ ⟨empty⟩
  cast₂ t = P.subst (_⊢_ _) (P.cong (_,_ tt) (ext (⊥-elim ∘ proj₂))) t

  ω : ε ▻ ⟨empty⟩ ⊢ ⟨empty⟩
  ω = cast₁ (ƛ (cast₂ (var zero) · var zero))

  -- A simple example of a term which does not have a normal form.

  Ω : ε ▻ ⟨empty⟩ ⊢ ⟨empty⟩
  Ω = cast₂ ω · ω

  const-Ω : ε ⊢ ⟨π⟩ ⟨empty⟩ ⟨empty⟩
  const-Ω = ƛ Ω

-- Some observations:
--
-- * The language with spines (in README.DependentlyTyped.Term) does
--   not support terms like the ones above; in the casts one would
--   have to prove that distinct spines are equal.
--
-- * The spines ensure that the normaliser in
--   README.DependentlyTyped.NBE terminates. The existence of terms
--   like Ω implies that it is impossible to implement a normaliser
--   for the spine-less language defined in this module.
