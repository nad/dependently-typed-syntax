------------------------------------------------------------------------
-- A type-checker
------------------------------------------------------------------------

import Level
open import Relation.Binary.PropositionalEquality as P using (_≡_)
open import Universe

-- The code makes use of the assumption that propositional equality of
-- functions is extensional.

module README.DependentlyTyped.Type-checker
  (Uni₀ : Universe Level.zero Level.zero)
  (ext : P.Extensionality Level.zero Level.zero)
  where

open import Category.Monad
open import Data.Maybe as Maybe
open import Data.Nat using (ℕ; zero; suc; pred)
open import Data.Product as Prod
open import Function as F hiding (_∋_) renaming (_∘_ to _⊚_)
import README.DependentlyTyped.Equality-checker as EC; open EC Uni₀ ext
import README.DependentlyTyped.NBE as NBE; open NBE Uni₀ ext
import README.DependentlyTyped.NormalForm as NF
open NF Uni₀ hiding (⌊_⌋)
import README.DependentlyTyped.Raw-term as RT; open RT Uni₀
import README.DependentlyTyped.Term as Term; open Term Uni₀
import README.DependentlyTyped.Term.Substitution as S; open S Uni₀
open import Relation.Nullary
import Relation.Nullary.Decidable as Dec
open import Relation.Nullary.Product

open P.≡-Reasoning
open RawMonadZero (Maybe.monadZero {f = Level.zero})

-- Computes a syntactic type for a variable from a matching syntactic
-- context.

type-of-var : ∀ {Γ σ} → Γ ∋ σ → Γ ctxt → Γ ⊢ σ type
type-of-var zero    (Γ′ ▻ σ′) = σ′               /⊢t wk
type-of-var (suc x) (Γ′ ▻ σ′) = type-of-var x Γ′ /⊢t wk

-- Infers the type of a variable, if possible.

infer-var : (Γ : Ctxt) (x : ℕ) →
            Dec (∃₂ λ σ (x′ : Γ ∋ σ) → position x′ ≡ x)
infer-var ε x = no helper
  where
  helper : ¬ ∃₂ λ σ (x′ : ε ∋ σ) → position x′ ≡ x
  helper (_ , () , _)
infer-var (Γ ▻ σ) zero    = yes (σ /̂ ŵk , zero , P.refl)
infer-var (Γ ▻ σ) (suc x) =
  Dec.map′ (Prod.map (λ σ → σ /̂ ŵk) (Prod.map suc (P.cong suc)))
           helper
           (infer-var Γ x)
  where
  helper : (∃₂ λ τ (x′ : Γ ▻ σ ∋ τ) → position x′ ≡ suc x) →
           (∃₂ λ τ (x′ : Γ     ∋ τ) → position x′ ≡ x)
  helper (._ , zero   , ())
  helper (._ , suc x′ , eq) = (_ , x′ , P.cong pred eq)

-- Infers the /syntactic/ type of a variable, if possible.

infer-var-syntactic :
  ∀ {Γ} → Γ ctxt → (x : ℕ) →
  Dec (∃ λ σ → Γ ⊢ σ type × ∃ λ (x′ : Γ ∋ σ) → position x′ ≡ x)
infer-var-syntactic {Γ} Γ′ x = Dec.map′
  (Prod.map F.id (λ p → type-of-var (proj₁ p) Γ′ , proj₁ p , proj₂ p))
  (Prod.map F.id proj₂)
  (infer-var Γ x)

mutual

  -- Tries to infer a well-typed form of a raw type.

  infer-ty :
    ∀ {Γ} → Γ ctxt → (σ : Raw-ty) →
    Maybe (∃₂ λ σ′ (σ″ : Γ ⊢ σ′ type) → ⌊ σ″ ⌋ty ≡ ⌊ σ ⌋raw-ty)
  infer-ty Γ′ ⋆      = return (_ , ⋆ , P.refl)
  infer-ty Γ′ (el t) =
    check Γ′ ⋆ t                      >>= λ { (t′ , eq) →
    return (_ , el t′ , P.cong el eq) }
  infer-ty Γ′ (π σ′₁ σ′₂) =
    infer-ty Γ′          σ′₁                     >>= λ { (_ , σ′₁′ , eq₁) →
    infer-ty (Γ′ ▻ σ′₁′) σ′₂                     >>= λ { (_ , σ′₂′ , eq₂) →
    return (_ , π σ′₁′ σ′₂′ , P.cong₂ π eq₁ eq₂) }}

  -- Tries to infer a type for a term. In the case of success a
  -- well-typed term is returned.

  infer :
    ∀ {Γ} → Γ ctxt → (t : Raw) →
    Maybe (∃ λ σ → Γ ⊢ σ type × ∃ λ (t′ : Γ ⊢ σ) → ⌊ t′ ⌋ ≡ ⌊ t ⌋raw)
  infer Γ′ (var x) with infer-var-syntactic Γ′ x
  ... | yes (_ , σ′ , x′ , eq) = return (_ , σ′ , var x′ , P.cong var eq)
  ... | no _                   = ∅
  infer Γ′ (ƛ t)     = ∅
  infer Γ′ (t₁ · t₂) =
    infer Γ′ t₁ >>=
    λ { (._ , π σ′₁ σ′₂ , t₁′ , eq₁) →
            check Γ′ σ′₁ t₂                           >>= λ { (t₂′ , eq₂) →
            return (_ , σ′₂ /⊢t sub t₂′ , t₁′ · t₂′ ,
                    P.cong₂ _·_ eq₁ eq₂) }
      ; _ → ∅
      }
  infer Γ′ (t ∶ σ) =
    infer-ty Γ′ σ             >>= λ { (_ , σ′ , eq) →
    check Γ′ σ′ t             >>= λ { (t′ , eq) →
    return (_ , σ′ , t′ , eq) }}

  -- Tries to type-check a term. In the case of success a well-typed
  -- term is returned.

  check : ∀ {Γ σ} → Γ ctxt → (σ′ : Γ ⊢ σ type) (t : Raw) →
          Maybe (∃ λ (t′ : Γ ⊢ σ) → ⌊ t′ ⌋ ≡ ⌊ t ⌋raw)
  check Γ′ (π σ′₁ σ′₂) (ƛ t) =
    check (Γ′ ▻ σ′₁) σ′₂ t      >>= λ { (t′ , eq) →
    return (ƛ t′ , P.cong ƛ eq) }
  check Γ′ σ′ t =
    infer Γ′ t                                           >>= λ { (_ , τ′ , t′ , eq₁) →
    τ′ ≟-Type σ′                                         >>= λ eq₂ →
    return (P.subst (_⊢_ _) (≅-Type-⇒-≡ eq₂) t′ , (begin
              ⌊ P.subst (_⊢_ _) (≅-Type-⇒-≡ eq₂) t′ ⌋  ≡⟨ ⌊⌋-cong $ drop-subst-⊢ F.id (≅-Type-⇒-≡ eq₂) ⟩
              ⌊ t′ ⌋                                   ≡⟨ eq₁ ⟩
              ⌊ t ⌋raw                                 ∎)) }

-- Tries to establish that the given raw term has the given raw type
-- (in the empty context).

infix 4 _∋?_

_∋?_ : (σ : Raw-ty) (t : Raw) →
       Maybe (∃₂ λ (σ′ : Type ε) (σ″ : ε ⊢ σ′ type) →
              ∃  λ (t′ : ε ⊢ σ′) →
                   ⌊ σ″ ⌋ty ≡ ⌊ σ ⌋raw-ty × ⌊ t′ ⌋ ≡ ⌊ t ⌋raw)
σ ∋? t = infer-ty ε σ                      >>= λ { (σ′ , σ″ , eq₁) →
         check ε σ″ t                      >>= λ { (t′ , eq₂) →
         return (σ′ , σ″ , t′ , eq₁ , eq₂) }}

------------------------------------------------------------------------
-- Examples

private

  σ₁ : Raw-ty
  σ₁ = π ⋆ ⋆

  σ₁′ : Type ε
  σ₁′ = proj₁ $ from-just $ infer-ty ε σ₁

  t₁ : Raw
  t₁ = ƛ (var zero)

  t₁′ : ε ⊢ σ₁′
  t₁′ = proj₁ $ proj₂ $ proj₂ $ from-just $ σ₁ ∋? t₁

  t₂ : ε ▻ (⋆ , _) ⊢ (⋆ , _)
  t₂ = proj₁ $ proj₂ $ proj₂ $ from-just $ infer (ε ▻ ⋆) (var zero)

  t₃ : Raw
  t₃ = (ƛ (var zero) ∶ π ⋆ ⋆) · var zero

  t₃′ : ε ▻ (⋆ , _) ⊢ (⋆ , _)
  t₃′ = proj₁ $ proj₂ $ proj₂ $ from-just $ infer (ε ▻ ⋆) t₃
