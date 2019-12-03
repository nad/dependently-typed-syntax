------------------------------------------------------------------------
-- There is a term without a corresponding syntactic type (given some
-- assumptions)
------------------------------------------------------------------------

import Level
open import Universe

module README.DependentlyTyped.Term-without-type
  (Uni₀ : Universe Level.zero Level.zero)
  where

import Axiom.Extensionality.Propositional as E
open import Data.Product
open import Function renaming (const to k)
import README.DependentlyTyped.NBE as NBE; open NBE Uni₀
import README.DependentlyTyped.NormalForm as NF; open NF Uni₀
import README.DependentlyTyped.Term as Term; open Term Uni₀
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_)
open import Relation.Nullary using (¬_)

abstract

  -- There are no closed neutral terms.

  no-closed-neutral : ∀ {σ} → ¬ (ε ⊢ σ ⟨ ne ⟩)
  no-closed-neutral (var ())
  no-closed-neutral (t₁ · t₂) = no-closed-neutral t₁

  -- There are no closed normal forms of "atomic" type.

  no-closed-atomic-normal :
    ∀ {σ} → ε ⊢ σ atomic-type → ¬ (ε ⊢ σ ⟨ no ⟩)
  no-closed-atomic-normal ⋆  (ne ⋆  t) = no-closed-neutral t
  no-closed-atomic-normal el (ne el t) = no-closed-neutral t

  -- There are no closed terms of "atomic" type (assuming
  -- extensionality).

  no-closed-atomic :
    E.Extensionality Level.zero Level.zero →
    ∀ {σ} → ε ⊢ σ atomic-type → ¬ (ε ⊢ σ)
  no-closed-atomic ext atomic t =
    no-closed-atomic-normal atomic (normalise ext t)

  -- There are terms without syntactic types, assuming that U₀ is
  -- inhabited (and also extensionality).
  --
  -- One could avoid this situation by annotating lambdas with the
  -- (syntactic) type of their domain. I tried this, and found it to
  -- be awkward. One case of the function
  -- README.DependentlyTyped.NBE.Value.řeify returns a lambda, and I
  -- didn't find a way to synthesise the annotation without supplying
  -- syntactic types to V̌alue, řeify, řeflect, etc.

  term-without-type :
    E.Extensionality Level.zero Level.zero → U₀ →
    ∃₂ λ Γ σ → ∃ λ (t : Γ ⊢ σ) → ¬ (Γ ⊢ σ type)
  term-without-type ext u = (ε , (-, σ) , ƛ (var zero) , proof)
    where
    σ : IType ε (π el el)
    σ = k (U-π (U-el u) (k (U-el u)))

    proof : ∀ {σ} → ¬ (ε ⊢ π el el , σ type)
    proof (π (el t) (el t′)) = no-closed-atomic ext ⋆ t
