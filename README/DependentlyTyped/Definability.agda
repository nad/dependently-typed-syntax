------------------------------------------------------------------------
-- A definability result: A "closed value" is the semantics of a
-- closed term if and only if it satisfies all "Kripke predicates"
------------------------------------------------------------------------

-- This module is based on parts of Frederik Ramcke's (at the time of
-- writing forthcoming) MSc thesis, "On Definability and Normalization
-- by Evaluation in the Logical Framework". I have not followed
-- Ramcke's development to the letter, but I have taken inspiration
-- from it. Ramcke seems to in turn have taken inspiration from Jung
-- and Tiuryn's "A New Characterization of Lambda Definability".

import Axiom.Extensionality.Propositional as E
open import Level using (Level)
open import Universe

-- The code makes use of the assumption that propositional equality is
-- extensional for functions.

module README.DependentlyTyped.Definability
  (Uni₀ : Universe Level.zero Level.zero)
  (ext : E.Extensionality Level.zero Level.zero)
  where

open import Data.Product as Prod renaming (curry to c)
open import Function.Base hiding (_∋_) renaming (const to k)
open import Function.Equality using (_⟨$⟩_)
open import Function.Equivalence
  using (_⇔_; module Equivalence; equivalence)
open import README.DependentlyTyped.NBE Uni₀ ext
open import README.DependentlyTyped.NormalForm Uni₀
open import README.DependentlyTyped.Term Uni₀
open import Relation.Binary.PropositionalEquality as P using (_≡_)

-- Predicates.

Predicate : Set₁
Predicate = ∀ {Γ σ} → Value Γ σ → Set

private
  variable
    Γ Δ : Ctxt
    Γ₊  : Ctxt₊ Γ
    σ τ : Type Γ
    P   : Predicate

-- Kripke predicates.

record Kripke (P : Predicate) : Set where
  field
    -- Single-step weakening.

    weaken₁ :
      {v : Value Γ σ} →
      P v → P (v /̂Val ŵk[ τ ])

    -- For π-types Kripke predicates have to be defined in a certain
    -- way (up to logical equivalence).

    definition-for-π :
      ∀ {σ τ} {f : Value Γ (Type-π σ τ)} →
      P f
        ⇔
      (∀ (Γ₊ : Ctxt₊ Γ) {v : Value (Γ ++₊ Γ₊) (σ /̂ ŵk₊ Γ₊)} →
         P v → P ((f /̂Val ŵk₊ Γ₊) ˢ v))

  -- Weakening.

  weaken :
    {v : Value Γ σ} (Γ₊ : Ctxt₊ Γ) →
    P v → P (v /̂Val ŵk₊ Γ₊)
  weaken ε        = id
  weaken (σ ◅ Γ₊) = weaken Γ₊ ∘ weaken₁

  -- A "fundamental theorem" for Kripke predicates.

  fundamental :
    {ρ̂ : Γ ⇨̂ Δ} →
    (∀ {σ} (x : Γ ∋ σ) → P (x /̂∋ ρ̂)) →
    (t : Γ ⊢ σ) →
    P (⟦ t ⟧ /̂Val ρ̂)
  fundamental hyp (var x)   = hyp x
  fundamental hyp (t₁ · t₂) =
    (Equivalence.to definition-for-π ⟨$⟩ fundamental hyp t₁)
      ε (fundamental hyp t₂)
  fundamental hyp (ƛ t) =
    Equivalence.from definition-for-π ⟨$⟩ λ Δ₊ p →
      fundamental
        (λ { zero    → p
           ; (suc x) → weaken Δ₊ (hyp x)
           })
        t

  -- A special case for closed terms.

  fundamental-closed : {σ : Type ε} → (t : ε ⊢ σ) → P ⟦ t ⟧
  fundamental-closed = fundamental (λ ())

open Kripke

-- A predicate based on V̌alue.

∃-V̌alue : Predicate
∃-V̌alue {Γ = Γ} {σ = σ} v =
  ∃ λ (v̌ : V̌alue Γ σ) → v ≅-Value ⟦̌ v̌ ⟧

-- ∃-V̌alue is a Kripke predicate.

∃-V̌alue-Kripke : Kripke ∃-V̌alue
weaken₁ ∃-V̌alue-Kripke =
  Prod.map ([_⟶_].function w̌eaken _)
           (λ { P.refl → [_⟶_].corresponds w̌eaken _ _ })
definition-for-π ∃-V̌alue-Kripke {Γ = Γ} {σ = σ} {τ = τ} {f = f} =
  equivalence
    (λ { (f , P.refl) Γ₊ (v , P.refl) →
         proj₁ f Γ₊ v , proj₂ f Γ₊ v
       })
    (λ hyp →
       let
         g : V̌alue-π Γ _ _ (IType-π σ τ)
         g = λ Γ₊ v → proj₁ (hyp Γ₊ (v , P.refl))

         lemma : f ≅-Value ⟦̌ _ ∣ g ⟧-π
         lemma =
           [ f ]                                                    ≡⟨⟩
           [ c ((f /̂Val ŵk₊ (_ ◅ ε)) ˢ ⟦ var zero ⟧n) ]             ≡⟨ curry-cong (ˢ-cong (P.refl {x = [ f /̂Val _ ]})
                                                                                          (P.sym $ ňeutral-to-normal-identity _ _)) ⟩
           [ c ((f /̂Val ŵk₊ (_ ◅ ε)) ˢ
                ⟦ ňeutral-to-normal _ (var zero) ⟧n) ]              ≡⟨⟩
           [ c ((f /̂Val ŵk₊ (_ ◅ ε)) ˢ ⟦̌ řeflect _ (var zero) ⟧) ]  ≡⟨ curry-cong (proj₂ (hyp _ _)) ⟩
           [ c ⟦̌ g (_ ◅ ε) (řeflect _ (var zero)) ⟧ ]               ≡⟨ P.sym (unfold-⟦̌∣⟧-π _ g) ⟩
           [ ⟦̌ _ ∣ g ⟧-π ]                                          ∎
       in
         ( g
         , (λ Γ₊ v → [ (⟦̌ _ ∣ g ⟧-π /̂Val ŵk₊ Γ₊) ˢ ⟦̌ v ⟧ ]  ≡⟨ ˢ-cong (/̂Val-cong (P.sym lemma) P.refl) P.refl ⟩
                     [ (f /̂Val ŵk₊ Γ₊) ˢ ⟦̌ v ⟧ ]            ≡⟨ proj₂ (hyp _ _) ⟩
                     [ ⟦̌ g Γ₊ v ⟧ ]                         ∎)
         )
       , lemma
    )
  where
  open P.≡-Reasoning

-- The definability result.

definability :
  {σ : Type ε} {v : Value ε σ} →
  (∃ λ (t : ε ⊢ σ) → v ≡ ⟦ t ⟧)
    ⇔
  ({P : Predicate} → Kripke P → P v)
definability = equivalence
  (λ { (t , P.refl) kripke → fundamental-closed kripke t })
  (λ hyp → Prod.map ([_⟶_].function V̌al-subst.trans _)
                    ≅-Value-⇒-≡
                    (hyp ∃-V̌alue-Kripke))
