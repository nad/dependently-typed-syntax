------------------------------------------------------------------------
-- Definition of a family of types which forms a Kripke model
------------------------------------------------------------------------

-- This file does not contain a proof showing that this family
-- actually forms a Kripke model.

import Level
open import Universe

module README.DependentlyTyped.Kripke-model.Definition
  {Uni₀ : Universe Level.zero Level.zero}
  where

open import Data.Product renaming (curry to c; uncurry to uc)
open import deBruijn.Substitution.Data
open import Function as F using (_ˢ_; _$_) renaming (const to k)
open import README.DependentlyTyped.NormalForm
open import README.DependentlyTyped.NormalForm.Substitution
import README.DependentlyTyped.Term as Term; open Term Uni₀
open import Relation.Binary.PropositionalEquality as P using (_≡_)

open P.≡-Reasoning

-- A wrapper which is used to make V̌alue "constructor-headed", which
-- in turn makes Agda infer more types for us.

infix 4 _⊢_⟨ne⟩

record _⊢_⟨ne⟩ (Γ : Ctxt) (σ : Type Γ) : Set where
  constructor [_]
  field t : Γ ⊢ σ ⟨ ne ⟩

mutual

  -- The Kripke model.

  V̌alue : ∀ Γ (σ : Type Γ) → Set
  V̌alue Γ (⋆         , σ) = Γ ⊢ ⋆  , σ ⟨ ne ⟩
  V̌alue Γ (el        , σ) = Γ ⊢ el , σ ⟨ne⟩
  V̌alue Γ (π sp₁ sp₂ , σ) =
    (Γ⁺ : Ctxt⁺ Γ)
    (v : V̌alue (Γ ++ Γ⁺) (sp₁ , ifst σ /̂I ŵk⁺ Γ⁺)) →
    V̌alue (Γ ++ Γ⁺) (sp₂ , isnd σ /̂I ŵk⁺ Γ⁺ ↑̂ ∘̂ ŝub ⟦ řeify sp₁ v ⟧n)

  -- Neutral terms can be turned into normal terms using reflection
  -- followed by reification.

  ňeutral-to-normal :
    ∀ {Γ} sp {σ} → Γ ⊢ sp , σ ⟨ ne ⟩ → Γ ⊢ sp , σ ⟨ no ⟩
  ňeutral-to-normal sp t = řeify sp (řeflect sp t)

  -- A normal term corresponding to variable zero.

  žero : ∀ {Γ} sp σ → Γ ▻ (sp , σ) ⊢ sp , σ /̂I ŵk ⟨ no ⟩
  žero sp σ = ňeutral-to-normal sp (var zero[ , σ ])

  -- Reification.

  řeify : ∀ {Γ} sp {σ} → V̌alue Γ (sp , σ) → Γ ⊢ sp , σ ⟨ no ⟩
  řeify     ⋆               t     = ne ⋆  t
  řeify     el              [ t ] = ne el t
  řeify {Γ} (π sp₁ sp₂) {σ} f     = cast $
    ƛ (řeify sp₂ (f (ε ▻ fst σ) (řeflect sp₁ (var zero))))
    where
    cast = P.subst (λ σ → Γ ⊢ , σ ⟨ no ⟩) (ifst-isnd-ŵk-ŝub-žero sp₁ σ)

  -- Reflection.

  řeflect : ∀ {Γ} sp {σ} → Γ ⊢ sp , σ ⟨ ne ⟩ → V̌alue Γ (sp , σ)
  řeflect ⋆           t = t
  řeflect el          t = [ t ]
  řeflect (π sp₁ sp₂) t = λ Γ⁺ v →
    řeflect sp₂ ((t /⊢n Renaming.wk⁺ Γ⁺) · řeify sp₁ v)

  abstract

    -- A given context morphism is equal to the identity.

    ŵk-ŝub-žero :
      ∀ {Γ} sp₁ {sp₂} (σ : IType Γ (π sp₁ sp₂)) →
      ŵk ↑̂ fst σ ∘̂ ŝub ⟦ žero sp₁ (ifst σ) ⟧n ≅-⇨̂ îd[ Γ ▻ fst σ ]
    ŵk-ŝub-žero sp₁ σ = begin
      [ ŵk ↑̂ ∘̂ ŝub ⟦ žero sp₁ (ifst σ) ⟧n ]  ≡⟨ ∘̂-cong (P.refl {x = [ ŵk ↑̂ ]})
                                                       (ŝub-cong (ňeutral-to-normal-identity sp₁ (var zero))) ⟩
      [ ŵk ↑̂ ∘̂ ŝub ⟦ var zero          ⟧n ]  ≡⟨ P.refl ⟩
      [ îd                                ]  ∎

    -- A variant of the lemma above.

    ifst-isnd-ŵk-ŝub-žero :
      ∀ {Γ} sp₁ {sp₂} (σ : IType Γ (π sp₁ sp₂)) →
      k U-π ˢ ifst σ ˢ c (isnd σ /̂I ŵk ↑̂ ∘̂ ŝub ⟦ žero sp₁ (ifst σ) ⟧n) ≡
      σ
    ifst-isnd-ŵk-ŝub-žero sp₁ σ = begin
      k U-π ˢ ifst σ ˢ c (isnd σ /̂I ŵk ↑̂ ∘̂ ŝub ⟦ žero sp₁ (ifst σ) ⟧n)  ≡⟨ P.cong (λ ρ → k U-π ˢ ifst σ ˢ c (isnd σ /̂I ρ))
                                                                                  (≅-⇨̂-⇒-≡ $ ŵk-ŝub-žero sp₁ σ) ⟩
      k U-π ˢ ifst σ ˢ c (isnd σ)                                       ≡⟨ P.refl ⟩
      σ                                                                 ∎

    -- In the semantics řeify is a left inverse of řeflect.

    ňeutral-to-normal-identity :
      ∀ {Γ} sp {σ} (t : Γ ⊢ sp , σ ⟨ ne ⟩) →
      ⟦ ňeutral-to-normal sp t ⟧n ≅-Value ⟦ t ⟧n
    ňeutral-to-normal-identity ⋆               t = P.refl
    ňeutral-to-normal-identity el              t = P.refl
    ňeutral-to-normal-identity (π sp₁ sp₂) {σ} t =
      let v = ⟦ ňeutral-to-normal sp₂
                  ((t /⊢n Renaming.wk) · žero sp₁ (ifst σ)) ⟧n

          lemma = begin
            [ v                                               ]  ≡⟨ ňeutral-to-normal-identity sp₂
                                                                      ((t /⊢n Renaming.wk) · žero sp₁ (ifst σ)) ⟩
            [ ⟦ (t /⊢n Renaming.wk) · žero sp₁ (ifst σ) ⟧n    ]  ≡⟨ P.refl ⟩
            [ ⟦ t /⊢n Renaming.wk ⟧n ˢ ⟦ žero sp₁ (ifst σ) ⟧n ]  ≡⟨ ˢ-cong (P.refl {x = [ snd σ /̂ ŵk ↑̂ ]})
                                                                           (P.sym $ t /⊢n-lemma Renaming.wk)
                                                                           (ňeutral-to-normal-identity sp₁ (var zero)) ⟩
            [ (⟦ t ⟧n /̂Val ŵk) ˢ ⟦ var zero ⟧n                ]  ≡⟨ P.refl ⟩
            [ uc ⟦ t ⟧n                                       ]  ∎

      in begin
        [ ⟦ ňeutral-to-normal (π sp₁ sp₂) t ⟧n ]  ≡⟨ ⟦⟧n-cong $ drop-subst-⊢n (λ σ → , σ) (ifst-isnd-ŵk-ŝub-žero sp₁ σ) ⟩
        [ c v                                  ]  ≡⟨ curry-cong lemma ⟩
        [ c {C = k El ˢ isnd σ} (uc ⟦ t ⟧n)    ]  ≡⟨ P.refl ⟩
        [ ⟦ t ⟧n                               ]  ∎
