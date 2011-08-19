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

  V̌alue′ : ∀ Γ sp (σ : IType Γ sp) → Set
  V̌alue′ Γ ⋆           σ = Γ ⊢ ⋆  , σ ⟨ ne ⟩
  V̌alue′ Γ el          σ = Γ ⊢ el , σ ⟨ne⟩
  V̌alue′ Γ (π sp₁ sp₂) σ =
    Σ (V̌alue-π Γ sp₁ sp₂ σ) (Well-behaved sp₁ sp₂ σ)

  V̌alue : (Γ : Ctxt) (σ : Type Γ) → Set
  V̌alue Γ (sp , σ) = V̌alue′ Γ sp σ

  V̌alue-π : ∀ Γ sp₁ sp₂ → IType Γ (π sp₁ sp₂) → Set
  V̌alue-π Γ sp₁ sp₂ σ =
    (Γ⁺ : Ctxt⁺ Γ)
    (v : V̌alue′ (Γ ++ Γ⁺) sp₁ (ifst σ /̂I ŵk⁺ Γ⁺)) →
    V̌alue′ (Γ ++ Γ⁺) sp₂ (isnd σ /̂I ŵk⁺ Γ⁺ ↑̂ ∘̂ ŝub ⟦̌ v ⟧)

  Well-behaved :
    ∀ {Γ} sp₁ sp₂ σ → V̌alue-π Γ sp₁ sp₂ σ → Set
  Well-behaved {Γ} sp₁ sp₂ σ f =
    ∀ Γ⁺ v → (⟦ řeify-π sp₁ sp₂ σ f ⟧n /̂Val ŵk⁺ Γ⁺) ˢ ⟦̌ v ⟧ ≅-Value
             ⟦̌ f Γ⁺ v ⟧

  -- The semantics of a value.

  ⟦̌_⟧ : ∀ {Γ sp σ} → V̌alue Γ (sp , σ) → Value Γ (sp , σ)
  ⟦̌ v ⟧ = ⟦ řeify _ v ⟧n

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
  řeify ⋆           t     = ne ⋆  t
  řeify el          [ t ] = ne el t
  řeify (π sp₁ sp₂) f     = řeify-π sp₁ sp₂ _ (proj₁ f)

  řeify-π : ∀ {Γ} sp₁ sp₂ σ →
            V̌alue-π Γ sp₁ sp₂ σ → Γ ⊢ π sp₁ sp₂ , σ ⟨ no ⟩
  řeify-π {Γ} sp₁ sp₂ σ f = čast sp₁ σ $
    ƛ (řeify sp₂ (f (ε ▻ fst σ) (řeflect sp₁ (var zero))))

  čast : ∀ {Γ} sp₁ {sp₂} (σ : IType Γ (π sp₁ sp₂)) →
         let ρ̂ = ŵk ↑̂ ∘̂ ŝub ⟦ žero sp₁ (ifst σ) ⟧n in
         Γ ⊢ , k U-π ˢ ifst σ ˢ c (isnd σ /̂I ρ̂) ⟨ no ⟩ →
         Γ ⊢ , σ ⟨ no ⟩
  čast {Γ} sp₁ σ =
    P.subst (λ σ → Γ ⊢ , σ ⟨ no ⟩) (ifst-isnd-ŵk-ŝub-žero sp₁ σ)

  -- Reflection.

  řeflect : ∀ {Γ} sp {σ} → Γ ⊢ sp , σ ⟨ ne ⟩ → V̌alue Γ (sp , σ)
  řeflect     ⋆               t = t
  řeflect     el              t = [ t ]
  řeflect {Γ} (π sp₁ sp₂) {σ} t =
    (λ Γ⁺ v → řeflect sp₂ ((t /⊢n Renaming.wk⁺ Γ⁺) · řeify sp₁ v)) ,
    řeflect-π-well-behaved sp₁ sp₂ t

  abstract

    řeflect-π-well-behaved :
      ∀ {Γ} sp₁ sp₂ {σ} (t : Γ ⊢ π sp₁ sp₂ , σ ⟨ ne ⟩) Γ⁺ v →
      let t′ = ňeutral-to-normal sp₂
                 ((t /⊢n Renaming.wk) · žero sp₁ (ifst σ)) in
      (⟦ čast sp₁ σ (ƛ t′) ⟧n /̂Val ŵk⁺ Γ⁺) ˢ ⟦̌ v ⟧
        ≅-Value
      ⟦ ňeutral-to-normal sp₂ ((t /⊢n Renaming.wk⁺ Γ⁺) · řeify sp₁ v) ⟧n
    řeflect-π-well-behaved sp₁ sp₂ {σ} t Γ⁺ v =
      let t′ = ňeutral-to-normal sp₂
                 ((t /⊢n Renaming.wk) · žero sp₁ (ifst σ))
          v′ = řeify sp₁ v

          lemma′ = begin
            [ ⟦ čast sp₁ σ (ƛ t′) ⟧n /̂Val ŵk⁺ Γ⁺ ]  ≡⟨ /̂Val-cong (ňeutral-to-normal-identity-π sp₁ sp₂ t) P.refl ⟩
            [ ⟦ t ⟧n                 /̂Val ŵk⁺ Γ⁺ ]  ≡⟨ t /⊢n-lemma Renaming.wk⁺ Γ⁺ ⟩
            [ ⟦ t /⊢n Renaming.wk⁺ Γ⁺ ⟧n         ]  ∎

      in begin
      [ (⟦ čast sp₁ σ (ƛ t′) ⟧n /̂Val ŵk⁺ Γ⁺) ˢ ⟦ v′ ⟧n            ]  ≡⟨ ˢ-cong lemma′ P.refl ⟩
      [ ⟦ t /⊢n Renaming.wk⁺ Γ⁺ ⟧n           ˢ ⟦ v′ ⟧n            ]  ≡⟨ P.refl ⟩
      [ ⟦ (t /⊢n Renaming.wk⁺ Γ⁺) · v′ ⟧n                         ]  ≡⟨ P.sym $ ňeutral-to-normal-identity sp₂ _ ⟩
      [ ⟦ ňeutral-to-normal sp₂ ((t /⊢n Renaming.wk⁺ Γ⁺) · v′) ⟧n ]  ∎

    -- A given context morphism is equal to the identity.

    ŵk-ŝub-žero :
      ∀ {Γ} sp₁ {sp₂} (σ : IType Γ (π sp₁ sp₂)) →
      ŵk ↑̂ fst σ ∘̂ ŝub ⟦ žero sp₁ (ifst σ) ⟧n ≅-⇨̂ îd[ Γ ▻ fst σ ]
    ŵk-ŝub-žero sp₁ σ = begin
      [ ŵk ↑̂ ∘̂ ŝub ⟦ žero sp₁ (ifst σ) ⟧n ]  ≡⟨ ∘̂-cong (P.refl {x = [ ŵk ↑̂ ]})
                                                       (ŝub-cong (ňeutral-to-normal-identity sp₁ (var zero))) ⟩
      [ ŵk ↑̂ ∘̂ ŝub ⟦ var zero          ⟧n ]  ≡⟨ P.refl ⟩
      [ îd                                ]  ∎

    -- A corollary of the lemma above.

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
    ňeutral-to-normal-identity ⋆           t = P.refl
    ňeutral-to-normal-identity el          t = P.refl
    ňeutral-to-normal-identity (π sp₁ sp₂) t =
      ňeutral-to-normal-identity-π sp₁ sp₂ t

    ňeutral-to-normal-identity-π :
      ∀ {Γ} sp₁ sp₂ {σ} (t : Γ ⊢ π sp₁ sp₂ , σ ⟨ ne ⟩) →
      let t′ = ňeutral-to-normal sp₂
                 ((t /⊢n Renaming.wk) · žero sp₁ (ifst σ)) in
      ⟦ čast sp₁ σ (ƛ t′) ⟧n ≅-Value ⟦ t ⟧n
    ňeutral-to-normal-identity-π sp₁ sp₂ {σ} t =
      let t′ = (t /⊢n Renaming.wk) · žero sp₁ (ifst σ)

          lemma = begin
            [ ⟦ ňeutral-to-normal sp₂ t′ ⟧n                   ]  ≡⟨ ňeutral-to-normal-identity sp₂ t′ ⟩
            [ ⟦ t′ ⟧n                                         ]  ≡⟨ P.refl ⟩
            [ ⟦ t /⊢n Renaming.wk ⟧n ˢ ⟦ žero sp₁ (ifst σ) ⟧n ]  ≡⟨ ˢ-cong (P.sym $ t /⊢n-lemma Renaming.wk)
                                                                           (ňeutral-to-normal-identity sp₁ (var zero)) ⟩
            [ (⟦ t ⟧n /̂Val ŵk)       ˢ lookup zero            ]  ≡⟨ P.refl ⟩
            [ uc ⟦ t ⟧n                                       ]  ∎

      in begin
      [ ⟦ čast sp₁ σ (ƛ (ňeutral-to-normal sp₂ t′)) ⟧n ]  ≡⟨ ⟦⟧n-cong $ drop-subst-⊢n (λ σ → , σ) (ifst-isnd-ŵk-ŝub-žero sp₁ σ) ⟩
      [ c ⟦ ňeutral-to-normal sp₂ t′ ⟧n                ]  ≡⟨ curry-cong lemma ⟩
      [ c {C = k El ˢ isnd σ} (uc ⟦ t ⟧n)              ]  ≡⟨ P.refl ⟩
      [ ⟦ t ⟧n                                         ]  ∎

-- An immediate consequence of the somewhat roundabout definition
-- above.

w̌ell-behaved :
  ∀ {Γ sp₁ sp₂ σ} (f : V̌alue Γ (π sp₁ sp₂ , σ)) →
  ∀ Γ⁺ v → (⟦̌_⟧ {σ = σ} f /̂Val ŵk⁺ Γ⁺) ˢ ⟦̌ v ⟧ ≅-Value ⟦̌ proj₁ f Γ⁺ v ⟧
w̌ell-behaved = proj₂
