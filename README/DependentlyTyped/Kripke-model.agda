------------------------------------------------------------------------
-- A Kripke model
------------------------------------------------------------------------

import Level
open import Universe

module README.DependentlyTyped.Kripke-model
  {Uni₀ : Universe Level.zero Level.zero}
  where

open import deBruijn.Substitution.Data
open import README.DependentlyTyped.NormalForm
open import README.DependentlyTyped.Substitution
import README.DependentlyTyped.Term as Term; open Term Uni₀
open import Relation.Binary.PropositionalEquality as P using (_≡_)

open P.≡-Reasoning

-- The family of types which forms a Kripke model.

import README.DependentlyTyped.Kripke-model.Definition as Definition
open Definition {Uni₀} public

-- -- Equality.

-- record [V̌alue] : Set where
--   constructor [_]
--   field
--     {Γ}  : Ctxt
--     {σ}  : Type Γ
--     {σ′} : Γ ⊢ σ type
--     v    : V̌alue Γ σ′

-- infix 4 _≅-V̌alue_

-- _≅-V̌alue_ : ∀ {Γ₁ σ₁} {σ′₁ : Γ₁ ⊢ σ₁ type} (v₁ : V̌alue Γ₁ σ′₁)
--               {Γ₂ σ₂} {σ′₂ : Γ₂ ⊢ σ₂ type} (v₂ : V̌alue Γ₂ σ′₂) → Set
-- v₁ ≅-V̌alue v₂ = [V̌alue].[_] v₁ ≡ [ v₂ ]

-- ≅-V̌alue-⇒-≡ : ∀ {Γ σ} {σ′ : Γ ⊢ σ type} {v₁ v₂ : V̌alue Γ σ′} →
--               v₁ ≅-V̌alue v₂ → v₁ ≡ v₂
-- ≅-V̌alue-⇒-≡ P.refl = P.refl

-- Application.

infixl 9 _·̌_

_·̌_ : ∀ {Γ σ τ} {σ′ : Γ ⊢ σ type} {τ′ : Γ ▻ σ ⊢ τ type} →
      V̌alue Γ (π σ′ τ′) → (v : V̌alue Γ σ′) →
      V̌alue Γ (τ′ /⊢t sub ⌊ řeify σ′ v ⌋)
_·̌_ {σ′ = σ′} {τ′} f v =
  P.subst (V̌alue _) ({!≅-type-⇒-≡ lemma₂!}) (f ε v′)
  where
  abstract
    lemma₁ : σ′ ≅-type σ′ /⊢t id
    lemma₁ = {!!}

  v′ = P.subst (V̌alue _) (≅-type-⇒-≡ lemma₁) v
  ρ′ = sub ⌊ řeify (σ′ /⊢t id) v′ ⌋

  abstract
    lemma₂ : τ′ /⊢t id ↑ ∘ ρ′ ≅-type τ′ /⊢t sub ⌊ řeify σ′ v ⌋
    lemma₂ = /⊢t-cong (P.refl {x = [ τ′ ]}) (begin
      [ id ↑ ∘ ρ′          ]  ≡⟨ P.refl ⟩
      [ id ∘ ρ′            ]  ≡⟨ id-∘ ρ′ ⟩
      [ ρ′                 ]  ≡⟨ {!!} ⟩
      [ sub ⌊ řeify σ′ v ⌋ ]  ∎)

-- Weakening.

w̌k⁺ : ∀ {Γ σ} (σ′ : Γ ⊢ σ type) Γ⁺ →
      V̌alue Γ σ′ → V̌alue (Γ ++ Γ⁺) (σ′ /⊢t wk⁺ Γ⁺)
w̌k⁺ ⋆         Γ⁺ t = t /⊢n Renaming.wk⁺ Γ⁺
w̌k⁺ (el t′)   Γ⁺ t = {!t /⊢n Renaming.wk⁺ Γ⁺!}
w̌k⁺ (π σ′ τ′) Γ⁺ f = λ Γ⁺⁺ v →
  {!f (Γ⁺ ++⁺ Γ⁺⁺) v!}

-- abstract

--   -- Properties required of a Kripke model (taken from Mitchell and
--   -- Moggi's "Kripke-style models for typed lambda calculus" and
--   -- adapted to the present setting).

--   -- No weakening amounts to nothing.

--   w̌k⁺-ε : ∀ {Γ σ} (σ′ : Γ ⊢ σ type) (v : V̌alue Γ σ′) →
--           w̌k⁺ σ′ ε v ≅-V̌alue v
--   w̌k⁺-ε σ′ v = ?

--   -- Repeated weakening can be consolidated into one.
--   --
--   -- TODO: State in a pointfree way?

--   w̌k⁺-w̌k⁺ : ∀ {Γ σ} (σ′ : Γ ⊢ σ type) (v : V̌alue Γ σ′) Γ⁺ Γ⁺⁺ →
--             w̌k⁺ (σ′ /⊢t wk⁺ Γ⁺) Γ⁺⁺ (w̌k⁺ σ′ Γ⁺ v) ≅-V̌alue
--             w̌k⁺ σ′ (Γ⁺ ++⁺ Γ⁺⁺) v
--   w̌k⁺-w̌k⁺ σ′ v Γ⁺ Γ⁺⁺ = ?

--   -- Naturality.

--   w̌k⁺-·̌ : ∀ {Γ σ τ} {σ′ : Γ ⊢ σ type} {τ′ : Γ ▻ σ ⊢ τ type} →
--           (f : V̌alue Γ (π σ′ τ′)) (v : V̌alue Γ σ′) Γ⁺ →
--           w̌k⁺ (τ′ /⊢t sub ⌊ řeify σ′ v ⌋) Γ⁺ (f ·̌ v) ≅-V̌alue
--           w̌k⁺ (π σ′ τ′) Γ⁺ f ·̌ w̌k⁺ σ′ Γ⁺ v
--   w̌k⁺-·̌ f v Γ⁺ = ?

--   -- Extensionality.

--   -- Enough elements.
