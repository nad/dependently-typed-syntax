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
open import README.DependentlyTyped.Substitution
import README.DependentlyTyped.Term as Term; open Term Uni₀
import Relation.Binary.PropositionalEquality as P

open P.≡-Reasoning

mutual

  -- The Kripke model.

  V̌alue : ∀ Γ {σ} → Γ ⊢ σ type → Set
  V̌alue Γ ⋆         = Γ ⊢ k ⋆ ⟨ ne ⟩
  V̌alue Γ (el t)    = Γ ⊢ k U.el ˢ ⟦ t ⟧ ⟨ ne ⟩
  V̌alue Γ (π σ′ τ′) =
    (Γ⁺ : Ctxt⁺ Γ)
    (v : V̌alue (Γ ++ Γ⁺) (σ′ /⊢t wk⁺ Γ⁺)) →
    V̌alue (Γ ++ Γ⁺)
      (τ′ /⊢t wk⁺ Γ⁺ ↑ ∘ sub ⌊ řeify (σ′ /⊢t wk⁺ Γ⁺) v ⌋)

  -- Reification.

  řeify : ∀ {Γ σ} (σ′ : Γ ⊢ σ type) → V̌alue Γ σ′ → Γ ⊢ σ ⟨ no ⟩
  řeify     ⋆                         t = ne ⋆       t
  řeify     (el t′)                   t = ne (el t′) t
  řeify {Γ} (π {σ = σ} {τ = τ} σ′ τ′) f =
    ƛ σ′ (P.subst (λ τ → Γ ▻ σ ⊢ τ ⟨ no ⟩)
                  (≅-Type-⇒-≡ $ /̂-ŵk-↑̂-∘̂-ŝub σ′ τ)
                  (řeify (τ′ /⊢t ρ) (f (ε ▻ σ) v)))
    where
    v = řeflect (σ′ /⊢t wk) (var zero)
    ρ = wk ↑ ∘ sub ⌊ řeify (σ′ /⊢t wk) v ⌋

  -- Reflection.

  řeflect : ∀ {Γ σ} (σ′ : Γ ⊢ σ type) → Γ ⊢ σ ⟨ ne ⟩ → V̌alue Γ σ′
  řeflect ⋆         t = t
  řeflect (el t′)   t = t
  řeflect (π σ′ τ′) t = λ Γ⁺ v →
    řeflect (τ′ /⊢t wk⁺ Γ⁺ ↑ ∘ sub ⌊ řeify (σ′ /⊢t wk⁺ Γ⁺) v ⌋)
            ((t /⊢n Renaming.wk⁺ Γ⁺) · řeify (σ′ /⊢t wk⁺ Γ⁺) v)

  abstract

    -- A given context morphism is equal to the identity.

    /̂-ŵk-↑̂-∘̂-ŝub :
      ∀ {Γ σ} (σ′ : Γ ⊢ σ type) (τ : Type (Γ ▻ σ)) →
      let t′ = řeify (σ′ /⊢t wk[ σ ])
                 (řeflect (σ′ /⊢t wk) (var zero)) in
      τ /̂ ŵk ↑̂ ∘̂ ŝub ⟦ t′ ⟧n ≅-Type τ
    /̂-ŵk-↑̂-∘̂-ŝub σ′ τ = /̂-cong (P.refl {x = [ τ ]}) (begin
      [ ŵk ↑̂ ∘̂ ŝub ⟦ řeify (σ′ /⊢t wk)
                       (řeflect (σ′ /⊢t wk) (var zero)) ⟧n ]  ≡⟨ ∘̂-cong (P.refl {x = [ ŵk ↑̂ ]})
                                                                        (ŝub-cong (řeify∘řeflect (σ′ /⊢t wk) (var zero))) ⟩
      [ ŵk ↑̂ ∘̂ ŝub ⟦ var zero ⟧n ]                            ≡⟨ P.refl ⟩
      [ îd ]                                                  ∎)

    -- In the semantics řeify is a left inverse of řeflect.

    řeify∘řeflect : ∀ {Γ σ} (σ′ : Γ ⊢ σ type) (t : Γ ⊢ σ ⟨ ne ⟩) →
                    ⟦ řeify σ′ (řeflect σ′ t) ⟧n ≅-Value ⟦ t ⟧n
    řeify∘řeflect     ⋆                         t = P.refl
    řeify∘řeflect     (el t′)                   t = P.refl
    řeify∘řeflect {Γ} (π {σ = σ} {τ = τ} σ′ τ′) t =
      let t′ = řeify (σ′ /⊢t wk) (řeflect (σ′ /⊢t wk) (var zero))
          ρ  = wk ↑ ∘ sub ⌊ t′ ⌋
          v  = ⟦ P.subst (λ τ → Γ ▻ σ ⊢ τ ⟨ no ⟩)
                         (≅-Type-⇒-≡ $ /̂-ŵk-↑̂-∘̂-ŝub σ′ τ)
                         (řeify (τ′ /⊢t ρ) (řeflect (τ′ /⊢t ρ)
                            ((t /⊢n Renaming.wk) · t′))) ⟧n

          lemma = begin
            [ v                                      ]  ≡⟨ ⟦⟧n-cong (drop-subst-⊢n F.id (≅-Type-⇒-≡ $ /̂-ŵk-↑̂-∘̂-ŝub σ′ τ)) ⟩
            [ ⟦ řeify (τ′ /⊢t ρ) (řeflect (τ′ /⊢t ρ)
                  ((t /⊢n Renaming.wk) · t′)) ⟧n     ]  ≡⟨ řeify∘řeflect (τ′ /⊢t ρ) ((t /⊢n Renaming.wk) · t′) ⟩
            [ ⟦ (t /⊢n Renaming.wk) · t′ ⟧n          ]  ≡⟨ P.refl ⟩
            [ ⟦ t /⊢n Renaming.wk ⟧n ˢ ⟦ t′ ⟧n       ]  ≡⟨ ˢ-cong (P.refl {x = [ τ /̂ ŵk ↑̂ ]})
                                                                  (P.sym $ t /⊢n-lemma Renaming.wk)
                                                                  (řeify∘řeflect (σ′ /⊢t wk) (var zero)) ⟩
            [ (⟦ t ⟧n /̂Val ŵk) ˢ ⟦ var zero ⟧n       ]  ≡⟨ P.refl ⟩
            [ uc ⟦ t ⟧n                              ]  ∎

      in begin
        [ ⟦ řeify (π σ′ τ′) (řeflect (π σ′ τ′) t) ⟧n ]  ≡⟨ curry-cong {v₁ = v} {v₂ = uc ⟦ t ⟧n} lemma ⟩
        [ c {C = λ γ → El (τ γ)} (uc ⟦ t ⟧n)         ]  ≡⟨ P.refl ⟩
        [ ⟦ t ⟧n                                     ]  ∎
