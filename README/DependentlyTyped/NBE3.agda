------------------------------------------------------------------------
-- Normalisation by evaluation
------------------------------------------------------------------------

open import Level using (zero)
open import Universe

module README.DependentlyTyped.NBE3 (Uni₀ : Universe zero zero) where

import README.DependentlyTyped.Term as Term
import README.DependentlyTyped.Substitution as Substitution
import README.DependentlyTyped.NormalForm as NormalForm
import README.DependentlyTyped.Spine as Spine
open Term Uni₀
open Substitution Uni₀
open NormalForm Uni₀
open Spine Uni₀

open import Data.Product renaming (curry to c; uncurry to uc)
import deBruijn.Substitution; open deBruijn.Substitution Uni
open import Function hiding (id) renaming (_∘_ to _⊚_; const to k)
open import Relation.Binary.HeterogeneousEquality as H using (_≅_)
open import Relation.Binary.PropositionalEquality as P using (_≡_)

open Tm-subst

mutual

  -- Kripke-style values.

  Kripke-val : ∀ Γ {σ} (σ′ : Γ ⊢ σ type) sp → spine σ′ ≡ sp → Set
  Kripke-val Γ ⋆         _           _  = Γ ⊢ k ⋆ [ ne ]
  Kripke-val Γ (el t)    _           _  = Γ ⊢ k U.el ˢ ⟦ t ⟧ [ ne ]
  Kripke-val Γ (π σ′ τ′) (π sp₁ sp₂) eq =
    (Γ⁺ : Ctxt⁺ Γ)
    (v : Kripke-val (Γ ++ Γ⁺) (σ′ /⊢t wk⋆ Γ⁺) sp₁
                    (P.trans (spine-preserved σ′ (wk⋆ Γ⁺))
                             (fst-cong eq))) →
    let ρ = wk⋆ Γ⁺ ↑ ∘ sub {!⌊ reify (σ′ /⊢t wk⋆ Γ⁺) v ⌋!} in  -- Γ ++ Γ⁺ ⊢ σ / wk⋆ Γ⁺
    Kripke-val (Γ ++ Γ⁺) (τ′ /⊢t ρ) sp₂
      (P.trans (spine-preserved τ′ ρ) (snd-cong eq))
  Kripke-val Γ (π σ′ τ′) ⋆  ()
  Kripke-val Γ (π σ′ τ′) el ()

--   -- Reification.

--   reify : ∀ {Γ σ} (σ′ : Γ ⊢ σ type) → Kripke-val Γ σ′ → Γ ⊢ σ [ no ]
--   reify = reify′
--     where
--     postulate
--       reify′ : ∀ {Γ σ} (σ′ : Γ ⊢ σ type) →
--                Kripke-val Γ σ′ → Γ ⊢ σ [ no ]
--   -- reify     ⋆                         t = ne ⋆       t
--   -- reify     (el t′)                   t = ne (el t′) t
--   -- reify {Γ} (π {σ = σ} {τ = τ} σ′ τ′) f = {!!}
--     -- ƛ t′
--     -- where
--     -- v : Kripke-val (Γ ▻ σ) (σ′ /⊢t wk)
--     -- v = reflect (σ′ /⊢t wk)
--     --             (P.subst (λ ρ → Γ ▻ σ ⊢ σ /̂ ρ [ ne ])
--     --                      (wk-lemma σ)
--     --                      (var zero))

--     -- ρ : Γ ▻ σ ⇨ Γ ▻ σ
--     -- ρ = wk ↑ ∘ sub ⌊ reify (σ′ /⊢t wk) v ⌋

--     -- abstract

--     --   lemma : ρ ≡ id
--     --   lemma = ?

--     -- v′ : Kripke-val (Γ ▻ σ) (τ′ /⊢t ρ)
--     -- v′ = f (ε ▻ σ) v

--     -- t : Γ ▻ σ ⊢ τ / ρ [ no ]
--     -- t = reify (τ′ /⊢t ρ) v′

--     -- t′ : Γ ▻ σ ⊢ τ [ no ]
--     -- t′ = P.subst (λ τ → Γ ▻ σ ⊢ τ [ no ])
--     --              (begin τ / ρ   ≡⟨ P.cong (_/_ τ) $ lemma ⟩
--     --                     τ / id  ≡⟨ P.cong (_/̂_ τ) $ P.sym $ id-lemma (Γ ▻ σ) ⟩
--     --                     τ       ∎)
--     --              t
--     --   where open P.≡-Reasoning

--   -- Reflection.

--   reflect : ∀ {Γ σ} (σ′ : Γ ⊢ σ type) → Γ ⊢ σ [ ne ] → Kripke-val Γ σ′
--   reflect = reflect′
--     where postulate reflect′ : _
--   -- reflect     ⋆                         t = t
--   -- reflect     (el t′)                   t = t
--   -- reflect {Γ} (π {σ = σ} {τ = τ} σ′ τ′) t = λ Γ⁺ v →
--   --   reflect (τ′ /⊢t wk⋆ Γ⁺ ↑ ∘ sub ⌊ reify (σ′ /⊢t wk⋆ Γ⁺) v ⌋)
--   --           (P.subst (λ ρ → Γ ++ Γ⁺ ⊢ τ /̂ ρ [ ne ])
--   --                    (lemma₂ Γ⁺ ⌊ reify (σ′ /⊢t wk⋆ Γ⁺) v ⌋)
--   --                    (P.subst (λ ρ → Γ ++ Γ⁺ ⊢ k U.π ˢ σ ˢ c τ /̂ ρ [ ne ])
--   --                             (lemma₁ Γ⁺)
--   --                             (t /⊢n Var-subst.wk⋆ Γ⁺) ·
--   --                             reify (σ′ /⊢t wk⋆ Γ⁺) v))
--   --   where
--   --   open P.≡-Reasoning

--   --   abstract
--   --     lemma₁ = λ (Γ⁺ : Ctxt⁺ Γ) → begin
--   --       Var-subst.⟦_⟧⇨ (Var-subst.wk⋆ Γ⁺)  ≡⟨ P.sym $ Var-subst.wk⋆-lemma Γ⁺ ⟩
--   --       ŵk⋆ Γ⁺                             ≡⟨ wk⋆-lemma Γ⁺ ⟩
--   --       ⟦ wk⋆ Γ⁺ ⟧⇨                        ∎

--   --     lemma₂ = λ (Γ⁺ : Ctxt⁺ Γ) (t : Γ ++ Γ⁺ ⊢ σ /̂ ⟦ wk⋆ Γ⁺ ⟧⇨) → begin
--   --       _↑̂ {σ = σ} ⟦ wk⋆ Γ⁺ ⟧⇨ ⊚ ŝub ⟦ t ⟧     ≡⟨ H.≅-to-≡ $
--   --                                                 ∘-cong (P.refl {x = Γ ▻ σ})
--   --                                                        (P.refl {x = Γ ++ Γ⁺ ▻ σ /̂ ⟦ wk⋆ Γ⁺ ⟧⇨})
--   --                                                        P.refl
--   --                                                        (H.≡-to-≅ $ _↑-lemma {σ = σ} (wk⋆ Γ⁺))
--   --                                                        (H.≡-to-≅ $ sub-lemma t) ⟩
--   --       ⟦ _↑ {σ = σ} (wk⋆ Γ⁺) ⟧⇨ ⊚ ⟦ sub t ⟧⇨  ≡⟨ wk⋆ Γ⁺ ↑ ∘-lemma sub t ⟩
--   --       ⟦ _↑ {σ = σ} (wk⋆ Γ⁺) ∘ sub t ⟧⇨       ∎

-- value : ∀ {Γ σ} (σ′ : Γ ⊢ σ type) → Kripke-val Γ σ′ → Value Γ σ
-- value ⋆         t = ⟦ ⌊ t ⌋ ⟧
-- value (el t′)   t = ⟦ ⌊ t ⌋ ⟧
-- value (π σ′ τ′) f = λ γ v → value τ′ {!f ε {!!}!} (γ , v)

-- Kripke : Term-like zero
-- Kripke = record
--   { _⊢_ = λ Γ σ → ∃ λ (σ′ : Γ ⊢ σ type) → Kripke-val Γ σ′
--   ; ⟦_⟧ = uc value
--   }

-- eval : ∀ {Γ σ} (σ′ : Γ ⊢ σ type) → Γ ⊢ σ → Env Γ → Kripke-val Γ σ′
-- eval σ′ (var x)   γ = {!!}
-- eval σ′ (ƛ σ″ t)  γ = {!!}
-- eval σ′ (t₁ · t₂) γ = {!!}
