------------------------------------------------------------------------
-- Some simple substitutions
------------------------------------------------------------------------

-- Given a term type which supports weakening and transformation of
-- variables to terms one can define various substitutions.

{-# OPTIONS --universe-polymorphism #-}

open import Universe

module deBruijn.Substitution.Function.Simple
  {u e} (Uni : Universe u e)
  where

import deBruijn.Context as Context
import deBruijn.Substitution.Function.Basics as Basics
open import deBruijn.Substitution.Function.Map
import deBruijn.TermLike as TermLike
open import Function using (_$_)
open import Level using (_⊔_)
open import Relation.Binary.HeterogeneousEquality as H using (_≅_)
open import Relation.Binary.PropositionalEquality as P using (_≡_)

open Context Uni
open TermLike Uni

record Simple {t} (T : Term-like t) : Set (u ⊔ e ⊔ t) where

  open Term-like T
  open Basics    T

  field

    -- Weakens terms.
    weaken : ∀ {Γ σ} → [ T ⟶ T ] (ŵk {Γ = Γ} {σ = σ})

    -- Takes variables to terms.
    var : ∀ {Γ} → [ Var ⟶ T ] (îd {Γ = Γ})

    -- A property relating weaken and var.
    weaken-var : ∀ {Γ σ τ} (x : Γ ∋ σ) →
                 weaken {σ = τ} · (var · x) ≡ var · suc x

  -- Weakens substitutions.

  wk-subst : ∀ {Γ Δ σ} {ρ̂ : Γ ⇨̂ Δ} → Sub ρ̂ → Sub (ρ̂ ∘̂ ŵk {σ = σ})
  wk-subst ρ = map weaken ρ

  -- Lifting.

  infix 10 _↑

  _↑ : ∀ {Γ Δ σ} {ρ̂ : Γ ⇨̂ Δ} → Sub ρ̂ → Sub (_↑̂ {σ = σ} ρ̂)
  _↑ {σ = σ} {ρ̂} ρ =
    P.subst Sub
            (H.≅-to-≡ $ ▻̂-cong P.refl P.refl H.refl H.refl
                          (H.≡-to-≅ $ P.sym $ corresponds var zero))
            (wk-subst ρ ▻⇨ var · zero)

  -- Application of substitutions to context extensions.

  infixl 8 _/⁺_

  _/⁺_ : ∀ {Γ Δ} {ρ̂ : Γ ⇨̂ Δ} → Ctxt⁺ Γ → Sub ρ̂ → Ctxt⁺ Δ
  Γ⁺ /⁺ ρ = Γ⁺ /̂⁺ ⟦ ρ ⟧⇨

  -- N-ary lifting.

  infixl 10 _↑⁺_

  _↑⁺_ : ∀ {Γ Δ} {ρ̂ : Γ ⇨̂ Δ} → Sub ρ̂ → ∀ Γ⁺ → Sub (ρ̂ ↑̂⁺ Γ⁺)
  ρ ↑⁺ ε        = ρ
  ρ ↑⁺ (Γ⁺ ▻ σ) = (ρ ↑⁺ Γ⁺) ↑

  -- The identity substitution.

  id : ∀ {Γ} → Sub (îd {Γ = Γ})
  id {ε}     = ε⇨
  id {Γ ▻ σ} = id ↑

  -- N-ary weakening.

  wk⁺ : ∀ {Γ} (Γ⁺ : Ctxt⁺ Γ) → Sub (ŵk⁺ Γ⁺)
  wk⁺ ε        = id
  wk⁺ (Γ⁺ ▻ σ) = wk-subst (wk⁺ Γ⁺)

  -- Weakening.

  wk : ∀ {Γ} {σ : Type Γ} → Sub (ŵk {σ = σ})
  wk {σ = σ} = wk⁺ (ε ▻ σ)

  -- A substitution which only replaces the first variable.

  sub : ∀ {Γ σ} (t : Γ ⊢ σ) → Sub (ŝub ⟦ t ⟧)
  sub t = id ▻⇨ t

  -- Some congruence lemmas.

  weaken-cong : ∀ {Γ₁ σ₁ τ₁} {t₁ : Γ₁ ⊢ σ₁}
                  {Γ₂ σ₂ τ₂} {t₂ : Γ₂ ⊢ σ₂} →
                Γ₁ ≡ Γ₂ → σ₁ ≅ σ₂ → τ₁ ≅ τ₂ → t₁ ≅ t₂ →
                weaken {σ = τ₁} · t₁ ≅ weaken {σ = τ₂} · t₂
  weaken-cong P.refl H.refl H.refl H.refl = H.refl

  var-cong : ∀ {Γ₁ σ₁} {x₁ : Γ₁ ∋ σ₁}
               {Γ₂ σ₂} {x₂ : Γ₂ ∋ σ₂} →
               Γ₁ ≡ Γ₂ → σ₁ ≅ σ₂ → x₁ ≅ x₂ →
               var · x₁ ≅ var · x₂
  var-cong P.refl H.refl H.refl = H.refl

  wk-subst-cong : ∀ {Γ₁ Δ₁ σ₁} {ρ̂₁ : Γ₁ ⇨̂ Δ₁} {ρ₁ : Sub ρ̂₁}
                    {Γ₂ Δ₂ σ₂} {ρ̂₂ : Γ₂ ⇨̂ Δ₂} {ρ₂ : Sub ρ̂₂} →
                  Γ₁ ≡ Γ₂ → Δ₁ ≡ Δ₂ → σ₁ ≅ σ₂ → ρ̂₁ ≅ ρ̂₂ → ρ₁ ≅ ρ₂ →
                  wk-subst {σ = σ₁} ρ₁ ≅ wk-subst {σ = σ₂} ρ₂
  wk-subst-cong P.refl P.refl H.refl H.refl H.refl = H.refl

  ↑-cong : ∀ {Γ₁ Δ₁} {ρ̂₁ : Γ₁ ⇨̂ Δ₁} {ρ₁ : Sub ρ̂₁} {σ₁}
             {Γ₂ Δ₂} {ρ̂₂ : Γ₂ ⇨̂ Δ₂} {ρ₂ : Sub ρ̂₂} {σ₂} →
           Γ₁ ≡ Γ₂ → Δ₁ ≡ Δ₂ → ρ̂₁ ≅ ρ̂₂ → ρ₁ ≅ ρ₂ → σ₁ ≅ σ₂ →
           _↑ {σ = σ₁} ρ₁ ≅ _↑ {σ = σ₂} ρ₂
  ↑-cong P.refl P.refl H.refl H.refl H.refl = H.refl

  /⁺-cong : ∀ {Γ₁ Δ₁} {Γ⁺₁ : Ctxt⁺ Γ₁} {ρ̂₁ : Γ₁ ⇨̂ Δ₁} {ρ₁ : Sub ρ̂₁}
              {Γ₂ Δ₂} {Γ⁺₂ : Ctxt⁺ Γ₂} {ρ̂₂ : Γ₂ ⇨̂ Δ₂} {ρ₂ : Sub ρ̂₂} →
            Γ₁ ≡ Γ₂ → Δ₁ ≡ Δ₂ → Γ⁺₁ ≅ Γ⁺₂ → ρ̂₁ ≅ ρ̂₂ → ρ₁ ≅ ρ₂ →
            Γ⁺₁ /⁺ ρ₁ ≅ Γ⁺₂ /⁺ ρ₂
  /⁺-cong P.refl P.refl H.refl H.refl H.refl = H.refl

  ↑⁺-cong : ∀ {Γ₁ Δ₁} {ρ̂₁ : Γ₁ ⇨̂ Δ₁} {ρ₁ : Sub ρ̂₁} {Γ⁺₁ : Ctxt⁺ Γ₁}
              {Γ₂ Δ₂} {ρ̂₂ : Γ₂ ⇨̂ Δ₂} {ρ₂ : Sub ρ̂₂} {Γ⁺₂ : Ctxt⁺ Γ₂} →
            Γ₁ ≡ Γ₂ → Δ₁ ≡ Δ₂ → ρ̂₁ ≅ ρ̂₂ → ρ₁ ≅ ρ₂ → Γ⁺₁ ≅ Γ⁺₂ →
            ρ₁ ↑⁺ Γ⁺₁ ≅ ρ₂ ↑⁺ Γ⁺₂
  ↑⁺-cong P.refl P.refl H.refl H.refl H.refl = H.refl

  id-cong : ∀ {Γ₁ Γ₂} → Γ₁ ≡ Γ₂ → id {Γ = Γ₁} ≅ id {Γ = Γ₂}
  id-cong P.refl = H.refl

  wk⁺-cong : ∀ {Γ₁} {Γ⁺₁ : Ctxt⁺ Γ₁} {Γ₂} {Γ⁺₂ : Ctxt⁺ Γ₂} →
             Γ₁ ≡ Γ₂ → Γ⁺₁ ≅ Γ⁺₂ → wk⁺ Γ⁺₁ ≅ wk⁺ Γ⁺₂
  wk⁺-cong P.refl H.refl = H.refl

  wk-cong : ∀ {Γ₁} {σ₁ : Type Γ₁} {Γ₂} {σ₂ : Type Γ₂} →
            Γ₁ ≡ Γ₂ → σ₁ ≅ σ₂ → wk {σ = σ₁} ≅ wk {σ = σ₂}
  wk-cong P.refl H.refl = H.refl

  sub-cong : ∀ {Γ₁ σ₁} {t₁ : Γ₁ ⊢ σ₁} {Γ₂ σ₂} {t₂ : Γ₂ ⊢ σ₂} →
             Γ₁ ≡ Γ₂ → σ₁ ≅ σ₂ → t₁ ≅ t₂ → sub t₁ ≅ sub t₂
  sub-cong P.refl H.refl H.refl = H.refl

  -- One can weaken either before or after looking up a variable.

  /∋-wk-subst : ∀ {Γ Δ σ τ} {ρ̂ : Γ ⇨̂ Δ} (x : Γ ∋ σ) (ρ : Sub ρ̂) →
                x /∋ wk-subst {σ = τ} ρ ≡ weaken {σ = τ} · (x /∋ ρ)
  /∋-wk-subst x ρ = P.refl

  abstract

    -- A corollary.

    /∋-wk-subst-var :
      ∀ {Γ Δ σ τ} {ρ̂ : Γ ⇨̂ Δ}
      (ρ : Sub ρ̂) (x : Γ ∋ τ) (y : Δ ∋ τ / ρ) →
      x /∋                  ρ ≡ var ·             y →
      x /∋ wk-subst {σ = σ} ρ ≡ var · suc {σ = σ} y
    /∋-wk-subst-var ρ x y hyp = begin
      x /∋ wk-subst ρ     ≡⟨ P.refl ⟩
      weaken · (x /∋ ρ)   ≡⟨ H.≅-to-≡ $ weaken-cong P.refl H.refl H.refl (H.≡-to-≅ hyp) ⟩
      weaken · (var · y)  ≡⟨ weaken-var y ⟩
      var · suc y         ∎
      where open P.≡-Reasoning

    -- The identity substitution has no effect.

    /-id : ∀ {Γ} (σ : Type Γ) → σ / id ≡ σ
    /-id σ = P.refl

    /⁺-id : ∀ {Γ} (Γ⁺ : Ctxt⁺ Γ) → Γ⁺ /⁺ id ≡ Γ⁺
    /⁺-id Γ⁺ = begin
      Γ⁺ /⁺ id  ≡⟨ P.refl ⟩
      Γ⁺ /̂⁺ îd  ≡⟨ /̂⁺-îd Γ⁺ ⟩
      Γ⁺        ∎
      where open P.≡-Reasoning

    mutual

      /∋-id : ∀ {Γ σ} (x : Γ ∋ σ) → x /∋ id ≡ var · x
      /∋-id {Γ = ε}     ()
      /∋-id {Γ = Γ ▻ τ} x = H.≅-to-≡ (begin
        x /∋ id ↑                ≅⟨ /∋-cong P.refl P.refl H.refl (H.refl {x = x})
                                      (▻̂-cong P.refl P.refl H.refl H.refl
                                         (H.≡-to-≅ $ corresponds var zero))
                                      (H.≡-subst-removable Sub
                                         (H.≅-to-≡ $
                                            ▻̂-cong P.refl P.refl H.refl H.refl
                                              (H.≡-to-≅ $ P.sym $ corresponds var zero))
                                         _) ⟩
        x /∋ (wk ▻⇨ var · zero)  ≅⟨ lemma x ⟩
        var · x                  ∎)
        where
        open H.≅-Reasoning

        lemma : ∀ {σ} (x : Γ ▻ τ ∋ σ) →
                x /∋ (wk {σ = τ} ▻⇨ var · zero) ≅ var · x
        lemma zero    = H.refl
        lemma (suc x) = H.≡-to-≅ $ /∋-wk x

      -- Weakening a variable is equivalent to incrementing it.

      /∋-wk : ∀ {Γ σ τ} (x : Γ ∋ σ) →
              x /∋ wk {σ = τ} ≡ var · suc x
      /∋-wk x = /∋-wk-subst-var id x x (/∋-id x)

    -- The n-ary lifting of the identity substitution is the identity
    -- substitution.

    id-↑⁺ : ∀ {Γ} (Γ⁺ : Ctxt⁺ Γ) → id ↑⁺ Γ⁺ ≅ id {Γ = Γ ++ Γ⁺}
    id-↑⁺ ε        = H.refl
    id-↑⁺ (Γ⁺ ▻ σ) = begin
      (id ↑⁺ Γ⁺) ↑  ≅⟨ ↑-cong P.refl (P.refl ++-cong H.≡-to-≅ (/⁺-id Γ⁺))
                              (îd-↑̂⁺ Γ⁺) (id-↑⁺ Γ⁺) H.refl ⟩
      id ↑          ∎
      where open H.≅-Reasoning
