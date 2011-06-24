------------------------------------------------------------------------
-- Some simple substitutions
------------------------------------------------------------------------

-- Given a term type which supports weakening and transformation of
-- variables to terms one can define various substitutions.

{-# OPTIONS --universe-polymorphism #-}

open import Universe

module deBruijn.Substitution.Data.Simple
  {u e} {Uni : Universe u e}
  where

import deBruijn.Context as Context
open import deBruijn.Substitution.Data.Basics
open import deBruijn.Substitution.Data.Map
import deBruijn.TermLike as TermLike
open import Function using (_$_)
open import Level using (_⊔_)
open import Relation.Binary.HeterogeneousEquality as H using (_≅_)
open import Relation.Binary.PropositionalEquality as P using (_≡_)

open Context Uni
open TermLike Uni

-- Simple substitutions.

record Simple {t} (T : Term-like t) : Set (u ⊔ e ⊔ t) where

  open Term-like T

  field

    -- Weakens terms.
    weaken : ∀ {Γ σ} → [ T ⟶ T ] (ŵk {Γ = Γ} {σ = σ})

    -- Takes variables to terms.
    var : [ Var ⟶⁼ T ]

    -- A property relating weaken and var.
    weaken-var : ∀ {Γ σ τ} (x : Γ ∋ σ) →
                 weaken {σ = τ} · (var · x) ≡ var · suc x

  -- Weakens substitutions.

  wk-subst : ∀ {Γ Δ σ} {ρ̂ : Γ ⇨̂ Δ} → Sub T ρ̂ → Sub T (ρ̂ ∘̂ ŵk {σ = σ})
  wk-subst ρ = map weaken ρ

  -- Lifting.

  infix 10 _↑ _↑⋆

  _↑ : ∀ {Γ Δ σ} {ρ̂ : Γ ⇨̂ Δ} → Sub T ρ̂ → Sub T (_↑̂ {σ = σ} ρ̂)
  ρ ↑ =
    P.subst (Sub T)
            (H.≅-to-≡ $ ▻̂-cong P.refl P.refl H.refl H.refl
                          (H.≡-to-≅ $ P.sym $ corresponds var zero))
            (wk-subst ρ ▻ var · zero)

  _↑⋆ : ∀ {Γ Δ σ} {ρ̂ : Γ ⇨̂ Δ} → Subs T ρ̂ → Subs T (_↑̂ {σ = σ} ρ̂)
  ε        ↑⋆ = ε
  (ρs ▻ ρ) ↑⋆ = ρs ↑⋆ ▻ ρ ↑

  -- N-ary lifting.

  infixl 10 _↑⁺_ _↑⁺⋆_

  _↑⁺_ : ∀ {Γ Δ} {ρ̂ : Γ ⇨̂ Δ} → Sub T ρ̂ → ∀ Γ⁺ → Sub T (ρ̂ ↑̂⁺ Γ⁺)
  ρ ↑⁺ ε        = ρ
  ρ ↑⁺ (Γ⁺ ▻ σ) = (ρ ↑⁺ Γ⁺) ↑

  _↑⁺⋆_ : ∀ {Γ Δ} {ρ̂ : Γ ⇨̂ Δ} → Subs T ρ̂ → ∀ Γ⁺ → Subs T (ρ̂ ↑̂⁺ Γ⁺)
  ρs ↑⁺⋆ ε        = ρs
  ρs ↑⁺⋆ (Γ⁺ ▻ σ) = (ρs ↑⁺⋆ Γ⁺) ↑⋆

  -- The identity substitution.

  id : ∀ {Γ} → Sub T (îd {Γ = Γ})
  id {ε}     = ε
  id {Γ ▻ σ} = id ↑

  -- N-ary weakening.

  wk⁺ : ∀ {Γ} (Γ⁺ : Ctxt⁺ Γ) → Sub T (ŵk⁺ Γ⁺)
  wk⁺ ε        = id
  wk⁺ (Γ⁺ ▻ σ) = wk-subst (wk⁺ Γ⁺)

  -- Weakening.

  wk : ∀ {Γ} {σ : Type Γ} → Sub T (ŵk {σ = σ})
  wk {σ = σ} = wk⁺ (ε ▻ σ)

  -- A substitution which only replaces the first variable.

  sub : ∀ {Γ σ} (t : Γ ⊢ σ) → Sub T (ŝub ⟦ t ⟧)
  sub t = id ▻ t

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

  wk-subst-cong : ∀ {Γ₁ Δ₁ σ₁} {ρ̂₁ : Γ₁ ⇨̂ Δ₁} {ρ₁ : Sub T ρ̂₁}
                    {Γ₂ Δ₂ σ₂} {ρ̂₂ : Γ₂ ⇨̂ Δ₂} {ρ₂ : Sub T ρ̂₂} →
                  Γ₁ ≡ Γ₂ → Δ₁ ≡ Δ₂ → σ₁ ≅ σ₂ → ρ̂₁ ≅ ρ̂₂ → ρ₁ ≅ ρ₂ →
                  wk-subst {σ = σ₁} ρ₁ ≅ wk-subst {σ = σ₂} ρ₂
  wk-subst-cong P.refl P.refl H.refl H.refl H.refl = H.refl

  ↑-cong : ∀ {Γ₁ Δ₁} {ρ̂₁ : Γ₁ ⇨̂ Δ₁} {ρ₁ : Sub T ρ̂₁} {σ₁}
             {Γ₂ Δ₂} {ρ̂₂ : Γ₂ ⇨̂ Δ₂} {ρ₂ : Sub T ρ̂₂} {σ₂} →
           Γ₁ ≡ Γ₂ → Δ₁ ≡ Δ₂ → ρ̂₁ ≅ ρ̂₂ → ρ₁ ≅ ρ₂ → σ₁ ≅ σ₂ →
           _↑ {σ = σ₁} ρ₁ ≅ _↑ {σ = σ₂} ρ₂
  ↑-cong P.refl P.refl H.refl H.refl H.refl = H.refl

  ↑⋆-cong : ∀ {Γ₁ Δ₁} {ρ̂₁ : Γ₁ ⇨̂ Δ₁} {ρs₁ : Subs T ρ̂₁} {σ₁}
              {Γ₂ Δ₂} {ρ̂₂ : Γ₂ ⇨̂ Δ₂} {ρs₂ : Subs T ρ̂₂} {σ₂} →
            Γ₁ ≡ Γ₂ → Δ₁ ≡ Δ₂ → ρ̂₁ ≅ ρ̂₂ → ρs₁ ≅ ρs₂ → σ₁ ≅ σ₂ →
            _↑⋆ {σ = σ₁} ρs₁ ≅ _↑⋆ {σ = σ₂} ρs₂
  ↑⋆-cong P.refl P.refl H.refl H.refl H.refl = H.refl

  ↑⁺-cong : ∀ {Γ₁ Δ₁} {ρ̂₁ : Γ₁ ⇨̂ Δ₁} {ρ₁ : Sub T ρ̂₁} {Γ⁺₁}
              {Γ₂ Δ₂} {ρ̂₂ : Γ₂ ⇨̂ Δ₂} {ρ₂ : Sub T ρ̂₂} {Γ⁺₂} →
            Γ₁ ≡ Γ₂ → Δ₁ ≡ Δ₂ → ρ̂₁ ≅ ρ̂₂ → ρ₁ ≅ ρ₂ → Γ⁺₁ ≅ Γ⁺₂ →
            ρ₁ ↑⁺ Γ⁺₁ ≅ ρ₂ ↑⁺ Γ⁺₂
  ↑⁺-cong P.refl P.refl H.refl H.refl H.refl = H.refl

  ↑⁺⋆-cong : ∀ {Γ₁ Δ₁} {ρ̂₁ : Γ₁ ⇨̂ Δ₁} {ρs₁ : Subs T ρ̂₁} {Γ⁺₁}
               {Γ₂ Δ₂} {ρ̂₂ : Γ₂ ⇨̂ Δ₂} {ρs₂ : Subs T ρ̂₂} {Γ⁺₂} →
             Γ₁ ≡ Γ₂ → Δ₁ ≡ Δ₂ → ρ̂₁ ≅ ρ̂₂ → ρs₁ ≅ ρs₂ → Γ⁺₁ ≅ Γ⁺₂ →
             ρs₁ ↑⁺⋆ Γ⁺₁ ≅ ρs₂ ↑⁺⋆ Γ⁺₂
  ↑⁺⋆-cong P.refl P.refl H.refl H.refl H.refl = H.refl

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

  abstract

    -- Unfolding lemma for _↑.

    unfold-↑ : ∀ {Γ Δ σ} {ρ̂ : Γ ⇨̂ Δ} (ρ : Sub T ρ̂) →
               _↑ {σ = σ} ρ ≅
               Sub._▻_ {σ = σ} (wk-subst {σ = σ / ρ} ρ) (var · zero)
    unfold-↑ _ =
      H.≡-subst-removable
        (Sub T)
        (H.≅-to-≡ $ ▻̂-cong P.refl P.refl H.refl H.refl
                      (H.≡-to-≅ $ P.sym $ corresponds var zero))
        _

    -- Some lemmas relating variables to lifting.

    /∋-↑ : ∀ {Γ Δ σ τ} {ρ̂ : Γ ⇨̂ Δ} (x : Γ ▻ σ ∋ τ) (ρ : Sub T ρ̂) →
           x /∋ ρ ↑ ≅ x /∋ (wk-subst {σ = σ / ρ} ρ ▻ var · zero)
    /∋-↑ x ρ =
      /∋-cong P.refl P.refl H.refl (H.refl {x = x})
        (H.sym $ ▻̂-cong P.refl P.refl H.refl H.refl
                   (H.≡-to-≅ $ P.sym $ corresponds var zero))
        (unfold-↑ ρ)

    zero-/∋-↑ : ∀ {Γ Δ} σ {ρ̂ : Γ ⇨̂ Δ} (ρ : Sub T ρ̂) →
                zero {σ = σ} /∋ ρ ↑ ≡ var · zero
    zero-/∋-↑ σ ρ = begin
      zero {σ = σ} /∋ ρ ↑                        ≅⟨ /∋-↑ (zero {σ = σ}) ρ ⟩
      zero {σ = σ} /∋ (wk-subst ρ ▻ var · zero)  ≡⟨ P.refl ⟩
      var · zero                                 ∎
      where open P.≡-Reasoning

    suc-/∋-↑ : ∀ {Γ Δ τ} σ {ρ̂ : Γ ⇨̂ Δ} (x : Γ ∋ τ) (ρ : Sub T ρ̂) →
               suc {σ = σ} x /∋ ρ ↑ ≡ x /∋ wk-subst ρ
    suc-/∋-↑ σ x ρ = begin
      suc {σ = σ} x /∋ ρ ↑                        ≅⟨ /∋-↑ (suc {σ = σ} x) ρ ⟩
      suc {σ = σ} x /∋ (wk-subst ρ ▻ var · zero)  ≡⟨ P.refl ⟩
      x /∋ wk-subst ρ                     ∎
      where open P.≡-Reasoning

    -- One can weaken either before or after looking up a variable.

    /∋-wk-subst : ∀ {Γ Δ σ τ} {ρ̂ : Γ ⇨̂ Δ} (x : Γ ∋ σ) (ρ : Sub T ρ̂) →
                  x /∋ wk-subst {σ = τ} ρ ≡ weaken {σ = τ} · (x /∋ ρ)
    /∋-wk-subst x ρ = /∋-map x weaken ρ

    -- A corollary.

    /∋-wk-subst-var :
      ∀ {Γ Δ σ τ} {ρ̂ : Γ ⇨̂ Δ}
      (ρ : Sub T ρ̂) (x : Γ ∋ τ) (y : Δ ∋ τ / ρ) →
      x /∋                  ρ ≡ var ·             y →
      x /∋ wk-subst {σ = σ} ρ ≡ var · suc {σ = σ} y
    /∋-wk-subst-var ρ x y hyp = begin
      x /∋ wk-subst ρ     ≡⟨ /∋-wk-subst x ρ ⟩
      weaken · (x /∋ ρ)   ≅⟨ weaken-cong P.refl H.refl H.refl (H.≡-to-≅ hyp) ⟩
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
        x /∋ id ↑               ≅⟨ /∋-↑ x id ⟩
        x /∋ (wk ▻ var · zero)  ≅⟨ lemma x ⟩
        var · x                 ∎)
        where
        open H.≅-Reasoning

        lemma : ∀ {σ} (x : Γ ▻ τ ∋ σ) →
                x /∋ (wk {σ = τ} ▻ var · zero) ≅ var · x
        lemma zero    = H.refl
        lemma (suc x) = H.≡-to-≅ $ /∋-wk x

      -- Weakening a variable is equivalent to incrementing it.

      /∋-wk : ∀ {Γ σ τ} (x : Γ ∋ τ) →
              x /∋ wk {σ = σ} ≡ var · suc x
      /∋-wk x = /∋-wk-subst-var id x x (/∋-id x)

    -- The n-ary lifting of the identity substitution is the identity
    -- substitution.

    id-↑⁺ : ∀ {Γ} (Γ⁺ : Ctxt⁺ Γ) → id ↑⁺ Γ⁺ ≅ id {Γ = Γ ++ Γ⁺}
    id-↑⁺ ε        = H.refl
    id-↑⁺ (Γ⁺ ▻ σ) = begin
      (id ↑⁺ Γ⁺) ↑  ≅⟨ ↑-cong P.refl (++-cong P.refl (H.≡-to-≅ $ /⁺-id Γ⁺))
                              (îd-↑̂⁺ Γ⁺) (id-↑⁺ Γ⁺) H.refl ⟩
      id ↑          ∎
      where open H.≅-Reasoning

    ε-↑⁺⋆ : ∀ {Γ} (Γ⁺ : Ctxt⁺ Γ) →
          ε ↑⁺⋆ Γ⁺ ≅ Subs.ε {T = T} {Γ = Γ ++ Γ⁺}
    ε-↑⁺⋆ ε        = H.refl
    ε-↑⁺⋆ (Γ⁺ ▻ σ) = begin
      (ε ↑⁺⋆ Γ⁺) ↑⋆  ≅⟨ ↑⋆-cong P.refl (++-cong P.refl (H.≡-to-≅ $ /̂⁺-îd Γ⁺))
                                (îd-↑̂⁺ Γ⁺) (ε-↑⁺⋆ Γ⁺) H.refl ⟩
      ε ↑⋆           ≡⟨ P.refl ⟩
      ε              ∎
      where open H.≅-Reasoning

    -- The identity substitution has no effect even if lifted.

    /∋-id-↑⁺ : ∀ {Γ} Γ⁺ {σ} (x : Γ ++ Γ⁺ ∋ σ) → x /∋ id ↑⁺ Γ⁺ ≅ var · x
    /∋-id-↑⁺ Γ⁺ x = begin
      x /∋ id ↑⁺ Γ⁺  ≅⟨ /∋-cong P.refl (++-cong P.refl (H.≡-to-≅ $ /⁺-id Γ⁺))
                                H.refl (H.refl {x = x}) (îd-↑̂⁺ Γ⁺) (id-↑⁺ Γ⁺) ⟩
      x /∋ id        ≡⟨ /∋-id x ⟩
      var · x        ∎
      where open H.≅-Reasoning

    -- N-ary lifting distributes over composition.

    ▻-↑⁺⋆ : ∀ {Γ Δ Ε} {ρ̂₁ : Γ ⇨̂ Δ} {ρ̂₂ : Δ ⇨̂ Ε}
            (ρs : Subs T ρ̂₁) (ρ : Sub T ρ̂₂) Γ⁺ →
            (ρs ▻ ρ) ↑⁺⋆ Γ⁺ ≅ Subs._▻_ (ρs ↑⁺⋆ Γ⁺) (ρ ↑⁺ (Γ⁺ /⁺⋆ ρs))
    ▻-↑⁺⋆ ρs ρ ε        = H.refl
    ▻-↑⁺⋆ ρs ρ (Γ⁺ ▻ σ) = begin
      ((ρs ▻ ρ) ↑⁺⋆ Γ⁺) ↑⋆                   ≅⟨ ↑⋆-cong P.refl
                                                        (++-cong P.refl (H.≡-to-≅ $ /̂⁺-∘̂ Γ⁺ ⟦ ρs ⟧⇨⋆ ⟦ ρ ⟧⇨))
                                                        (∘̂-↑̂⁺ ⟦ ρs ⟧⇨⋆ ⟦ ρ ⟧⇨ Γ⁺) (▻-↑⁺⋆ ρs ρ Γ⁺) H.refl ⟩
      (ρs ↑⁺⋆ Γ⁺ ▻ ρ ↑⁺ (Γ⁺ /⁺⋆ ρs)) ↑⋆      ≡⟨ P.refl ⟩
      (ρs ↑⁺⋆ Γ⁺) ↑⋆ ▻ (ρ ↑⁺ (Γ⁺ /⁺⋆ ρs)) ↑  ∎
      where open H.≅-Reasoning

    -- If ρ is morally a renaming, then "deep application" of ρ to a
    -- variable is still a variable.

    /∋-↑⁺ : ∀ {Γ Δ} {ρ̂ : Γ ⇨̂ Δ}
            (ρ : Sub T ρ̂) (f : [ Var ⟶ Var ] ρ̂) →
            (∀ {σ} (x : Γ ∋ σ) → x /∋ ρ ≡ var · (f · x)) →
            ∀ Γ⁺ {σ} (x : Γ ++ Γ⁺ ∋ σ) →
            x /∋ ρ ↑⁺ Γ⁺ ≡ var · (lift f Γ⁺ · x)
    /∋-↑⁺ ρ f hyp ε        x    = hyp x
    /∋-↑⁺ ρ f hyp (Γ⁺ ▻ σ) zero = begin
      zero {σ = σ} /∋ (ρ ↑⁺ Γ⁺) ↑  ≡⟨ zero-/∋-↑ σ (ρ ↑⁺ Γ⁺) ⟩
      var · zero                   ∎
      where open P.≡-Reasoning
    /∋-↑⁺ ρ f hyp (Γ⁺ ▻ σ) (suc x) = begin
      suc {σ = σ} x /∋ (ρ ↑⁺ Γ⁺) ↑      ≡⟨ suc-/∋-↑ σ x (ρ ↑⁺ Γ⁺) ⟩
      x /∋ wk-subst (ρ ↑⁺ Γ⁺)           ≡⟨ /∋-wk-subst x (ρ ↑⁺ Γ⁺) ⟩
      weaken · (x /∋ ρ ↑⁺ Γ⁺)           ≅⟨ weaken-cong P.refl H.refl H.refl
                                                       (H.≡-to-≅ $ /∋-↑⁺ ρ f hyp Γ⁺ x) ⟩
      weaken · (var · (lift f Γ⁺ · x))  ≡⟨ weaken-var (lift f Γ⁺ · x) ⟩
      var · suc (lift f Γ⁺ · x)         ∎
      where open P.≡-Reasoning

    -- "Deep weakening" of a variable can be expressed without
    -- reference to the weaken function.

    /∋-wk-↑⁺ : ∀ {Γ σ} Γ⁺ {τ} (x : Γ ++ Γ⁺ ∋ τ) →
               x /∋ wk {σ = σ} ↑⁺ Γ⁺ ≡
               var · (lift weaken∋ Γ⁺ · x)
    /∋-wk-↑⁺ = /∋-↑⁺ wk weaken∋ /∋-wk

    /∋-wk-↑⁺-↑⁺ : ∀ {Γ σ} Γ⁺ Γ⁺⁺ {τ} (x : Γ ++ Γ⁺ ++ Γ⁺⁺ ∋ τ) →
                  x /∋ wk {σ = σ} ↑⁺ Γ⁺ ↑⁺ Γ⁺⁺ ≡
                  var · (lift (lift weaken∋ Γ⁺) Γ⁺⁺ · x)
    /∋-wk-↑⁺-↑⁺ Γ⁺ = /∋-↑⁺ (wk ↑⁺ Γ⁺) (lift weaken∋ Γ⁺) (/∋-wk-↑⁺ Γ⁺)

    -- Two n-ary liftings can be merged into one.

    ↑⁺-++⁺ : ∀ {Γ Δ} {ρ̂ : Γ ⇨̂ Δ} (ρ : Sub T ρ̂) Γ⁺ Γ⁺⁺ →
             ρ ↑⁺ (Γ⁺ ++⁺ Γ⁺⁺) ≅ ρ ↑⁺ Γ⁺ ↑⁺ Γ⁺⁺
    ↑⁺-++⁺ ρ Γ⁺ ε         = H.refl
    ↑⁺-++⁺ ρ Γ⁺ (Γ⁺⁺ ▻ σ) = begin
      (ρ ↑⁺ (Γ⁺ ++⁺ Γ⁺⁺)) ↑  ≅⟨ ↑-cong (P.sym $ ++-assoc Γ⁺ Γ⁺⁺) (++-++⁺-/̂⁺ ⟦ ρ ⟧⇨ Γ⁺ Γ⁺⁺)
                                       (↑̂⁺-++⁺ ⟦ ρ ⟧⇨ Γ⁺ Γ⁺⁺) (↑⁺-++⁺ ρ Γ⁺ Γ⁺⁺)
                                       (H.≡-subst-removable Type (++-assoc Γ⁺ Γ⁺⁺) σ) ⟩
      (ρ ↑⁺ Γ⁺ ↑⁺ Γ⁺⁺) ↑     ∎
      where open H.≅-Reasoning
