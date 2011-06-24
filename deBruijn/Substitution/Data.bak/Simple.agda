------------------------------------------------------------------------
-- Some simple substitutions
------------------------------------------------------------------------

-- Given a term type which supports weakening and transformation of
-- variables to terms one can define various substitutions.

{-# OPTIONS --universe-polymorphism #-}

open import Universe

module deBruijn.Substitution.Data.Simple
  {u e} (Uni : Universe u e)
  where

import deBruijn.Context as Context
import deBruijn.Substitution.Basics as Basics
open import Function using (_$_)
open import Level using (_⊔_)
open import Relation.Binary.HeterogeneousEquality as H using (_≅_)
open import Relation.Binary.PropositionalEquality as P using (_≡_)

open Context Uni

record Simple {t} (T : Term-like t) : Set (u ⊔ e ⊔ t) where

  open Term-like T
  open Basics    T

  field

    -- Weakens terms.
    weaken       : ∀ {Γ σ τ} → Γ ⊢ σ → Γ ▻ τ ⊢ σ /̂ ŵk
    weaken-lemma : ∀ {Γ σ τ} (t : Γ ⊢ σ) →
                   ⟦ t ⟧ /Val ŵk {σ = τ} ≡ ⟦ weaken {τ = τ} t ⟧

    -- Takes variables to terms.
    var       : ∀ {Γ σ} → Γ ∋ σ → Γ ⊢ σ
    var-lemma : ∀ {Γ σ} (x : Γ ∋ σ) → lookup x ≡ ⟦ var x ⟧

    -- A property relating weaken and var.
    weaken-var : ∀ {Γ σ τ} (x : Γ ∋ σ) →
                 weaken {τ = τ} (var x) ≡ var (suc x)

  mutual

    -- Weakens substitutions.

    wk-subst : ∀ {Γ Δ σ} → Γ ⇨ Δ → Γ ⇨ Δ ▻ σ
    wk-subst ε                 = ε
    wk-subst (_▻_ {σ = τ} ρ t) =
      wk-subst ρ ▻
      P.subst (λ ρ → _ ⊢ τ /̂ ρ) (wk-subst-lemma ρ) (weaken t)

    abstract

      wk-subst-lemma :
        ∀ {Γ Δ σ} (ρ : Γ ⇨ Δ) →
        ⟦ ρ ⟧⇨ ∘̂ ŵk ≡ ⟦ wk-subst {σ = σ} ρ ⟧⇨
      wk-subst-lemma         ε                                 = P.refl
      wk-subst-lemma {σ = σ} (_▻_ {Γ = Γ} {Δ = Δ} {σ = τ} ρ t) =
        H.≅-to-≡ $
        ▻̂-cong P.refl P.refl H.refl (H.≡-to-≅ $ wk-subst-lemma ρ) lemma
        where
        open H.≅-Reasoning

        lemma = begin
          ⟦ t ⟧ /Val ŵk                 ≅⟨ H.≡-to-≅ $ weaken-lemma t ⟩
          ⟦ weaken t ⟧                  ≅⟨ ⟦⟧-cong P.refl
                                                   (/̂-cong P.refl P.refl (H.refl {x = τ})
                                                           (H.≡-to-≅ $ wk-subst-lemma ρ))
                                                   (H.sym $ H.≡-subst-removable (λ ρ → _ ⊢ τ /̂ ρ)
                                                                                (wk-subst-lemma ρ) _) ⟩
          ⟦ P.subst (λ ρ → _ ⊢ τ /̂ ρ)
                    (wk-subst-lemma ρ)
                    (weaken t) ⟧        ∎

  -- Lifting.

  infix 10 _↑ _↑-lemma

  _↑ : ∀ {Γ Δ σ} (ρ : Γ ⇨ Δ) → Γ ▻ σ ⇨ Δ ▻ σ / ρ
  _↑ {σ = σ} ρ =
    wk-subst ρ ▻
    P.subst (λ ρ → _ ⊢ σ /̂ ρ) (wk-subst-lemma ρ) (var zero)

  abstract

    _↑-lemma : ∀ {Γ Δ σ} (ρ : Γ ⇨ Δ) →
               ⟦ ρ ⟧⇨ ↑̂ ≡ ⟦ _↑ {σ = σ} ρ ⟧⇨
    _↑-lemma {Γ} {Δ} {σ} ρ =
      H.≅-to-≡ $
      ▻̂-cong P.refl P.refl H.refl (H.≡-to-≅ $ wk-subst-lemma ρ) lemma
      where
      open H.≅-Reasoning

      lemma = begin
        lookup zero                   ≅⟨ H.≡-to-≅ $ var-lemma zero ⟩
        ⟦ var zero ⟧                  ≅⟨ ⟦⟧-cong P.refl
                                                 (/̂-cong P.refl P.refl (H.refl {x = σ})
                                                         (H.≡-to-≅ $ wk-subst-lemma ρ))
                                                 (H.sym $ H.≡-subst-removable (λ ρ → _ ⊢ σ /̂ ρ)
                                                                              (wk-subst-lemma ρ) _) ⟩
        ⟦ P.subst (λ ρ → _ ⊢ σ /̂ ρ)
                  (wk-subst-lemma ρ)
                  (var zero) ⟧        ∎

  -- Application of substitutions to context extensions.

  infixl 8 _/⁺_

  _/⁺_ : ∀ {Γ Δ} → Ctxt⁺ Γ → Γ ⇨ Δ → Ctxt⁺ Δ
  Γ⁺ /⁺ ρ = Γ⁺ /̂⁺ ⟦ ρ ⟧⇨

  mutual

    -- N-ary lifting.

    infixl 10 _↑⁺_ _↑⁺-lemma_

    _↑⁺_ : ∀ {Γ Δ} (ρ : Γ ⇨ Δ) Γ⁺ → Γ ++ Γ⁺ ⇨ Δ ++ Γ⁺ /⁺ ρ
    ρ ↑⁺ ε        = ρ
    ρ ↑⁺ (Γ⁺ ▻ σ) =
      P.subst (λ ρ′ → _ ++ Γ⁺ ▻ σ ⇨ _ ++ Γ⁺ /⁺ ρ ▻ σ /̂ ρ′)
              (P.sym $ ρ ↑⁺-lemma Γ⁺)
              ((ρ ↑⁺ Γ⁺) ↑)

    abstract

      _↑⁺-lemma_ : ∀ {Γ Δ} (ρ : Γ ⇨ Δ) Γ⁺ → ⟦ ρ ⟧⇨ ↑̂⁺ Γ⁺ ≡ ⟦ ρ ↑⁺ Γ⁺ ⟧⇨
      ρ ↑⁺-lemma ε        = P.refl
      ρ ↑⁺-lemma (Γ⁺ ▻ σ) = H.≅-to-≡ (begin
        (⟦ ρ ⟧⇨ ↑̂⁺ Γ⁺) ↑̂                                        ≅⟨ ↑̂-cong P.refl P.refl (H.≡-to-≅ $ ρ ↑⁺-lemma Γ⁺) H.refl ⟩
        ⟦ ρ ↑⁺ Γ⁺ ⟧⇨ ↑̂                                          ≡⟨ (ρ ↑⁺ Γ⁺) ↑-lemma ⟩
        ⟦ (ρ ↑⁺ Γ⁺) ↑ ⟧⇨                                        ≅⟨ ⟦⟧⇨-cong P.refl
                                                                            (▻-cong P.refl
                                                                                    (/̂-cong P.refl P.refl (H.refl {x = σ})
                                                                                            (H.≡-to-≅ $ P.sym $ ρ ↑⁺-lemma Γ⁺)))
                                                                            (H.sym $ H.≡-subst-removable
                                                                                       (λ ρ′ → _ ++ Γ⁺ ▻ σ ⇨ _ ++ Γ⁺ /⁺ ρ ▻ σ /̂ ρ′)
                                                                                       (P.sym $ ρ ↑⁺-lemma Γ⁺) _) ⟩
        ⟦ P.subst (λ ρ′ → _ ++ Γ⁺ ▻ σ ⇨ _ ++ Γ⁺ /⁺ ρ ▻ σ /̂ ρ′)
                  (P.sym $ ρ ↑⁺-lemma Γ⁺)
                  ((ρ ↑⁺ Γ⁺) ↑) ⟧⇨                              ∎)
        where open H.≅-Reasoning

  -- The identity substitution.

  mutual

    id : ∀ {Γ} → Γ ⇨ Γ
    id {ε}     = ε
    id {Γ ▻ σ} =
      P.subst (λ ρ → Γ ▻ σ ⇨ Γ ▻ σ /̂ ρ) (P.sym $ id-lemma Γ) (id ↑)

    abstract

      id-lemma : ∀ Γ → îd ≡ ⟦ id {Γ = Γ} ⟧⇨
      id-lemma ε       = P.refl
      id-lemma (Γ ▻ σ) = H.≅-to-≡ (begin
        îd ↑̂                                 ≅⟨ ↑̂-cong P.refl P.refl (H.≡-to-≅ $ id-lemma Γ) H.refl ⟩
        ⟦ id ⟧⇨ ↑̂                            ≡⟨ id ↑-lemma ⟩
        ⟦ id ↑ ⟧⇨                            ≅⟨ ⟦⟧⇨-cong P.refl
                                                         (▻-cong P.refl
                                                                 (/̂-cong P.refl P.refl (H.refl {x = σ})
                                                                         (H.≡-to-≅ $ P.sym $ id-lemma Γ)))
                                                         (H.sym $ H.≡-subst-removable (λ ρ → Γ ▻ σ ⇨ Γ ▻ σ /̂ ρ)
                                                                                      (P.sym $ id-lemma Γ) _) ⟩
        ⟦ P.subst (λ ρ → Γ ▻ σ ⇨ Γ ▻ σ /̂ ρ)
                  (P.sym $ id-lemma Γ)
                  (id ↑) ⟧⇨                  ∎)
        where open H.≅-Reasoning

  -- N-ary weakening.

  wk⁺ : ∀ {Γ} Γ⁺ → Γ ⇨ Γ ++ Γ⁺
  wk⁺ ε        = id
  wk⁺ (Γ⁺ ▻ σ) = wk-subst (wk⁺ Γ⁺)

  abstract

    wk⁺-lemma : ∀ {Γ} (Γ⁺ : Ctxt⁺ Γ) → ŵk⁺ Γ⁺ ≡ ⟦ wk⁺ Γ⁺ ⟧⇨
    wk⁺-lemma ε        = id-lemma _
    wk⁺-lemma (Γ⁺ ▻ σ) = begin
      ŵk⁺ Γ⁺ ∘̂ ŵk             ≡⟨ P.cong (λ ρ → ρ ∘̂ ŵk) (wk⁺-lemma Γ⁺) ⟩
      ⟦ wk⁺ Γ⁺ ⟧⇨ ∘̂ ŵk        ≡⟨ wk-subst-lemma (wk⁺ Γ⁺) ⟩
      ⟦ wk-subst (wk⁺ Γ⁺) ⟧⇨  ∎
      where open P.≡-Reasoning

  -- Weakening.

  wk : ∀ {Γ σ} → Γ ⇨ Γ ▻ σ
  wk {σ = σ} = wk⁺ (ε ▻ σ)

  abstract

    wk-lemma : ∀ {Γ} (σ : Type Γ) → ŵk {σ = σ} ≡ ⟦ wk {σ = σ} ⟧⇨
    wk-lemma σ = wk⁺-lemma (ε ▻ σ)

  -- A substitution which only replaces the first variable.

  sub : ∀ {Γ σ} → Γ ⊢ σ → Γ ▻ σ ⇨ Γ
  sub {σ = σ} t = id ▻ P.subst (λ ρ → _ ⊢ σ /̂ ρ) (id-lemma _) t

  abstract

    sub-lemma : ∀ {Γ σ} (t : Γ ⊢ σ) → ŝub ⟦ t ⟧ ≡ ⟦ sub t ⟧⇨
    sub-lemma {Γ} {σ} t = H.≅-to-≡ $
      ▻̂-cong P.refl P.refl H.refl (H.≡-to-≅ $ id-lemma Γ)
             (⟦⟧-cong P.refl
                      (/̂-cong P.refl P.refl (H.refl {x = σ})
                              (H.≡-to-≅ $ id-lemma _))
                      (H.sym $ H.≡-subst-removable (λ ρ → Γ ⊢ σ /̂ ρ)
                                                   (id-lemma _) t))

  -- Some congruence lemmas.

  weaken-cong : ∀ {Γ₁ σ₁ τ₁} {t₁ : Γ₁ ⊢ σ₁}
                  {Γ₂ σ₂ τ₂} {t₂ : Γ₂ ⊢ σ₂} →
                Γ₁ ≡ Γ₂ → σ₁ ≅ σ₂ → τ₁ ≅ τ₂ → t₁ ≅ t₂ →
                weaken {τ = τ₁} t₁ ≅ weaken {τ = τ₂} t₂
  weaken-cong P.refl H.refl H.refl H.refl = H.refl

  var-cong : ∀ {Γ₁ σ₁} {x₁ : Γ₁ ∋ σ₁}
               {Γ₂ σ₂} {x₂ : Γ₂ ∋ σ₂} →
               Γ₁ ≡ Γ₂ → σ₁ ≅ σ₂ → x₁ ≅ x₂ →
               var x₁ ≅ var x₂
  var-cong P.refl H.refl H.refl = H.refl

  wk-subst-cong : ∀ {Γ₁ Δ₁ σ₁} {ρ₁ : Γ₁ ⇨ Δ₁}
                    {Γ₂ Δ₂ σ₂} {ρ₂ : Γ₂ ⇨ Δ₂} →
                  Γ₁ ≡ Γ₂ → Δ₁ ≡ Δ₂ → σ₁ ≅ σ₂ → ρ₁ ≅ ρ₂ →
                  wk-subst {σ = σ₁} ρ₁ ≅ wk-subst {σ = σ₂} ρ₂
  wk-subst-cong P.refl P.refl H.refl H.refl = H.refl

  ↑-cong : ∀ {Γ₁ Δ₁} {ρ₁ : Γ₁ ⇨ Δ₁} {σ₁}
             {Γ₂ Δ₂} {ρ₂ : Γ₂ ⇨ Δ₂} {σ₂} →
           Γ₁ ≡ Γ₂ → Δ₁ ≡ Δ₂ → ρ₁ ≅ ρ₂ → σ₁ ≅ σ₂ →
           _↑ {σ = σ₁} ρ₁ ≅ _↑ {σ = σ₂} ρ₂
  ↑-cong P.refl P.refl H.refl H.refl = H.refl

  /⁺-cong : ∀ {Γ₁ Δ₁} {Γ⁺₁ : Ctxt⁺ Γ₁} {ρ₁ : Γ₁ ⇨ Δ₁}
              {Γ₂ Δ₂} {Γ⁺₂ : Ctxt⁺ Γ₂} {ρ₂ : Γ₂ ⇨ Δ₂} →
            Γ₁ ≡ Γ₂ → Δ₁ ≡ Δ₂ → Γ⁺₁ ≅ Γ⁺₂ → ρ₁ ≅ ρ₂ →
            Γ⁺₁ /⁺ ρ₁ ≅ Γ⁺₂ /⁺ ρ₂
  /⁺-cong P.refl P.refl H.refl H.refl = H.refl

  ↑⁺-cong : ∀ {Γ₁ Δ₁} {ρ₁ : Γ₁ ⇨ Δ₁} {Γ⁺₁ : Ctxt⁺ Γ₁}
              {Γ₂ Δ₂} {ρ₂ : Γ₂ ⇨ Δ₂} {Γ⁺₂ : Ctxt⁺ Γ₂} →
            Γ₁ ≡ Γ₂ → Δ₁ ≡ Δ₂ → ρ₁ ≅ ρ₂ → Γ⁺₁ ≅ Γ⁺₂ →
            ρ₁ ↑⁺ Γ⁺₁ ≅ ρ₂ ↑⁺ Γ⁺₂
  ↑⁺-cong P.refl P.refl H.refl H.refl = H.refl

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

    -- One can weaken either before or after looking up a variable.

    /∋-wk-subst : ∀ {Γ Δ σ τ} (x : Γ ∋ σ) (ρ : Γ ⇨ Δ) →
                  x /∋ wk-subst {σ = τ} ρ ≅ weaken {τ = τ} (x /∋ ρ)
    /∋-wk-subst zero (_▻_ {σ = τ} ρ t) = begin
      P.subst (λ ρ → _ ⊢ τ /̂ ρ) (wk-subst-lemma ρ)
              (weaken t)                            ≅⟨ H.≡-subst-removable (λ ρ → _ ⊢ τ /̂ ρ) (wk-subst-lemma ρ) _ ⟩
      weaken t                                      ∎
      where open H.≅-Reasoning
    /∋-wk-subst (suc x) (ρ ▻ t) = /∋-wk-subst x ρ

    -- A corollary.

    /∋-wk-subst-var : ∀ {Γ Δ σ τ υ} ρ (x : Γ ∋ σ) (y : Δ ∋ υ) →
                      σ / ρ ≡ υ →
                      x /∋                  ρ ≅ var              y →
                      x /∋ wk-subst {σ = τ} ρ ≅ var (suc {σ = τ} y)
    /∋-wk-subst-var ρ x y hyp₁ hyp₂ = begin
      x /∋ wk-subst ρ  ≅⟨ /∋-wk-subst x ρ ⟩
      weaken (x /∋ ρ)  ≅⟨ weaken-cong P.refl (H.≡-to-≅ hyp₁) H.refl hyp₂ ⟩
      weaken (var y)   ≡⟨ weaken-var y ⟩
      var (suc y)      ∎
      where open H.≅-Reasoning

    -- The identity substitution has no effect.

    /-id : ∀ {Γ} (σ : Type Γ) → σ / id ≡ σ
    /-id σ = begin
      σ / id  ≡⟨ P.cong (λ ρ → σ /̂ ρ) $ P.sym $ id-lemma _ ⟩
      σ /̂ îd  ≡⟨ /̂-îd σ ⟩
      σ       ∎
      where open P.≡-Reasoning

    /⁺-id : ∀ {Γ} (Γ⁺ : Ctxt⁺ Γ) → Γ⁺ /⁺ id ≡ Γ⁺
    /⁺-id Γ⁺ = begin
      Γ⁺ /⁺ id  ≡⟨ P.cong (λ ρ → Γ⁺ /̂⁺ ρ) $ P.sym $ id-lemma _ ⟩
      Γ⁺ /̂⁺ îd  ≡⟨ /̂⁺-îd Γ⁺ ⟩
      Γ⁺        ∎
      where open P.≡-Reasoning

    mutual

      /∋-id : ∀ {Γ σ} (x : Γ ∋ σ) → x /∋ id ≅ var x
      /∋-id (zero {Γ = Γ} {σ = σ}) = begin
        zero /∋ P.subst (λ ρ → Γ ▻ σ ⇨ Γ ▻ σ /̂ ρ)
                        (P.sym $ id-lemma Γ) (id ↑)    ≅⟨ /∋-cong P.refl (▻-cong P.refl (H.sym $ H.≡-to-≅ $ /-id σ))
                                                                  H.refl (H.refl {x = zero})
                                                                  (H.≡-subst-removable (λ ρ → Γ ▻ σ ⇨ Γ ▻ σ /̂ ρ)
                                                                                       (P.sym $ id-lemma Γ) _) ⟩
        zero {σ = σ} /∋ id ↑                           ≡⟨ P.refl ⟩
        P.subst (λ ρ → _ ⊢ σ /̂ ρ) (wk-subst-lemma id)
                (var (zero {σ = σ / id}))              ≅⟨ H.≡-subst-removable (λ ρ → _ ⊢ σ /̂ ρ) (wk-subst-lemma id) _ ⟩
        var (zero {σ = σ / id})                        ≅⟨ (let lem  = H.≡-to-≅ (/-id σ)
                                                               lem′ = ▻-cong P.refl lem in
                                                           var-cong lem′
                                                                    (/̂-cong P.refl lem′ lem (ŵk-cong P.refl lem))
                                                                    (zero-cong P.refl lem)) ⟩
        var (zero {σ = σ})                             ∎
        where open H.≅-Reasoning
      /∋-id (suc {Γ = Γ} {τ = τ} x) = begin
        suc x /∋ P.subst (λ ρ → Γ ▻ τ ⇨ Γ ▻ τ /̂ ρ)
                         (P.sym $ id-lemma Γ) (id ↑)  ≅⟨ /∋-cong P.refl (▻-cong P.refl (H.sym $ H.≡-to-≅ $ /-id τ))
                                                                 H.refl (H.refl {x = suc x})
                                                                 (H.≡-subst-removable (λ ρ → Γ ▻ τ ⇨ Γ ▻ τ /̂ ρ)
                                                                                      (P.sym $ id-lemma Γ) _) ⟩
        suc {σ = τ} x /∋ id ↑                         ≡⟨ P.refl ⟩
        x /∋ wk-subst {σ = τ / id} id                 ≡⟨ P.refl ⟩
        x /∋ wk {σ = τ / id}                          ≅⟨ /∋-cong P.refl (▻-cong P.refl (H.≡-to-≅ $ /-id τ))
                                                                 H.refl (H.refl {x = x})
                                                                 (wk-cong P.refl (H.≡-to-≅ $ /-id τ)) ⟩
        x /∋ wk {σ = τ}                               ≅⟨ /∋-wk x ⟩
        var (suc {σ = τ} x)                           ∎
        where open H.≅-Reasoning

      -- Weakening a variable is equivalent to incrementing it.

      /∋-wk : ∀ {Γ σ τ} (x : Γ ∋ σ) →
              x /∋ wk {σ = τ} ≅ var (suc {σ = τ} x)
      /∋-wk x = /∋-wk-subst-var id x x (/-id _) (/∋-id x)

    -- The n-ary lifting of the identity substitution is the identity
    -- substitution.

    id-↑⁺ : ∀ {Γ} (Γ⁺ : Ctxt⁺ Γ) → id ↑⁺ Γ⁺ ≅ id {Γ = Γ ++ Γ⁺}
    id-↑⁺ ε        = H.refl
    id-↑⁺ (Γ⁺ ▻ σ) = begin
      P.subst (λ ρ′ → _ ++ Γ⁺ ▻ σ ⇨ _ ++ Γ⁺ /⁺ id ▻ σ /̂ ρ′)
              (P.sym $ id ↑⁺-lemma Γ⁺)
              ((id ↑⁺ Γ⁺) ↑)                                ≅⟨ H.≡-subst-removable (λ ρ′ → _ ++ Γ⁺ ▻ σ ⇨ _ ++ Γ⁺ /⁺ id ▻ σ /̂ ρ′)
                                                                                   (P.sym $ id ↑⁺-lemma Γ⁺) _ ⟩
      (id ↑⁺ Γ⁺) ↑                                          ≅⟨ ↑-cong P.refl (P.refl ++-cong H.≡-to-≅ (/⁺-id Γ⁺)) (id-↑⁺ Γ⁺) H.refl ⟩
      id ↑                                                  ≅⟨ H.sym $ H.≡-subst-removable (λ ρ → _ ++ Γ⁺ ▻ σ ⇨ _ ++ Γ⁺ ▻ σ /̂ ρ)
                                                                                           (P.sym $ id-lemma (_ ++ Γ⁺)) _ ⟩
      P.subst (λ ρ → _ ++ Γ⁺ ▻ σ ⇨ _ ++ Γ⁺ ▻ σ /̂ ρ)
              (P.sym $ id-lemma (_ ++ Γ⁺))
              (id ↑)                                        ∎
      where open H.≅-Reasoning
