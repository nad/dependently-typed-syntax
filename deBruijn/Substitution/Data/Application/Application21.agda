------------------------------------------------------------------------
-- Lemmas related to application of substitutions
------------------------------------------------------------------------

-- The record below allows the application operation to be
-- "heterogeneous", applying substitutions containing one kind of term
-- to another kind of term. TODO: This results in some extra
-- complication—is it worth it?

{-# OPTIONS --universe-polymorphism #-}

open import Universe
open import deBruijn.Substitution.Data.Simple
import deBruijn.TermLike as TermLike

module deBruijn.Substitution.Data.Application.Application21
  {u e} {Uni : Universe u e} where

import deBruijn.Context as Context
open import deBruijn.Substitution.Data.Application.Application
open import deBruijn.Substitution.Data.Basics
open import deBruijn.Substitution.Data.Map
open import Function using (_$_)
open import Level using (_⊔_)
open import Relation.Binary.HeterogeneousEquality as H using (_≅_)
open import Relation.Binary.PropositionalEquality as P using (_≡_)

open Context Uni
open TermLike Uni

-- Lemmas and definitions related to application.

record Application₂₁
  {t₁} {T₁ : Term-like t₁}
  {t₂} {T₂ : Term-like t₂}

  -- Simple substitutions for the first kind of terms.
  (simple₁ : Simple T₁)

  -- Simple substitutions for the second kind of terms.
  (simple₂ : Simple T₂)

  -- A translation from the first to the second kind of terms.
  (trans : [ T₁ ⟶⁼ T₂ ])
  : Set (u ⊔ e ⊔ t₁ ⊔ t₂) where

  open Term-like T₁ renaming (_⊢_ to _⊢₁_)
  open Term-like T₂ renaming (_⊢_ to _⊢₂_)
  open Simple simple₁
    using ()
    renaming ( id to id₁; sub to sub₁; var to var₁
             ; weaken to weaken₁; wk to wk₁; wk-subst to wk-subst₁
             ; _↑ to _↑₁; _↑⁺_ to _↑⁺₁_; _↑⋆ to _↑⋆₁; _↑⁺⋆_ to _↑⁺⋆₁_
             )
  open Simple simple₂
    using ()
    renaming ( id to id₂; var to var₂
             ; weaken to weaken₂; wk to wk₂; wk-subst to wk-subst₂
             ; _↑ to _↑₂
             )

  field
    application : Application T₁ T₂

  open Application application

  field
    -- The two weakening functions coincide.
    trans-weaken : ∀ {Γ σ τ} (t : Γ ⊢₁ τ) →
                   trans · (weaken₁ · t) ≡
                   weaken₂ {σ = σ} · (trans · t)

    -- The two variable inclusion functions coincide.
    trans-var : ∀ {Γ σ} (x : Γ ∋ σ) → trans · (var₁ · x) ≡ var₂ · x

    -- _/⊢_ and _/∋₁_ coincide for variables.
    var-/⊢ : ∀ {Γ Δ σ} {ρ̂ : Γ ⇨̂ Δ} (x : Γ ∋ σ) (ρ : Sub T₁ ρ̂) →
             var₂ · x /⊢ ρ ≡ trans · (x /∋ ρ)

  -- Application of multiple substitutions to variables.
  --
  -- TODO: Remove?

  app∋⋆ : ∀ {Γ Δ} {ρ̂ : Γ ⇨̂ Δ} → Subs T₁ ρ̂ → [ Var ⟶ T₂ ] ρ̂
  app∋⋆ ε        = var₂
  app∋⋆ (ε ▻ ρ)  = trans [∘] app∋ ρ
  app∋⋆ (ρs ▻ ρ) = app ρ [∘] app∋⋆ ρs

  infixl 8 _/∋⋆_

  _/∋⋆_ : ∀ {Γ Δ σ} {ρ̂ : Γ ⇨̂ Δ} → Γ ∋ σ → Subs T₁ ρ̂ → Δ ⊢₂ σ /̂ ρ̂
  x /∋⋆ ρs = app∋⋆ ρs · x

  -- Composition of multiple substitutions.
  --
  -- TODO: Remove?

  ∘⋆ : ∀ {Γ Δ} {ρ̂ : Γ ⇨̂ Δ} → Subs T₁ ρ̂ → Sub T₂ ρ̂
  ∘⋆ ε        = id₂
  ∘⋆ (ρs ▻ ρ) = ∘⋆ ρs ∘ ρ

  -- Some congruence lemmas.

  trans-cong : ∀ {Γ₁ σ₁} {t₁ : Γ₁ ⊢₁ σ₁}
                 {Γ₂ σ₂} {t₂ : Γ₂ ⊢₁ σ₂} →
               Γ₁ ≡ Γ₂ → σ₁ ≅ σ₂ → t₁ ≅ t₂ →
               trans · t₁ ≅ trans · t₂
  trans-cong P.refl H.refl H.refl = H.refl

  app∋⋆-cong : ∀ {Γ₁ Δ₁} {ρ̂₁ : Γ₁ ⇨̂ Δ₁} {ρs₁ : Subs T₁ ρ̂₁}
                 {Γ₂ Δ₂} {ρ̂₂ : Γ₂ ⇨̂ Δ₂} {ρs₂ : Subs T₁ ρ̂₂} →
               Γ₁ ≡ Γ₂ → Δ₁ ≡ Δ₂ → ρ̂₁ ≅ ρ̂₂ → ρs₁ ≅ ρs₂ →
               app∋⋆ ρs₁ ≅ app∋⋆ ρs₂
  app∋⋆-cong P.refl P.refl H.refl H.refl = H.refl

  /∋⋆-cong :
    ∀ {Γ₁ Δ₁ σ₁} {x₁ : Γ₁ ∋ σ₁} {ρ̂₁ : Γ₁ ⇨̂ Δ₁} {ρs₁ : Subs T₁ ρ̂₁}
      {Γ₂ Δ₂ σ₂} {x₂ : Γ₂ ∋ σ₂} {ρ̂₂ : Γ₂ ⇨̂ Δ₂} {ρs₂ : Subs T₁ ρ̂₂} →
    Γ₁ ≡ Γ₂ → Δ₁ ≡ Δ₂ → σ₁ ≅ σ₂ → x₁ ≅ x₂ → ρ̂₁ ≅ ρ̂₂ → ρs₁ ≅ ρs₂ →
    x₁ /∋⋆ ρs₁ ≅ x₂ /∋⋆ ρs₂
  /∋⋆-cong P.refl P.refl H.refl H.refl H.refl H.refl = H.refl

  ∘⋆-cong : ∀ {Γ₁ Δ₁} {ρ̂₁ : Γ₁ ⇨̂ Δ₁} {ρs₁ : Subs T₁ ρ̂₁}
              {Γ₂ Δ₂} {ρ̂₂ : Γ₂ ⇨̂ Δ₂} {ρs₂ : Subs T₁ ρ̂₂} →
            Γ₁ ≡ Γ₂ → Δ₁ ≡ Δ₂ → ρ̂₁ ≅ ρ̂₂ → ρs₁ ≅ ρs₂ → ∘⋆ ρs₁ ≅ ∘⋆ ρs₂
  ∘⋆-cong P.refl P.refl H.refl H.refl = H.refl

  abstract

    -- Applying a composed substitution to a variable is equivalent to
    -- applying all the substitutions one after another.
    --
    -- TODO: Remove this lemma?

    /∋-∘⋆ : ∀ {Γ Δ σ} {ρ̂ : Γ ⇨̂ Δ} (x : Γ ∋ σ) (ρs : Subs T₁ ρ̂) →
            x /∋ ∘⋆ ρs ≡ var₂ · x /⊢⋆ ρs
    /∋-∘⋆ x ε = begin
      x /∋ id₂  ≡⟨ Simple./∋-id simple₂ x ⟩
      var₂ · x  ∎
      where open P.≡-Reasoning
    /∋-∘⋆ x (ρs ▻ ρ) = begin
      x /∋ ∘⋆ ρs ∘ ρ        ≡⟨ /∋-∘ x (∘⋆ ρs) ρ ⟩
      x /∋ ∘⋆ ρs /⊢ ρ       ≅⟨ /⊢-cong P.refl P.refl H.refl (H.≡-to-≅ $ /∋-∘⋆ x ρs) H.refl H.refl ⟩
      var₂ · x /⊢⋆ ρs /⊢ ρ  ∎
      where open P.≡-Reasoning

    -- x /∋⋆ ρs is synonymous with var₂ · x /⊢⋆ ρs.
    --
    -- TODO: Remove?

    var-/⊢⋆ : ∀ {Γ Δ σ} {ρ̂ : Γ ⇨̂ Δ} (x : Γ ∋ σ) (ρs : Subs T₁ ρ̂) →
              var₂ · x /⊢⋆ ρs ≡ x /∋⋆ ρs
    var-/⊢⋆ x ε       = P.refl
    var-/⊢⋆ x (ε ▻ ρ) = begin
      var₂ · x /⊢ ρ     ≡⟨ var-/⊢ x ρ ⟩
      trans · (x /∋ ρ)  ∎
      where open P.≡-Reasoning
    var-/⊢⋆ x (ρs ▻ ρ₁ ▻ ρ₂) = begin
      var₂ · x /⊢⋆ (ρs ▻ ρ₁) /⊢ ρ₂  ≅⟨ /⊢-cong P.refl P.refl H.refl
                                               (H.≡-to-≅ $ var-/⊢⋆ x (ρs ▻ ρ₁))
                                               H.refl H.refl ⟩
      x /∋⋆ (ρs ▻ ρ₁) /⊢ ρ₂         ∎
      where open P.≡-Reasoning

    -- A helper lemma.

    /∋-≡-var : ∀ {Γ Δ σ} {ρ̂ : Γ ⇨̂ Δ}
               (x : Γ ∋ σ) (ρ : Sub T₁ ρ̂) {y} →
               x /∋ ρ ≡ var₁ · y → var₂ · x /⊢ ρ ≡ var₂ · y
    /∋-≡-var x ρ {y} hyp = begin
      var₂ · x /⊢ ρ       ≡⟨ var-/⊢ x ρ ⟩
      trans · (x /∋ ρ)    ≅⟨ trans-cong P.refl H.refl (H.≡-to-≅ hyp) ⟩
      trans · (var₁ · y)  ≡⟨ trans-var y ⟩
      var₂ · y            ∎
      where open P.≡-Reasoning

    -- A variant of /∋-id.

    var-/⊢-id : ∀ {Γ σ} (x : Γ ∋ σ) → var₂ · x /⊢ id₁ ≡ var₂ · x
    var-/⊢-id x = /∋-≡-var x id₁ (Simple./∋-id simple₁ x)

    -- A variant of /∋-wk-↑⁺.

    var-/⊢-wk-↑⁺ : ∀ {Γ σ} Γ⁺ {τ} (x : Γ ++ Γ⁺ ∋ τ) →
                   var₂ · x /⊢ wk₁ {σ = σ} ↑⁺₁ Γ⁺ ≡
                   var₂ · (lift weaken∋ Γ⁺ · x)
    var-/⊢-wk-↑⁺ Γ⁺ x =
      /∋-≡-var x (wk₁ ↑⁺₁ Γ⁺) (Simple./∋-wk-↑⁺ simple₁ Γ⁺ x)

    -- A variant of /∋-wk-↑⁺-↑⁺.

    var-/⊢-wk-↑⁺-↑⁺ : ∀ {Γ σ} Γ⁺ Γ⁺⁺ {τ} (x : Γ ++ Γ⁺ ++ Γ⁺⁺ ∋ τ) →
                      var₂ · x /⊢ wk₁ {σ = σ} ↑⁺₁ Γ⁺ ↑⁺₁ Γ⁺⁺ ≡
                      var₂ · (lift (lift weaken∋ Γ⁺) Γ⁺⁺ · x)
    var-/⊢-wk-↑⁺-↑⁺ Γ⁺ Γ⁺⁺ x =
      /∋-≡-var x (wk₁ ↑⁺₁ Γ⁺ ↑⁺₁ Γ⁺⁺)
               (Simple./∋-wk-↑⁺-↑⁺ simple₁ Γ⁺ Γ⁺⁺ x)

    -- Variants of zero-/∋-↑.

    zero-/⊢-↑ : ∀ {Γ Δ} {ρ̂ : Γ ⇨̂ Δ} σ (ρ : Sub T₁ ρ̂) →
                var₂ · zero /⊢ _↑₁ {σ = σ} ρ ≡ var₂ · zero
    zero-/⊢-↑ σ ρ =
      /∋-≡-var zero (_↑₁ {σ = σ} ρ) (Simple.zero-/∋-↑ simple₁ σ ρ)

    zero-/⊢⋆-↑⋆ : ∀ {Γ Δ} {ρ̂ : Γ ⇨̂ Δ} σ (ρs : Subs T₁ ρ̂) →
                  var₂ · zero /⊢⋆ _↑⋆₁ {σ = σ} ρs ≡ var₂ · zero
    zero-/⊢⋆-↑⋆ σ ε        = P.refl
    zero-/⊢⋆-↑⋆ σ (ρs ▻ ρ) = begin
      var₂ · zero /⊢⋆ _↑⋆₁ {σ = σ} ρs /⊢ ρ ↑₁  ≅⟨ /⊢-cong P.refl P.refl H.refl (H.≡-to-≅ $ zero-/⊢⋆-↑⋆ σ ρs) H.refl
                                                          (H.refl {x = _↑₁ {σ = σ /⋆ ρs} ρ}) ⟩
      var₂ · zero /⊢ _↑₁ {σ = σ /⋆ ρs} ρ       ≡⟨ zero-/⊢-↑ (σ /⋆ ρs) ρ ⟩
      var₂ · zero                              ∎
      where open P.≡-Reasoning

    -- A corollary of ε-↑⁺⋆.

    /⊢⋆-ε-↑⁺⋆ : ∀ {Γ} Γ⁺ {σ} (t : Γ ++ Γ⁺ ⊢₂ σ) →
                t /⊢⋆ ε ↑⁺⋆₁ Γ⁺ ≅ t
    /⊢⋆-ε-↑⁺⋆ Γ⁺ t = begin
      t /⊢⋆ ε ↑⁺⋆₁ Γ⁺  ≅⟨ /⊢⋆-cong P.refl (++-cong P.refl (H.≡-to-≅ $ /̂⁺-îd Γ⁺))
                                   H.refl (H.refl {x = t}) (îd-↑̂⁺ Γ⁺)
                                   (Simple.ε-↑⁺⋆ simple₁ Γ⁺) ⟩
      t /⊢⋆ ε          ≡⟨ P.refl ⟩
      t                ∎
      where open H.≅-Reasoning

    -- A corollary of ▻-↑⁺⋆.

    /⊢⋆-▻-↑⁺⋆ :
      ∀ {Γ Δ Ε} {ρ̂₁ : Γ ⇨̂ Δ} {ρ̂₂ : Δ ⇨̂ Ε} Γ⁺ {σ}
      (t : Γ ++ Γ⁺ ⊢₂ σ) (ρs : Subs T₁ ρ̂₁) (ρ : Sub T₁ ρ̂₂) →
      t /⊢⋆ (ρs ▻ ρ) ↑⁺⋆₁ Γ⁺ ≅ t /⊢⋆ ρs ↑⁺⋆₁ Γ⁺ /⊢ ρ ↑⁺₁ (Γ⁺ /⁺⋆ ρs)
    /⊢⋆-▻-↑⁺⋆ Γ⁺ t ρs ρ =
      /⊢⋆-cong
        P.refl (++-cong P.refl (H.≡-to-≅ $ /̂⁺-∘̂ Γ⁺ ⟦ ρs ⟧⇨⋆ ⟦ ρ ⟧⇨))
        H.refl (H.refl {x = t})
        (∘̂-↑̂⁺ ⟦ ρs ⟧⇨⋆ ⟦ ρ ⟧⇨ Γ⁺) (Simple.▻-↑⁺⋆ simple₁ ρs ρ Γ⁺)

    -- A corollary of ε-↑⁺⋆ and ▻-↑⁺⋆.

    /⊢⋆-ε-▻-↑⁺⋆ : ∀ {Γ Δ} {ρ̂ : Γ ⇨̂ Δ} Γ⁺ {σ}
                  (t : Γ ++ Γ⁺ ⊢₂ σ) (ρ : Sub T₁ ρ̂) →
                  t /⊢⋆ (ε ▻ ρ) ↑⁺⋆₁ Γ⁺ ≡ t /⊢ ρ ↑⁺₁ Γ⁺
    /⊢⋆-ε-▻-↑⁺⋆ Γ⁺ t ρ =
      let lemma₁ = ++-cong P.refl (H.≡-to-≅ $ /̂⁺-∘̂ Γ⁺ îd ⟦ ρ ⟧⇨)
          lemma₂ = ++-cong P.refl (H.≡-to-≅ $ /̂⁺-îd Γ⁺)
      in H.≅-to-≡ (begin
      t /⊢⋆ (ε ▻ ρ) ↑⁺⋆₁ Γ⁺                ≅⟨ /⊢⋆-cong P.refl lemma₁ H.refl (H.refl {x = t}) (∘̂-↑̂⁺ îd ⟦ ρ ⟧⇨ Γ⁺)
                                                       (Simple.▻-↑⁺⋆ simple₁ ε ρ Γ⁺) ⟩
      t /⊢⋆ ε ↑⁺⋆₁ Γ⁺ /⊢ ρ ↑⁺₁ (Γ⁺ /̂⁺ îd)  ≅⟨ /⊢-cong lemma₂ (P.sym lemma₁)
                                                      (/̂-cong P.refl lemma₂ H.refl (îd-↑̂⁺ Γ⁺))
                                                      (/⊢⋆-ε-↑⁺⋆ Γ⁺ t)
                                                      (↑̂⁺-cong P.refl P.refl H.refl (H.≡-to-≅ $ /̂⁺-îd Γ⁺))
                                                      (Simple.↑⁺-cong simple₁ P.refl P.refl H.refl H.refl
                                                                      (H.≡-to-≅ $ /̂⁺-îd Γ⁺)) ⟩
      t               /⊢ ρ ↑⁺₁ Γ⁺          ∎)
      where open H.≅-Reasoning

    -- Another corollary of ε-↑⁺⋆ and ▻-↑⁺⋆.

    /⊢⋆-ε-▻-▻-↑⁺⋆ :
      ∀ {Γ Δ Ε} {ρ̂₁ : Γ ⇨̂ Δ} {ρ̂₂ : Δ ⇨̂ Ε} Γ⁺ {σ}
      (t : Γ ++ Γ⁺ ⊢₂ σ) (ρ₁ : Sub T₁ ρ̂₁) (ρ₂ : Sub T₁ ρ̂₂) →
      t /⊢⋆ (ε ▻ ρ₁ ▻ ρ₂) ↑⁺⋆₁ Γ⁺ ≅ t /⊢ ρ₁ ↑⁺₁ Γ⁺ /⊢ ρ₂ ↑⁺₁ (Γ⁺ /⁺ ρ₁)
    /⊢⋆-ε-▻-▻-↑⁺⋆ Γ⁺ t ρ₁ ρ₂ = begin
      t /⊢⋆ (ε ▻ ρ₁ ▻ ρ₂) ↑⁺⋆₁ Γ⁺                  ≅⟨ /⊢⋆-cong P.refl (++-cong P.refl (H.≡-to-≅ $ /̂⁺-∘̂ Γ⁺ ⟦ ρ₁ ⟧⇨ ⟦ ρ₂ ⟧⇨))
                                                               H.refl (H.refl {x = t}) (∘̂-↑̂⁺ ⟦ ρ₁ ⟧⇨ ⟦ ρ₂ ⟧⇨ Γ⁺)
                                                               (Simple.▻-↑⁺⋆ simple₁ (ε ▻ ρ₁) ρ₂ Γ⁺) ⟩
      t /⊢⋆ (ε ▻ ρ₁) ↑⁺⋆₁ Γ⁺ /⊢ ρ₂ ↑⁺₁ (Γ⁺ /⁺ ρ₁)  ≅⟨ /⊢-cong P.refl P.refl H.refl (H.≡-to-≅ $ /⊢⋆-ε-▻-↑⁺⋆ Γ⁺ t ρ₁)
                                                              H.refl H.refl ⟩
      t /⊢ ρ₁ ↑⁺₁ Γ⁺ /⊢ ρ₂ ↑⁺₁ (Γ⁺ /⁺ ρ₁)          ∎
      where open H.≅-Reasoning

    -- Application of sub cancels one occurrence of suc.

    suc-/⊢-sub : ∀ {Γ σ τ} (x : Γ ∋ σ) (t : Γ ⊢₁ τ) →
                 var₂ · suc x /⊢ sub₁ t ≡ var₂ · x
    suc-/⊢-sub x t = begin
      var₂ · suc x /⊢ sub₁ t     ≡⟨ var-/⊢ (suc x) (sub₁ t) ⟩
      trans · (suc x /∋ sub₁ t)  ≡⟨ P.refl ⟩
      trans · (x /∋ id₁)         ≅⟨ trans-cong P.refl H.refl
                                      (H.≡-to-≅ $ Simple./∋-id simple₁ x) ⟩
      trans · (var₁ · x)         ≡⟨ trans-var x ⟩
      var₂ · x                   ∎
      where open P.≡-Reasoning

    -- First weakening and then substituting something for the first
    -- variable is equivalent to doing nothing.

    wk-∘-sub : ∀ {Γ σ} (t : Γ ⊢₁ σ) → wk₂ ∘ sub₁ t ≡ id₂
    wk-∘-sub t = H.≅-to-≡ $ extensionality P.refl H.refl λ x → begin
      x /∋ wk₂ ∘ sub₁ t       ≡⟨ /∋-∘ x wk₂ (sub₁ t) ⟩
      x /∋ wk₂ /⊢ sub₁ t      ≅⟨ /⊢-cong P.refl P.refl H.refl
                                         (H.≡-to-≅ $ Simple./∋-wk simple₂ x)
                                         H.refl H.refl ⟩
      var₂ · suc x /⊢ sub₁ t  ≡⟨ suc-/⊢-sub x t ⟩
      var₂ · x                ≡⟨ P.sym $ Simple./∋-id simple₂ x ⟩
      x /∋ id₂                ∎
      where open H.≅-Reasoning

    -- id is a left identity of _∘_ (more or less).

    id-∘ : ∀ {Γ Δ} {ρ̂ : Γ ⇨̂ Δ} (ρ : Sub T₁ ρ̂) → id₂ ∘ ρ ≡ map trans ρ
    id-∘ ρ = H.≅-to-≡ $
      extensionality P.refl H.refl λ x → begin
        x /∋ id₂ ∘ ρ      ≡⟨ /∋-∘ x id₂ ρ ⟩
        x /∋ id₂ /⊢ ρ     ≅⟨ /⊢-cong P.refl P.refl H.refl
                                     (H.≡-to-≅ $ Simple./∋-id simple₂ x)
                                     H.refl (H.refl {x = ρ}) ⟩
        var₂ · x /⊢ ρ     ≡⟨ var-/⊢ x ρ ⟩
        trans · (x /∋ ρ)  ≡⟨ P.sym $ /∋-map x trans ρ ⟩
        x /∋ map trans ρ  ∎
      where open H.≅-Reasoning

    -- One can translate a substitution either before or after
    -- weakening it.

    map-trans-wk-subst :
      ∀ {Γ Δ σ} {ρ̂ : Γ ⇨̂ Δ} (ρ : Sub T₁ ρ̂) →
      map trans (wk-subst₁ {σ = σ} ρ) ≡ wk-subst₂ (map trans ρ)
    map-trans-wk-subst {σ = σ} ρ = begin
      map trans (wk-subst₁ {σ = σ} ρ)    ≡⟨ P.sym $ map-[∘] trans (weaken₁ {σ = σ}) ρ ⟩
      map (trans [∘] weaken₁ {σ = σ}) ρ  ≅⟨ map-cong-ext₁ P.refl P.refl H.refl H.refl
                                                          (λ t → H.≡-to-≅ $ trans-weaken t)
                                                          (H.refl {x = ρ}) ⟩
      map (weaken₂ [∘] trans) ρ          ≡⟨ map-[∘] weaken₂ trans ρ ⟩
      wk-subst₂ (map trans ρ)            ∎
      where open P.≡-Reasoning

    -- One can translate a substitution either before or after lifting
    -- it.

    map-trans-↑ : ∀ {Γ Δ σ} {ρ̂ : Γ ⇨̂ Δ} (ρ : Sub T₁ ρ̂) →
                  map trans (_↑₁ {σ = σ} ρ) ≡ map trans ρ ↑₂
    map-trans-↑ {σ = σ} ρ = H.≅-to-≡ (begin
      map trans (_↑₁ {σ = σ} ρ)                                    ≅⟨ map-cong P.refl P.refl P.refl
                                                                               (▻̂-cong P.refl P.refl H.refl H.refl
                                                                                       (H.≡-to-≅ $ corresponds var₁ zero))
                                                                               H.refl (H.refl {x = trans})
                                                                               (Simple.unfold-↑ simple₁ ρ) ⟩
      map trans (wk-subst₁ {σ = σ / ρ} ρ ▻ var₁ · zero)            ≅⟨ map-▻ trans (wk-subst₁ ρ) _ ⟩
      map trans (wk-subst₁ {σ = σ / ρ} ρ) ▻ trans · (var₁ · zero)  ≅⟨ ▻⇨-cong P.refl P.refl H.refl H.refl
                                                                              (H.≡-to-≅ $ map-trans-wk-subst ρ)
                                                                              (H.≡-to-≅ $ trans-var zero) ⟩
      wk-subst₂ (map trans ρ) ▻ var₂ · zero                        ≅⟨ H.sym $ Simple.unfold-↑ simple₂ (map trans ρ) ⟩
      map trans ρ ↑₂                                               ∎)
      where open H.≅-Reasoning

  open Application application public
