------------------------------------------------------------------------
-- Lemmas related to application of substitutions
------------------------------------------------------------------------

{-# OPTIONS --universe-polymorphism #-}

open import Universe

module deBruijn.Substitution.Data.Application.Application222
  {u e} {Uni : Universe u e}
  where

import deBruijn.Context as Context
open import deBruijn.Substitution.Data.Application.Application221
open import deBruijn.Substitution.Data.Basics
open import deBruijn.Substitution.Data.Map
open import deBruijn.Substitution.Data.Simple
import deBruijn.TermLike as TermLike
open import Function using (_$_)
open import Level using (_⊔_)
open import Relation.Binary.HeterogeneousEquality as H using (_≅_)
open import Relation.Binary.PropositionalEquality as P using (_≡_)

open Context Uni
open TermLike Uni

-- Lemmas related to application.

record Application₂₂₂
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
    renaming ( id to id₁; sub to sub₁; var to var₁; wk to wk₁
             ; _↑ to _↑₁; _↑⁺_ to _↑⁺₁_; _↑⋆ to _↑⋆₁; _↑⁺⋆_ to _↑⁺⋆₁_
             )
  open Simple simple₂
    using ()
    renaming ( var to var₂
             ; weaken to weaken₂; wk-subst to wk-subst₂
             ; _↑ to _↑₂; _↑⁺_ to _↑⁺₂_
             )

  field
    application₂₂₁ : Application₂₂₁ simple₁ simple₂ trans

  open Application₂₂₁ application₂₂₁ public

  abstract

    -- A variant of suc-/∋-↑.

    suc-/⊢⋆-↑⋆ :
      ∀ {Γ Δ} {ρ̂ : Γ ⇨̂ Δ}
      σ {τ} (x : Γ ∋ τ) (ρs : Subs T₁ ρ̂) →
      var₂ · suc {σ = σ} x /⊢⋆ ρs ↑⋆₁ ≡ var₂ · x /⊢⋆ (ρs ▻ wk₁)
    suc-/⊢⋆-↑⋆ σ x ε = begin
      var₂ · suc x     ≡⟨ P.sym $ var-/⊢-wk-↑⁺ ε x ⟩
      var₂ · x /⊢ wk₁  ∎
      where open P.≡-Reasoning
    suc-/⊢⋆-↑⋆ σ x (ρs ▻ ρ) = begin
      var₂ · suc {σ = σ} x /⊢⋆ ρs ↑⋆₁ /⊢ ρ ↑₁       ≅⟨ /⊢-cong P.refl P.refl H.refl
                                                               (H.≡-to-≅ $ suc-/⊢⋆-↑⋆ σ x ρs)
                                                               H.refl (H.refl {x = ρ ↑₁}) ⟩
      var₂ · x /⊢⋆ ρs /⊢ wk₁ {σ = σ /⋆ ρs} /⊢ ρ ↑₁  ≡⟨ P.sym $ /⊢-/⊢-wk (σ /⋆ ρs) (var₂ · x /⊢⋆ ρs) ρ ⟩
      var₂ · x /⊢⋆ ρs /⊢ ρ /⊢ wk₁                   ∎
      where open P.≡-Reasoning

    -- The antecedent of var-/⊢⋆-↑⁺⋆-⇒-/⊢⋆-↑⁺⋆ follows from a less
    -- complicated statement.

    var-/⊢⋆-⇒-var-/⊢⋆-↑⁺⋆ :
      ∀ {Γ Δ} {ρ̂ : Γ ⇨̂ Δ} {ρs₁ : Subs T₁ ρ̂} {ρs₂ : Subs T₁ ρ̂} →
      (∀ {σ} (x : Γ ∋ σ) → var₂ · x /⊢⋆ ρs₁ ≡ var₂ · x /⊢⋆ ρs₂) →
      ∀ Γ⁺ {σ} (x : Γ ++ Γ⁺ ∋ σ) →
      var₂ · x /⊢⋆ ρs₁ ↑⁺⋆₁ Γ⁺ ≡ var₂ · x /⊢⋆ ρs₂ ↑⁺⋆₁ Γ⁺
    var-/⊢⋆-⇒-var-/⊢⋆-↑⁺⋆                   hyp ε        x    = hyp x
    var-/⊢⋆-⇒-var-/⊢⋆-↑⁺⋆ {ρs₁ = ρs₁} {ρs₂} hyp (Γ⁺ ▻ σ) zero = begin
      var₂ · zero /⊢⋆ ρs₁ ↑⁺⋆₁ (Γ⁺ ▻ σ)  ≡⟨ zero-/⊢⋆-↑⋆ σ (ρs₁ ↑⁺⋆₁ Γ⁺) ⟩
      var₂ · zero                        ≡⟨ P.sym $ zero-/⊢⋆-↑⋆ σ (ρs₂ ↑⁺⋆₁ Γ⁺) ⟩
      var₂ · zero /⊢⋆ ρs₂ ↑⁺⋆₁ (Γ⁺ ▻ σ)  ∎
      where open P.≡-Reasoning
    var-/⊢⋆-⇒-var-/⊢⋆-↑⁺⋆ {ρs₁ = ρs₁} {ρs₂} hyp (Γ⁺ ▻ σ) (suc x) = begin
      var₂ · suc x /⊢⋆ ρs₁ ↑⁺⋆₁ (Γ⁺ ▻ σ)   ≡⟨ suc-/⊢⋆-↑⋆ σ x (ρs₁ ↑⁺⋆₁ Γ⁺) ⟩
      var₂ · x     /⊢⋆ ρs₁ ↑⁺⋆₁ Γ⁺ /⊢ wk₁  ≅⟨ /⊢-cong P.refl P.refl H.refl
                                                      (H.≡-to-≅ $ var-/⊢⋆-⇒-var-/⊢⋆-↑⁺⋆ hyp Γ⁺ x)
                                                      H.refl (H.refl {x = wk₁}) ⟩
      var₂ · x     /⊢⋆ ρs₂ ↑⁺⋆₁ Γ⁺ /⊢ wk₁  ≡⟨ P.sym $ suc-/⊢⋆-↑⋆ σ x (ρs₂ ↑⁺⋆₁ Γ⁺) ⟩
      var₂ · suc x /⊢⋆ ρs₂ ↑⁺⋆₁ (Γ⁺ ▻ σ)   ∎
      where open P.≡-Reasoning

    -- Variants of var-/⊢⋆-↑⁺⋆-⇒-/⊢⋆-↑⁺⋆ which may be easier to use.

    var-/⊢⋆-⇒-/⊢⋆-↑⁺⋆ :
      ∀ {Γ Δ} {ρ̂ : Γ ⇨̂ Δ} (ρs₁ : Subs T₁ ρ̂) (ρs₂ : Subs T₁ ρ̂) →
      (∀ {σ} (x : Γ ∋ σ) → var₂ · x /⊢⋆ ρs₁ ≡ var₂ · x /⊢⋆ ρs₂) →
      ∀ Γ⁺ {σ} (t : Γ ++ Γ⁺ ⊢₂ σ) →
      t /⊢⋆ ρs₁ ↑⁺⋆₁ Γ⁺ ≡ t /⊢⋆ ρs₂ ↑⁺⋆₁ Γ⁺
    var-/⊢⋆-⇒-/⊢⋆-↑⁺⋆ ρs₁ ρs₂ hyp =
      var-/⊢⋆-↑⁺⋆-⇒-/⊢⋆-↑⁺⋆ ρs₁ ρs₂ (var-/⊢⋆-⇒-var-/⊢⋆-↑⁺⋆ hyp)

    var-/⊢⋆-⇒-/⊢⋆ :
      ∀ {Γ Δ} {ρ̂ : Γ ⇨̂ Δ} (ρs₁ : Subs T₁ ρ̂) (ρs₂ : Subs T₁ ρ̂) →
      (∀ {σ} (x : Γ ∋ σ) → var₂ · x /⊢⋆ ρs₁ ≡ var₂ · x /⊢⋆ ρs₂) →
      ∀ {σ} (t : Γ ⊢₂ σ) → t /⊢⋆ ρs₁ ≡ t /⊢⋆ ρs₂
    var-/⊢⋆-⇒-/⊢⋆ ρs₁ ρs₂ hyp = var-/⊢⋆-⇒-/⊢⋆-↑⁺⋆ ρs₁ ρs₂ hyp ε

    -- The identity substitution has no effect.

    /⊢-id : ∀ {Γ σ} (t : Γ ⊢₂ σ) → t /⊢ id₁ ≡ t
    /⊢-id = var-/⊢⋆-⇒-/⊢⋆ (ε ▻ id₁) ε var-/⊢-id

    -- id is a right identity of _∘_.

    ∘-id : ∀ {Γ Δ} {ρ̂ : Γ ⇨̂ Δ} (ρ : Sub T₂ ρ̂) → ρ ∘ id₁ ≡ ρ
    ∘-id ρ = H.≅-to-≡ $
      extensionality P.refl H.refl λ x → begin
        x /∋ ρ ∘ id₁   ≡⟨ /∋-∘ x ρ id₁ ⟩
        x /∋ ρ /⊢ id₁  ≡⟨ /⊢-id (x /∋ ρ) ⟩
        x /∋ ρ         ∎
      where open H.≅-Reasoning

    -- Lifting distributes over composition.

    ∘-↑ : ∀ {Γ Δ Ε} σ {ρ̂₁ : Γ ⇨̂ Δ} {ρ̂₂ : Δ ⇨̂ Ε}
          (ρ₁ : Sub T₂ ρ̂₁) (ρ₂ : Sub T₁ ρ̂₂) →
          _↑₂ {σ = σ} (ρ₁ ∘ ρ₂) ≡ ρ₁ ↑₂ ∘ ρ₂ ↑₁
    ∘-↑ σ ρ₁ ρ₂ =
      let ρ₂↑ = _↑₁ {σ = σ / ρ₁} ρ₂

          lemma₁ = begin
            wk-subst₂ (ρ₁ ∘ ρ₂)               ≡⟨ P.refl ⟩
            map weaken₂ (map (app ρ₂) ρ₁)     ≡⟨ P.sym $ map-[∘] weaken₂ (app ρ₂) ρ₁ ⟩
            map (weaken₂ [∘] app ρ₂) ρ₁       ≅⟨ map-cong-ext₁ P.refl P.refl H.refl H.refl
                                                   (λ t → begin
                                                      weaken₂ · (t /⊢ ρ₂)  ≡⟨ P.sym $ /⊢-wk (t /⊢ ρ₂) ⟩
                                                      t /⊢ ρ₂ /⊢ wk₁       ≡⟨ /⊢-/⊢-wk (σ / ρ₁) t ρ₂ ⟩
                                                      t /⊢ wk₁ /⊢ ρ₂↑      ≅⟨ /⊢-cong P.refl P.refl H.refl
                                                                                      (H.≡-to-≅ $ /⊢-wk t)
                                                                                      H.refl H.refl ⟩
                                                      weaken₂ · t /⊢ ρ₂↑   ∎)
                                                   (H.refl {x = ρ₁}) ⟩
            map (app ρ₂↑ [∘] weaken₂) ρ₁      ≡⟨ map-[∘] (app ρ₂↑) weaken₂ ρ₁ ⟩
            map (app ρ₂↑) (map (weaken₂) ρ₁)  ∎

          lemma₂ = begin
            var₂ · zero            ≡⟨ P.sym $ trans-var zero ⟩
            trans · (var₁ · zero)  ≅⟨ trans-cong P.refl H.refl
                                        (H.≡-to-≅ $ P.sym $ Simple.zero-/∋-↑ simple₁ (σ / ρ₁) ρ₂) ⟩
            trans · (zero /∋ ρ₂↑)  ≡⟨ P.sym $ var-/⊢ zero ρ₂↑ ⟩
            var₂ · zero /⊢ ρ₂↑     ∎

      in H.≅-to-≡ (begin
      (ρ₁ ∘ ρ₂) ↑₂                                             ≅⟨ Simple.unfold-↑ simple₂ (ρ₁ ∘ ρ₂) ⟩
      wk-subst₂ (ρ₁ ∘ ρ₂) ▻ var₂ · zero                        ≅⟨ ▻⇨-cong P.refl P.refl H.refl H.refl lemma₁ lemma₂ ⟩
      map (app ρ₂↑) (map (weaken₂ {σ = σ / ρ₁}) ρ₁) ▻
        var₂ · zero /⊢ ρ₂↑                                     ≅⟨ H.sym $ map-▻ (app ρ₂↑) (wk-subst₂ {σ = σ / ρ₁} ρ₁) (var₂ · zero) ⟩
      map (app ρ₂↑) (wk-subst₂ {σ = σ / ρ₁} ρ₁ ▻ var₂ · zero)  ≅⟨ map-cong P.refl P.refl P.refl
                                                                    (▻̂-cong P.refl P.refl H.refl H.refl
                                                                       (H.≡-to-≅ $ P.sym $ corresponds var₂ zero))
                                                                    H.refl (H.refl {x = app ρ₂↑})
                                                                    (H.sym $ Simple.unfold-↑ simple₂ ρ₁) ⟩
      map (app ρ₂↑) (ρ₁ ↑₂)                                    ≡⟨ P.refl ⟩
      ρ₁ ↑₂ ∘ ρ₂ ↑₁                                            ∎)
      where open H.≅-Reasoning

    -- N-ary lifting distributes over composition.

    ∘-↑⁺ : ∀ {Γ Δ Ε} {ρ̂₁ : Γ ⇨̂ Δ} {ρ̂₂ : Δ ⇨̂ Ε}
           (ρ₁ : Sub T₂ ρ̂₁) (ρ₂ : Sub T₁ ρ̂₂) Γ⁺ →
           (ρ₁ ∘ ρ₂) ↑⁺₂ Γ⁺ ≅ ρ₁ ↑⁺₂ Γ⁺ ∘ ρ₂ ↑⁺₁ (Γ⁺ /⁺ ρ₁)
    ∘-↑⁺ ρ₁ ρ₂ ε        = H.refl
    ∘-↑⁺ ρ₁ ρ₂ (Γ⁺ ▻ σ) = begin
      ((ρ₁ ∘ ρ₂) ↑⁺₂ Γ⁺) ↑₂                    ≅⟨ Simple.↑-cong simple₂ P.refl
                                                    (++-cong P.refl (H.≡-to-≅ $ /̂⁺-∘̂ Γ⁺ ⟦ ρ₁ ⟧⇨ ⟦ ρ₂ ⟧⇨))
                                                    (∘̂-↑̂⁺ ⟦ ρ₁ ⟧⇨ ⟦ ρ₂ ⟧⇨ Γ⁺)
                                                    (∘-↑⁺ ρ₁ ρ₂ Γ⁺) H.refl ⟩
      (ρ₁ ↑⁺₂ Γ⁺ ∘ ρ₂ ↑⁺₁ (Γ⁺ /⁺ ρ₁)) ↑₂       ≡⟨ ∘-↑ σ (ρ₁ ↑⁺₂ Γ⁺) (ρ₂ ↑⁺₁ (Γ⁺ /⁺ ρ₁)) ⟩
      (ρ₁ ↑⁺₂ Γ⁺) ↑₂ ∘ (ρ₂ ↑⁺₁ (Γ⁺ /⁺ ρ₁)) ↑₁  ∎
      where open H.≅-Reasoning

    -- First weakening and then substituting something for the first
    -- variable is equivalent to doing nothing.

    /⊢-wk-/⊢-sub : ∀ {Γ σ τ} (t : Γ ⊢₂ τ) (t′ : Γ ⊢₁ σ) →
                   t /⊢ wk₁ /⊢ sub₁ t′ ≡ t
    /⊢-wk-/⊢-sub t t′ = var-/⊢⋆-⇒-/⊢⋆ (ε ▻ wk₁ ▻ sub₁ t′) ε (λ x → begin
      var₂ · x /⊢ wk₁ /⊢ sub₁ t′  ≅⟨ /⊢-cong P.refl P.refl H.refl
                                             (H.≡-to-≅ $ /∋-≡-var x wk₁ (Simple./∋-wk simple₁ x))
                                             H.refl H.refl ⟩
      var₂ · suc x /⊢ sub₁ t′     ≡⟨ suc-/⊢-sub x t′ ⟩
      var₂ · x                    ∎) t
      where open P.≡-Reasoning

    -- Weakening a substitution and composing with sub is the same as
    -- doing nothing.

    wk-subst-∘-sub : ∀ {Γ Δ σ} {ρ̂ : Γ ⇨̂ Δ} (ρ : Sub T₂ ρ̂) (t : Δ ⊢₁ σ) →
                     wk-subst₂ ρ ∘ sub₁ t ≡ ρ
    wk-subst-∘-sub ρ t = H.≅-to-≡ $ extensionality P.refl H.refl λ x →
      let lemma = begin
            x /∋ wk-subst₂ ρ    ≡⟨ Simple./∋-wk-subst simple₂ x ρ ⟩
            weaken₂ · (x /∋ ρ)  ≡⟨ P.sym $ /⊢-wk (x /∋ ρ) ⟩
            x /∋ ρ /⊢ wk₁       ∎
      in begin
        x /∋ wk-subst₂ ρ ∘ sub₁ t     ≡⟨ /∋-∘ x (wk-subst₂ ρ) (sub₁ t) ⟩
        x /∋ wk-subst₂ ρ /⊢ sub₁ t    ≅⟨ /⊢-cong P.refl P.refl H.refl lemma H.refl H.refl ⟩
        x /∋ ρ /⊢ wk₁ /⊢ sub₁ t       ≡⟨ /⊢-wk-/⊢-sub (x /∋ ρ) t ⟩
        x /∋ ρ                        ∎
      where open H.≅-Reasoning
