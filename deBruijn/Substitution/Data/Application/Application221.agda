------------------------------------------------------------------------
-- Lemmas related to application of substitutions
------------------------------------------------------------------------

{-# OPTIONS --universe-polymorphism #-}

open import Universe

module deBruijn.Substitution.Data.Application.Application221
  {u e} {Uni : Universe u e}
  where

import deBruijn.Context as Context
open import deBruijn.Substitution.Data.Application.Application21
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

record Application₂₂₁
  {t₁} {T₁ : Term-like t₁}
  {t₂} {T₂ : Term-like t₂}

  -- Simple substitutions for the first kind of terms.
  (simple₁ : Simple T₁)

  -- Simple substitutions for the second kind of terms.
  (simple₂ : Simple T₂)

  -- A translation from the first to the second kind of terms.
  (trans : [ T₁ ⟶⁼ T₂ ])
  : Set (u ⊔ e ⊔ t₁ ⊔ t₂) where

  open Term-like T₂ renaming (_⊢_ to _⊢₂_)
  open Simple simple₁
    using ()
    renaming ( wk to wk₁; wk-subst to wk-subst₁
             ; _↑ to _↑₁; _↑⁺_ to _↑⁺₁_; _↑⁺⋆_ to _↑⁺⋆₁_
             )
  open Simple simple₂
    using ()
    renaming ( var to var₂
             ; weaken to weaken₂; wk to wk₂; wk-subst to wk-subst₂
             ; _↑ to _↑₂
             )

  field
    application₂₁ : Application₂₁ simple₁ simple₂ trans

  open Application₂₁ application₂₁

  field
    -- Lifts equalities valid for all variables and liftings to
    -- arbitrary terms.
    var-/⊢⋆-↑⁺⋆-⇒-/⊢⋆-↑⁺⋆ :
      ∀ {Γ Δ} {ρ̂ : Γ ⇨̂ Δ} (ρs₁ : Subs T₁ ρ̂) (ρs₂ : Subs T₁ ρ̂) →
      (∀ Γ⁺ {σ} (x : Γ ++ Γ⁺ ∋ σ) →
         var₂ · x /⊢⋆ ρs₁ ↑⁺⋆₁ Γ⁺ ≡ var₂ · x /⊢⋆ ρs₂ ↑⁺⋆₁ Γ⁺) →
      ∀ Γ⁺ {σ} (t : Γ ++ Γ⁺ ⊢₂ σ) →
      t /⊢⋆ ρs₁ ↑⁺⋆₁ Γ⁺ ≡ t /⊢⋆ ρs₂ ↑⁺⋆₁ Γ⁺

    -- The wk substitution and the weaken function are equivalent.
    /⊢-wk : ∀ {Γ σ τ} (t : Γ ⊢₂ τ) → t /⊢ wk₁ ≡ weaken₂ {σ = σ} · t

  abstract

    -- wk-subst is equivalent to composition with wk.

    ∘-wk : ∀ {Γ Δ σ} {ρ̂ : Γ ⇨̂ Δ} (ρ : Sub T₂ ρ̂) →
           ρ ∘ wk₁ ≡ wk-subst₂ {σ = σ} ρ
    ∘-wk ρ = begin
      map (app wk₁) ρ  ≅⟨ map-cong-ext₁ P.refl P.refl H.refl H.refl
                                        (λ t → H.≡-to-≅ $ /⊢-wk t)
                                        (H.refl {x = ρ}) ⟩
      map weaken₂   ρ  ∎
      where open P.≡-Reasoning

    -- The wk substitution commutes with any other (more or less).
    --
    -- TODO: Prove this lemma using /⊢-/⊢-wk?

    wk-∘-↑ : ∀ {Γ Δ} σ {ρ̂ : Γ ⇨̂ Δ} (ρ : Sub T₁ ρ̂) →
             map trans ρ ∘ wk₁ ≡ wk₂ {σ = σ} ∘ ρ ↑₁
    wk-∘-↑ σ ρ = H.≅-to-≡ $ extensionality P.refl H.refl λ {τ} x → begin
      x /∋ map trans ρ ∘ wk₁             ≅⟨ /∋-cong P.refl P.refl H.refl (H.refl {x = x}) H.refl
                                              (H.≡-to-≅ $ ∘-wk (map trans ρ)) ⟩
      x /∋ wk-subst₂ (map trans ρ)       ≡⟨ P.sym $ Simple.suc-/∋-↑ simple₂ σ x (map trans ρ) ⟩
      suc {σ = σ} x /∋ map trans ρ ↑₂    ≅⟨ /∋-cong P.refl P.refl H.refl (H.refl {x = suc {σ = σ} x})
                                                    H.refl (H.≡-to-≅ $ P.sym $ map-trans-↑ ρ) ⟩
      suc {σ = σ} x /∋ map trans (ρ ↑₁)  ≡⟨ /∋-map (suc {σ = σ} x) trans (ρ ↑₁) ⟩
      trans · (suc {σ = σ} x /∋ ρ ↑₁)    ≡⟨ P.sym $ var-/⊢ (suc {σ = σ} x) (ρ ↑₁) ⟩
      var₂ · suc {σ = σ} x /⊢ ρ ↑₁       ≅⟨ /⊢-cong P.refl P.refl H.refl
                                              (H.≡-to-≅ $ P.sym $ Simple./∋-wk simple₂ {σ = σ} x)
                                              H.refl (H.refl {x = ρ ↑₁}) ⟩
      x /∋ wk₂ {σ = σ} /⊢ ρ ↑₁           ≡⟨ P.sym $ /∋-∘ x (wk₂ {σ = σ}) (ρ ↑₁) ⟩
      x /∋ wk₂ {σ = σ} ∘ ρ ↑₁            ∎
      where open H.≅-Reasoning

    -- A variant of suc-/∋-↑.

    var-suc-/⊢-↑ :
      ∀ {Γ Δ} σ {τ} {ρ̂ : Γ ⇨̂ Δ} (x : Γ ∋ τ) (ρ : Sub T₁ ρ̂) →
      var₂ · suc {σ = σ} x /⊢ ρ ↑₁ ≡ var₂ · x /⊢ ρ /⊢ wk₁
    var-suc-/⊢-↑ σ x ρ =
      let lemma₁ = begin
            x /∋ map trans ρ  ≡⟨ /∋-map x trans ρ ⟩
            trans · (x /∋ ρ)  ≡⟨ P.sym $ var-/⊢ x ρ ⟩
            var₂ · x /⊢ ρ     ∎

          lemma₂ = begin
            map trans (wk-subst₁ ρ)  ≡⟨ map-trans-wk-subst ρ ⟩
            wk-subst₂ (map trans ρ)  ≡⟨ P.sym $ ∘-wk (map trans ρ) ⟩
            map trans ρ ∘ wk₁        ∎

      in begin
      var₂ · suc {σ = σ} x /⊢ ρ ↑₁     ≡⟨ var-/⊢ (suc {σ = σ} x) (ρ ↑₁) ⟩
      trans · (suc {σ = σ} x /∋ ρ ↑₁)  ≅⟨ trans-cong P.refl H.refl (H.≡-to-≅ $ Simple.suc-/∋-↑ simple₁ σ x ρ) ⟩
      trans · (x /∋ wk-subst₁ ρ)       ≡⟨ P.sym $ /∋-map x trans (wk-subst₁ ρ) ⟩
      x /∋ map trans (wk-subst₁ ρ)     ≅⟨ /∋-cong P.refl P.refl H.refl (H.refl {x = x}) H.refl (H.≡-to-≅ lemma₂) ⟩
      x /∋ map trans ρ ∘ wk₁           ≡⟨ /∋-∘ x (map trans ρ) wk₁ ⟩
      x /∋ map trans ρ /⊢ wk₁          ≅⟨ /⊢-cong P.refl P.refl H.refl (H.≡-to-≅ lemma₁) H.refl (H.refl {x = wk₁}) ⟩
      var₂ · x /⊢ ρ /⊢ wk₁             ∎
      where open P.≡-Reasoning

    private

      -- wk ↑⁺ Γ⁺ and wk commute (more or less).
      --
      -- This lemma is an instance of /⊢-/⊢-wk, which is proved below
      -- using, among other things, this lemma.

      /⊢-wk-↑⁺-/⊢-wk :
        ∀ {Γ} σ Γ⁺ τ {υ} (t : Γ ++ Γ⁺ ⊢₂ υ) →
        t /⊢ wk₁ ↑⁺₁ Γ⁺ /⊢ wk₁ ≡ t /⊢ wk₁ /⊢ wk₁ {σ = σ} ↑⁺₁ (Γ⁺ ▻ τ)
      /⊢-wk-↑⁺-/⊢-wk σ Γ⁺ τ {υ} t = var-/⊢⋆-↑⁺⋆-⇒-/⊢⋆-↑⁺⋆
        (ε ▻ wk₁ {σ = σ} ↑⁺₁ Γ⁺ ▻ wk₁ {σ = τ / wk₁ ↑⁺₁ Γ⁺})
        (ε ▻ wk₁ ▻ wk₁ ↑⁺₁ (Γ⁺ ▻ τ))
        (λ Γ⁺⁺ {υ} x → H.≅-to-≡ (begin
           var₂ · x /⊢⋆ (ε ▻ wk₁ ↑⁺₁ Γ⁺ ▻ wk₁) ↑⁺⋆₁ Γ⁺⁺                ≅⟨ /⊢⋆-ε-▻-▻-↑⁺⋆ Γ⁺⁺ (var₂ · x) (wk₁ ↑⁺₁ Γ⁺) wk₁ ⟩
           var₂ · x /⊢ wk₁ ↑⁺₁ Γ⁺ ↑⁺₁ Γ⁺⁺ /⊢
             wk₁ ↑⁺₁ (Γ⁺⁺ /⁺ wk₁ ↑⁺₁ Γ⁺)                               ≅⟨ /⊢-cong P.refl P.refl H.refl
                                                                                  (H.≡-to-≅ $ var-/⊢-wk-↑⁺-↑⁺ Γ⁺ Γ⁺⁺ x)
                                                                                  H.refl H.refl ⟩
           var₂ · (lift (lift weaken∋ Γ⁺) Γ⁺⁺ · x) /⊢
             wk₁ ↑⁺₁ (Γ⁺⁺ /⁺ wk₁ ↑⁺₁ Γ⁺)                               ≡⟨ var-/⊢-wk-↑⁺ (Γ⁺⁺ /⁺ wk₁ ↑⁺₁ Γ⁺)
                                                                                       (lift (lift weaken∋ Γ⁺) Γ⁺⁺ · x) ⟩
           var₂ · (lift weaken∋ (Γ⁺⁺ /⁺ wk₁ ↑⁺₁ Γ⁺) ·
                     (lift (lift weaken∋ Γ⁺) Γ⁺⁺ · x))                 ≅⟨ Simple.var-cong simple₂
                                                                            (▻-/̂-++-/̂⁺-/̂⁺-ŵk τ (ŵk ↑̂⁺ Γ⁺) Γ⁺⁺)
                                                                            (/̂-↑̂⁺-/̂-ŵk-↑̂⁺ τ (ŵk ↑̂⁺ Γ⁺) Γ⁺⁺ υ)
                                                                            (lift-weaken∋-lift-lift-weaken∋ σ Γ⁺ τ Γ⁺⁺ x) ⟩
           var₂ · (lift (lift weaken∋ (Γ⁺ ▻ τ)) (Γ⁺⁺ /⁺ wk₁) ·
                     (lift weaken∋ Γ⁺⁺ · x))                           ≡⟨ P.sym $ var-/⊢-wk-↑⁺-↑⁺ (Γ⁺ ▻ τ) (Γ⁺⁺ /⁺ wk₁)
                                                                                                  (lift weaken∋ Γ⁺⁺ · x) ⟩
           var₂ · (lift weaken∋ Γ⁺⁺ · x) /⊢
             wk₁ {σ = σ} ↑⁺₁ (Γ⁺ ▻ τ) ↑⁺₁ (Γ⁺⁺ /⁺ wk₁)                 ≅⟨ H.sym $ /⊢-cong P.refl P.refl H.refl
                                                                                          (H.≡-to-≅ $ var-/⊢-wk-↑⁺ Γ⁺⁺ x)
                                                                                          H.refl H.refl ⟩
           var₂ · x /⊢ wk₁ ↑⁺₁ Γ⁺⁺ /⊢
             wk₁ {σ = σ} ↑⁺₁ (Γ⁺ ▻ τ) ↑⁺₁ (Γ⁺⁺ /⁺ wk₁)                 ≅⟨ H.sym $ /⊢⋆-ε-▻-▻-↑⁺⋆ Γ⁺⁺ (var₂ · x) wk₁
                                                                                                (wk₁ {σ = σ} ↑⁺₁ (Γ⁺ ▻ τ)) ⟩
           var₂ · x /⊢⋆ (ε ▻ wk₁ ▻ wk₁ {σ = σ} ↑⁺₁ (Γ⁺ ▻ τ)) ↑⁺⋆₁ Γ⁺⁺  ∎))
        ε t
        where open H.≅-Reasoning

      -- Another lemma used in the proof of /⊢-/⊢-wk.

      var-/⊢-↑⁺-wk-↑⁺ :
        ∀ {Γ Δ} σ {ρ̂ : Γ ⇨̂ Δ} (ρ : Sub T₁ ρ̂) Γ⁺ {υ} (x : Γ ++ Γ⁺ ∋ υ) →
        var₂ · x /⊢ ρ ↑⁺₁ Γ⁺ /⊢ wk₁ {σ = σ / ρ} ↑⁺₁ (Γ⁺ /⁺ ρ) ≅
        var₂ · (lift (weaken∋ {σ = σ}) Γ⁺ · x) /⊢ ρ ↑₁ ↑⁺₁ (Γ⁺ /⁺ wk₁)
      var-/⊢-↑⁺-wk-↑⁺ σ ρ ε        x    = H.≡-to-≅ $ P.sym $ var-suc-/⊢-↑ σ x ρ
      var-/⊢-↑⁺-wk-↑⁺ σ ρ (Γ⁺ ▻ τ) zero =
        let lemma₁ = ▻-/̂-++-/̂⁺-/̂⁺-ŵk σ ⟦ ρ ⟧⇨ Γ⁺
            lemma₂ = /̂-↑̂⁺-/̂-ŵk-↑̂⁺ σ ⟦ ρ ⟧⇨ Γ⁺ τ
        in begin
        var₂ · zero /⊢ ρ ↑⁺₁ (Γ⁺ ▻ τ) /⊢ wk₁ ↑⁺₁ ((Γ⁺ ▻ τ) /⁺ ρ)  ≅⟨ /⊢-cong P.refl P.refl H.refl
                                                                             (H.≡-to-≅ $ zero-/⊢-↑ τ (ρ ↑⁺₁ Γ⁺))
                                                                             H.refl (H.refl {x = wk₁ ↑⁺₁ ((Γ⁺ ▻ τ) /⁺ ρ)}) ⟩
        var₂ · zero /⊢ wk₁ ↑⁺₁ ((Γ⁺ ▻ τ) /⁺ ρ)                    ≡⟨ zero-/⊢-↑ (τ / ρ ↑⁺₁ Γ⁺) (wk₁ ↑⁺₁ (Γ⁺ /⁺ ρ)) ⟩
        var₂ · zero                                               ≅⟨ Simple.var-cong simple₂ (▻-cong lemma₁ lemma₂)
                                                                                     (/̂-cong lemma₁ (▻-cong lemma₁ lemma₂)
                                                                                             lemma₂ (ŵk-cong lemma₁ lemma₂))
                                                                                     (zero-cong lemma₁ lemma₂) ⟩
        var₂ · zero                                               ≡⟨ P.sym $ zero-/⊢-↑ (τ / wk₁ ↑⁺₁ Γ⁺)
                                                                                       (_↑₁ {σ = σ} ρ ↑⁺₁ (Γ⁺ /⁺ wk₁)) ⟩
        var₂ · zero /⊢ _↑₁ {σ = σ} ρ ↑⁺₁ ((Γ⁺ ▻ τ) /⁺ wk₁)        ∎
        where open H.≅-Reasoning
      var-/⊢-↑⁺-wk-↑⁺ σ ρ (Γ⁺ ▻ τ) (suc {τ = υ} x) =
        let lemma₁ = ▻-/̂-++-/̂⁺-/̂⁺-ŵk σ ⟦ ρ ⟧⇨ Γ⁺
            lemma₂ = /̂-↑̂⁺-/̂-ŵk-↑̂⁺ σ ⟦ ρ ⟧⇨ Γ⁺
        in begin
        var₂ · suc x /⊢ ρ ↑⁺₁ (Γ⁺ ▻ τ) /⊢ wk₁ ↑⁺₁ ((Γ⁺ ▻ τ) /⁺ ρ)  ≅⟨ /⊢-cong P.refl P.refl H.refl
                                                                              (H.≡-to-≅ $ var-suc-/⊢-↑ τ x (ρ ↑⁺₁ Γ⁺))
                                                                              H.refl (H.refl {x = wk₁ ↑⁺₁ ((Γ⁺ ▻ τ) /⁺ ρ)}) ⟩
        var₂ · x /⊢ ρ ↑⁺₁ Γ⁺ /⊢ wk₁ /⊢ wk₁ ↑⁺₁ ((Γ⁺ ▻ τ) /⁺ ρ)     ≡⟨ P.sym $ /⊢-wk-↑⁺-/⊢-wk
                                                                        (σ / ρ) (Γ⁺ /⁺ ρ) (τ / ρ ↑⁺₁ Γ⁺)
                                                                        (var₂ · x /⊢ ρ ↑⁺₁ Γ⁺) ⟩
        var₂ · x /⊢ ρ ↑⁺₁ Γ⁺ /⊢ wk₁ {σ = σ / ρ} ↑⁺₁ (Γ⁺ /⁺ ρ)
          /⊢ wk₁ {σ = τ / ρ ↑⁺₁ Γ⁺ / wk₁ ↑⁺₁ (Γ⁺ /⁺ ρ)}            ≅⟨ /⊢-cong lemma₁ (▻-cong lemma₁ (lemma₂ τ)) (lemma₂ υ)
                                                                              (var-/⊢-↑⁺-wk-↑⁺ σ ρ Γ⁺ x)
                                                                              (ŵk-cong lemma₁ (lemma₂ τ))
                                                                              (Simple.wk-cong simple₁ lemma₁ (lemma₂ τ)) ⟩
        var₂ · (lift (weaken∋ {σ = σ}) Γ⁺ · x) /⊢
          ρ ↑₁ ↑⁺₁ (Γ⁺ /⁺ wk₁) /⊢ wk₁                              ≡⟨ P.sym $ var-suc-/⊢-↑
                                                                        (τ / wk₁ ↑⁺₁ Γ⁺)
                                                                        (lift (weaken∋ {σ = σ}) Γ⁺ · x)
                                                                        (ρ ↑₁ ↑⁺₁ (Γ⁺ /⁺ wk₁)) ⟩
        var₂ · suc (lift (weaken∋ {σ = σ}) Γ⁺ · x) /⊢
          ρ ↑₁ ↑⁺₁ ((Γ⁺ ▻ τ) /⁺ wk₁)                               ∎
        where open H.≅-Reasoning

    -- The wk substitution commutes with any other (more or less).

    /⊢-/⊢-wk : ∀ {Γ Δ} σ {τ} {ρ̂ : Γ ⇨̂ Δ} (t : Γ ⊢₂ τ) (ρ : Sub T₁ ρ̂) →
               t /⊢ ρ /⊢ wk₁ ≡ t /⊢ wk₁ {σ = σ} /⊢ ρ ↑₁
    /⊢-/⊢-wk {Γ} {Δ} σ t ρ = var-/⊢⋆-↑⁺⋆-⇒-/⊢⋆-↑⁺⋆
      (ε ▻ ρ ▻ wk₁)
      (ε ▻ wk₁ {σ = σ} ▻ ρ ↑₁)
      (λ Γ⁺ x → H.≅-to-≡ (begin
         var₂ · x /⊢⋆ (ε ▻ ρ ▻ wk₁) ↑⁺⋆₁ Γ⁺                              ≅⟨ /⊢⋆-ε-▻-▻-↑⁺⋆ Γ⁺ (var₂ · x) ρ wk₁ ⟩
         var₂ · x /⊢ ρ ↑⁺₁ Γ⁺ /⊢ wk₁ ↑⁺₁ (Γ⁺ /⁺ ρ)                       ≅⟨ var-/⊢-↑⁺-wk-↑⁺ σ ρ Γ⁺ x ⟩
         var₂ · (lift (weaken∋ {σ = σ}) Γ⁺ · x) /⊢ ρ ↑₁ ↑⁺₁ (Γ⁺ /⁺ wk₁)  ≅⟨ /⊢-cong P.refl P.refl H.refl
                                                                                    (H.≡-to-≅ $ P.sym $ var-/⊢-wk-↑⁺ {σ = σ} Γ⁺ x)
                                                                                    H.refl (H.refl {x = ρ ↑₁ ↑⁺₁ (Γ⁺ /⁺ wk₁)}) ⟩
         var₂ · x /⊢ wk₁ {σ = σ} ↑⁺₁ Γ⁺ /⊢ ρ ↑₁ ↑⁺₁ (Γ⁺ /⁺ wk₁)          ≅⟨ H.sym $ /⊢⋆-ε-▻-▻-↑⁺⋆ Γ⁺ (var₂ · x) (wk₁ {σ = σ}) (ρ ↑₁) ⟩
         var₂ · x /⊢⋆ (ε ▻ wk₁ {σ = σ} ▻ ρ ↑₁) ↑⁺⋆₁ Γ⁺                   ∎)) ε t
      where open H.≅-Reasoning

  open Application₂₁ application₂₁ public
