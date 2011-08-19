------------------------------------------------------------------------
-- Lemmas related to application of substitutions
------------------------------------------------------------------------

{-# OPTIONS --universe-polymorphism #-}

open import Universe

module deBruijn.Substitution.Data.Application.Application221
  {i u e} {Uni : Indexed-universe i u e}
  where

import deBruijn.Context as Context
open import deBruijn.Substitution.Data.Application.Application21
open import deBruijn.Substitution.Data.Basics
open import deBruijn.Substitution.Data.Map
open import deBruijn.Substitution.Data.Simple
import deBruijn.TermLike as TermLike
open import Function using (_$_)
open import Level using (_⊔_)
import Relation.Binary.PropositionalEquality as P

open Context Uni
open P.≡-Reasoning
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
  : Set (i ⊔ u ⊔ e ⊔ t₁ ⊔ t₂) where

  open Term-like T₂ using ([_]) renaming (_⊢_ to _⊢₂_; _≅-⊢_ to _≅-⊢₂_)
  open Simple simple₁
    using ()
    renaming ( wk to wk₁; wk[_] to wk₁[_]; wk-subst to wk-subst₁
             ; _↑ to _↑₁; _↑_ to _↑₁_; _↑⁺_ to _↑⁺₁_; _↑⁺⋆_ to _↑⁺⋆₁_
             )
  open Simple simple₂
    using ()
    renaming ( var to var₂
             ; weaken to weaken₂; weaken[_] to weaken₂[_]
             ; wk[_] to wk₂[_]
             ; wk-subst to wk-subst₂; wk-subst[_] to wk-subst₂[_]
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
      (∀ Γ⁺ {σ} (x : Γ ++⁺ Γ⁺ ∋ σ) →
         var₂ · x /⊢⋆ ρs₁ ↑⁺⋆₁ Γ⁺ ≅-⊢₂ var₂ · x /⊢⋆ ρs₂ ↑⁺⋆₁ Γ⁺) →
      ∀ Γ⁺ {σ} (t : Γ ++⁺ Γ⁺ ⊢₂ σ) →
      t /⊢⋆ ρs₁ ↑⁺⋆₁ Γ⁺ ≅-⊢₂ t /⊢⋆ ρs₂ ↑⁺⋆₁ Γ⁺

    -- The wk substitution and the weaken function are equivalent.
    /⊢-wk : ∀ {Γ σ τ} (t : Γ ⊢₂ τ) →
            t /⊢ wk₁[ σ ] ≅-⊢₂ weaken₂[ σ ] · t

  abstract

    -- wk-subst is equivalent to composition with wk.

    ∘-wk : ∀ {Γ Δ σ} {ρ̂ : Γ ⇨̂ Δ} (ρ : Sub T₂ ρ̂) →
           ρ ∘ wk₁[ σ ] ≅-⇨ wk-subst₂[ σ ] ρ
    ∘-wk ρ = begin
      [ map (app wk₁) ρ ]  ≡⟨ map-cong-ext₁ P.refl /⊢-wk (P.refl {x = [ ρ ]}) ⟩
      [ map weaken₂   ρ ]  ∎

    -- The wk substitution commutes (modulo lifting etc.) with any
    -- other.
    --
    -- TODO: Prove this lemma using /⊢-/⊢-wk?

    wk-∘-↑ : ∀ {Γ Δ} σ {ρ̂ : Γ ⇨̂ Δ} (ρ : Sub T₁ ρ̂) →
             map trans ρ ∘ wk₁[ σ / ρ ] ≅-⇨ wk₂[ σ ] ∘ ρ ↑₁
    wk-∘-↑ σ ρ = extensionality P.refl λ x → begin
      [ x /∋ map trans ρ ∘ wk₁         ]  ≡⟨ /∋-cong (P.refl {x = [ x ]}) (∘-wk (map trans ρ)) ⟩
      [ x /∋ wk-subst₂ (map trans ρ)   ]  ≡⟨ P.sym $ Simple.suc-/∋-↑ simple₂ σ x (map trans ρ) ⟩
      [ suc[ σ ] x /∋ map trans ρ ↑₂   ]  ≡⟨ /∋-cong (P.refl {x = [ suc[ σ ] x ]}) (P.sym $ map-trans-↑ ρ) ⟩
      [ suc[ σ ] x /∋ map trans (ρ ↑₁) ]  ≡⟨ /∋-map (suc[ σ ] x) trans (ρ ↑₁) ⟩
      [ trans · (suc[ σ ] x /∋ ρ ↑₁)   ]  ≡⟨ P.sym $ var-/⊢ (suc[ σ ] x) (ρ ↑₁) ⟩
      [ var₂ · suc[ σ ] x /⊢ ρ ↑₁      ]  ≡⟨ /⊢-cong (P.sym $ Simple./∋-wk simple₂ {σ = σ} x) (P.refl {x = [ ρ ↑₁ ]}) ⟩
      [ x /∋ wk₂[ σ ] /⊢ ρ ↑₁          ]  ≡⟨ P.sym $ /∋-∘ x wk₂[ σ ] (ρ ↑₁) ⟩
      [ x /∋ wk₂[ σ ] ∘ ρ ↑₁           ]  ∎

    -- A variant of suc-/∋-↑.

    var-suc-/⊢-↑ :
      ∀ {Γ Δ} σ {τ} {ρ̂ : Γ ⇨̂ Δ} (x : Γ ∋ τ) (ρ : Sub T₁ ρ̂) →
      var₂ · suc[ σ ] x /⊢ ρ ↑₁ ≅-⊢₂
      var₂ · x /⊢ ρ /⊢ wk₁[ σ / ρ ]
    var-suc-/⊢-↑ σ x ρ =
      let lemma₁ = begin
            [ x /∋ map trans ρ ]  ≡⟨ /∋-map x trans ρ ⟩
            [ trans · (x /∋ ρ) ]  ≡⟨ P.sym $ var-/⊢ x ρ ⟩
            [ var₂ · x /⊢ ρ    ]  ∎

          lemma₂ = begin
            [ map trans (wk-subst₁ ρ) ]  ≡⟨ map-trans-wk-subst ρ ⟩
            [ wk-subst₂ (map trans ρ) ]  ≡⟨ P.sym $ ∘-wk (map trans ρ) ⟩
            [ map trans ρ ∘ wk₁       ]  ∎

      in begin
      [ var₂ · suc[ σ ] x /⊢ ρ ↑₁    ]  ≡⟨ var-/⊢ (suc[ σ ] x) (ρ ↑₁) ⟩
      [ trans · (suc[ σ ] x /∋ ρ ↑₁) ]  ≡⟨ trans-cong (Simple.suc-/∋-↑ simple₁ σ x ρ) ⟩
      [ trans · (x /∋ wk-subst₁ ρ)      ]  ≡⟨ P.sym $ /∋-map x trans (wk-subst₁ ρ) ⟩
      [ x /∋ map trans (wk-subst₁ ρ)    ]  ≡⟨ /∋-cong (P.refl {x = [ x ]}) lemma₂ ⟩
      [ x /∋ map trans ρ ∘ wk₁          ]  ≡⟨ /∋-∘ x (map trans ρ) wk₁ ⟩
      [ x /∋ map trans ρ /⊢ wk₁         ]  ≡⟨ /⊢-cong lemma₁ (P.refl {x = [ wk₁ ]}) ⟩
      [ var₂ · x /⊢ ρ /⊢ wk₁            ]  ∎

    private

      -- wk ↑⁺ Γ⁺ and wk commute (more or less).
      --
      -- This lemma is an instance of /⊢-/⊢-wk, which is proved below
      -- using, among other things, this lemma.

      /⊢-wk-↑⁺-/⊢-wk :
        ∀ {Γ} σ Γ⁺ τ {υ} (t : Γ ++⁺ Γ⁺ ⊢₂ υ) →
        let wk-σ = wk₁[ σ ] ↑⁺₁ Γ⁺ in
        t /⊢ wk-σ /⊢ wk₁[ τ / wk-σ ] ≅-⊢₂
        t /⊢ wk₁ /⊢ wk₁[ σ ] ↑⁺₁ (Γ⁺ ▻ τ)
      /⊢-wk-↑⁺-/⊢-wk σ Γ⁺ τ t = var-/⊢⋆-↑⁺⋆-⇒-/⊢⋆-↑⁺⋆
        (ε ▻ wk₁[ σ ] ↑⁺₁ Γ⁺ ▻ wk₁[ τ / wk₁ ↑⁺₁ Γ⁺ ])
        (ε ▻ wk₁ ▻ wk₁ ↑⁺₁ (Γ⁺ ▻ τ))
        (λ Γ⁺⁺ x → begin
           [ var₂ · x /⊢⋆ (ε ▻ wk₁ ↑⁺₁ Γ⁺ ▻ wk₁) ↑⁺⋆₁ Γ⁺⁺            ]  ≡⟨ /⊢⋆-ε-▻-▻-↑⁺⋆ Γ⁺⁺ (var₂ · x) (wk₁ ↑⁺₁ Γ⁺) wk₁ ⟩
           [ var₂ · x /⊢ wk₁ ↑⁺₁ Γ⁺ ↑⁺₁ Γ⁺⁺ /⊢
               wk₁ ↑⁺₁ (Γ⁺⁺ /⁺ wk₁ ↑⁺₁ Γ⁺)                           ]  ≡⟨ /⊢-cong (var-/⊢-wk-↑⁺-↑⁺ Γ⁺ Γ⁺⁺ x) P.refl ⟩
           [ var₂ · (lift (lift weaken∋ Γ⁺) Γ⁺⁺ · x) /⊢
               wk₁ ↑⁺₁ (Γ⁺⁺ /⁺ wk₁ ↑⁺₁ Γ⁺)                           ]  ≡⟨ var-/⊢-wk-↑⁺ (Γ⁺⁺ /⁺ wk₁ ↑⁺₁ Γ⁺)
                                                                                        (lift (lift weaken∋ Γ⁺) Γ⁺⁺ · x) ⟩
           [ var₂ · (lift weaken∋ (Γ⁺⁺ /⁺ wk₁ ↑⁺₁ Γ⁺) ·
                       (lift (lift weaken∋ Γ⁺) Γ⁺⁺ · x))             ]  ≡⟨ Simple.var-cong simple₂
                                                                             (lift-weaken∋-lift-lift-weaken∋ σ Γ⁺ τ Γ⁺⁺ x) ⟩
           [ var₂ · (lift (lift weaken∋ (Γ⁺ ▻ τ)) (Γ⁺⁺ /⁺ wk₁) ·
                       (lift weaken∋ Γ⁺⁺ · x))                       ]  ≡⟨ P.sym $ var-/⊢-wk-↑⁺-↑⁺ (Γ⁺ ▻ τ) (Γ⁺⁺ /⁺ wk₁)
                                                                                                   (lift weaken∋ Γ⁺⁺ · x) ⟩
           [ var₂ · (lift weaken∋ Γ⁺⁺ · x) /⊢
               wk₁[ σ ] ↑⁺₁ (Γ⁺ ▻ τ) ↑⁺₁ (Γ⁺⁺ /⁺ wk₁)                ]  ≡⟨ P.sym $ /⊢-cong (var-/⊢-wk-↑⁺ Γ⁺⁺ x) P.refl ⟩
           [ var₂ · x /⊢ wk₁ ↑⁺₁ Γ⁺⁺ /⊢
               wk₁[ σ ] ↑⁺₁ (Γ⁺ ▻ τ) ↑⁺₁ (Γ⁺⁺ /⁺ wk₁)                ]  ≡⟨ P.sym $ /⊢⋆-ε-▻-▻-↑⁺⋆ Γ⁺⁺ (var₂ · x) wk₁
                                                                                                     (wk₁[ σ ] ↑⁺₁ (Γ⁺ ▻ τ)) ⟩
           [ var₂ · x /⊢⋆ (ε ▻ wk₁ ▻ wk₁[ σ ] ↑⁺₁ (Γ⁺ ▻ τ)) ↑⁺⋆₁ Γ⁺⁺ ]  ∎)
        ε t

      -- Another lemma used in the proof of /⊢-/⊢-wk.

      var-/⊢-↑⁺-/⊢-wk-↑⁺ :
        ∀ {Γ Δ} σ {ρ̂ : Γ ⇨̂ Δ} (ρ : Sub T₁ ρ̂) Γ⁺ {υ} (x : Γ ++⁺ Γ⁺ ∋ υ) →
        var₂ · x /⊢ ρ ↑⁺₁ Γ⁺ /⊢ wk₁[ σ / ρ ] ↑⁺₁ (Γ⁺ /⁺ ρ) ≅-⊢₂
        var₂ · (lift weaken∋[ σ ] Γ⁺ · x) /⊢ ρ ↑₁ ↑⁺₁ (Γ⁺ /⁺ wk₁)
      var-/⊢-↑⁺-/⊢-wk-↑⁺ σ ρ ε        x    = P.sym $ var-suc-/⊢-↑ σ x ρ
      var-/⊢-↑⁺-/⊢-wk-↑⁺ σ ρ (Γ⁺ ▻ τ) zero = begin
        [ var₂ · zero /⊢ ρ ↑⁺₁ (Γ⁺ ▻ τ) /⊢ wk₁ ↑⁺₁ ((Γ⁺ ▻ τ) /⁺ ρ) ]  ≡⟨ /⊢-cong (zero-/⊢-↑ τ (ρ ↑⁺₁ Γ⁺))
                                                                                 (P.refl {x = [ wk₁ ↑⁺₁ ((Γ⁺ ▻ τ) /⁺ ρ) ]}) ⟩
        [ var₂ · zero /⊢ wk₁ ↑⁺₁ ((Γ⁺ ▻ τ) /⁺ ρ)                   ]  ≡⟨ zero-/⊢-↑ (τ / ρ ↑⁺₁ Γ⁺) (wk₁ ↑⁺₁ (Γ⁺ /⁺ ρ)) ⟩
        [ var₂ · zero                                              ]  ≡⟨ Simple.var-cong simple₂
                                                                           (zero-cong (/̂-↑̂⁺-/̂-ŵk-↑̂⁺ σ ⟦ ρ ⟧⇨ Γ⁺ τ)) ⟩
        [ var₂ · zero                                              ]  ≡⟨ P.sym $ zero-/⊢-↑ (τ / wk₁ ↑⁺₁ Γ⁺)
                                                                                           (ρ ↑₁ σ ↑⁺₁ (Γ⁺ /⁺ wk₁)) ⟩
        [ var₂ · zero /⊢ ρ ↑₁ σ ↑⁺₁ ((Γ⁺ ▻ τ) /⁺ wk₁)              ]  ∎
      var-/⊢-↑⁺-/⊢-wk-↑⁺ σ ρ (Γ⁺ ▻ τ) (suc x) = begin
        [ var₂ · suc x /⊢ ρ ↑⁺₁ (Γ⁺ ▻ τ) /⊢ wk₁ ↑⁺₁ ((Γ⁺ ▻ τ) /⁺ ρ) ]  ≡⟨ /⊢-cong (var-suc-/⊢-↑ τ x (ρ ↑⁺₁ Γ⁺))
                                                                                  (P.refl {x = [ wk₁ ↑⁺₁ ((Γ⁺ ▻ τ) /⁺ ρ) ]}) ⟩
        [ var₂ · x /⊢ ρ ↑⁺₁ Γ⁺ /⊢ wk₁ /⊢ wk₁ ↑⁺₁ ((Γ⁺ ▻ τ) /⁺ ρ)    ]  ≡⟨ P.sym $ /⊢-wk-↑⁺-/⊢-wk (σ / ρ) (Γ⁺ /⁺ ρ) (τ / ρ ↑⁺₁ Γ⁺)
                                                                                                 (var₂ · x /⊢ ρ ↑⁺₁ Γ⁺) ⟩
        [ var₂ · x /⊢ ρ ↑⁺₁ Γ⁺ /⊢ wk₁[ σ / ρ ] ↑⁺₁ (Γ⁺ /⁺ ρ)
            /⊢ wk₁[ τ / ρ ↑⁺₁ Γ⁺ / wk₁ ↑⁺₁ (Γ⁺ /⁺ ρ) ]              ]  ≡⟨ /⊢-cong
                                                                            (var-/⊢-↑⁺-/⊢-wk-↑⁺ σ ρ Γ⁺ x)
                                                                            (Simple.wk-cong simple₁ (/̂-↑̂⁺-/̂-ŵk-↑̂⁺ σ ⟦ ρ ⟧⇨ Γ⁺ τ)) ⟩
        [ var₂ · (lift weaken∋[ σ ] Γ⁺ · x) /⊢
            ρ ↑₁ ↑⁺₁ (Γ⁺ /⁺ wk₁) /⊢ wk₁                             ]  ≡⟨ P.sym $ var-suc-/⊢-↑ (τ / wk₁ ↑⁺₁ Γ⁺)
                                                                                               (lift weaken∋[ σ ] Γ⁺ · x)
                                                                                               (ρ ↑₁ ↑⁺₁ (Γ⁺ /⁺ wk₁)) ⟩
        [ var₂ · suc (lift weaken∋[ σ ] Γ⁺ · x) /⊢
            ρ ↑₁ ↑⁺₁ ((Γ⁺ ▻ τ) /⁺ wk₁)                              ]  ∎

    -- The wk substitution commutes (modulo lifting etc.) with any
    -- other.

    /⊢-/⊢-wk : ∀ {Γ Δ} σ {τ} {ρ̂ : Γ ⇨̂ Δ} (t : Γ ⊢₂ τ) (ρ : Sub T₁ ρ̂) →
               t /⊢ ρ /⊢ wk₁[ σ / ρ ] ≅-⊢₂ t /⊢ wk₁[ σ ] /⊢ ρ ↑₁
    /⊢-/⊢-wk σ t ρ = var-/⊢⋆-↑⁺⋆-⇒-/⊢⋆-↑⁺⋆
      (ε ▻ ρ ▻ wk₁)
      (ε ▻ wk₁[ σ ] ▻ ρ ↑₁)
      (λ Γ⁺ x → begin
         [ var₂ · x /⊢⋆ (ε ▻ ρ ▻ wk₁) ↑⁺⋆₁ Γ⁺                        ]  ≡⟨ /⊢⋆-ε-▻-▻-↑⁺⋆ Γ⁺ (var₂ · x) ρ wk₁ ⟩
         [ var₂ · x /⊢ ρ ↑⁺₁ Γ⁺ /⊢ wk₁ ↑⁺₁ (Γ⁺ /⁺ ρ)                 ]  ≡⟨ var-/⊢-↑⁺-/⊢-wk-↑⁺ σ ρ Γ⁺ x ⟩
         [ var₂ · (lift weaken∋[ σ ] Γ⁺ · x) /⊢ ρ ↑₁ ↑⁺₁ (Γ⁺ /⁺ wk₁) ]  ≡⟨ /⊢-cong (P.sym $ var-/⊢-wk-↑⁺ {σ = σ} Γ⁺ x)
                                                                                   (P.refl {x = [ ρ ↑₁ ↑⁺₁ (Γ⁺ /⁺ wk₁) ]}) ⟩
         [ var₂ · x /⊢ wk₁[ σ ] ↑⁺₁ Γ⁺ /⊢ ρ ↑₁ ↑⁺₁ (Γ⁺ /⁺ wk₁)       ]  ≡⟨ P.sym $ /⊢⋆-ε-▻-▻-↑⁺⋆ Γ⁺ (var₂ · x) wk₁[ σ ] (ρ ↑₁) ⟩
         [ var₂ · x /⊢⋆ (ε ▻ wk₁[ σ ] ▻ ρ ↑₁) ↑⁺⋆₁ Γ⁺                ]  ∎) ε t

  open Application₂₁ application₂₁ public
