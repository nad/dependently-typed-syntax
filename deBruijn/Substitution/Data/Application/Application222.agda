------------------------------------------------------------------------
-- Lemmas related to application of substitutions
------------------------------------------------------------------------

{-# OPTIONS --universe-polymorphism #-}

open import Universe

module deBruijn.Substitution.Data.Application.Application222
  {i u e} {Uni : Indexed-universe i u e}
  where

import deBruijn.Context; open deBruijn.Context Uni
open import deBruijn.Substitution.Data.Application.Application221
open import deBruijn.Substitution.Data.Basics
open import deBruijn.Substitution.Data.Map
open import deBruijn.Substitution.Data.Simple
open import Function using (_$_)
open import Level using (_⊔_)
import Relation.Binary.PropositionalEquality as P

open P.≡-Reasoning

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
  : Set (i ⊔ u ⊔ e ⊔ t₁ ⊔ t₂) where

  open Term-like T₁ using () renaming (_⊢_ to _⊢₁_)
  open Term-like T₂ using ([_]) renaming (_⊢_ to _⊢₂_; _≅-⊢_ to _≅-⊢₂_)
  open Simple simple₁
    using ()
    renaming ( id to id₁; sub to sub₁; var to var₁
             ; wk to wk₁; wk[_] to wk₁[_]
             ; _↑ to _↑₁; _↑_ to _↑₁_; _↑⁺_ to _↑⁺₁_; _↑₊_ to _↑₊₁_
             ; _↑⋆ to _↑⋆₁; _↑⁺⋆_ to _↑⁺⋆₁_
             )
  open Simple simple₂
    using ()
    renaming ( var to var₂
             ; weaken to weaken₂; weaken[_] to weaken₂[_]
             ; wk-subst to wk-subst₂; wk-subst[_] to wk-subst₂[_]
             ; _↑ to _↑₂; _↑_ to _↑₂_; _↑⁺_ to _↑⁺₂_; _↑₊_ to _↑₊₂_
             )

  field
    application₂₂₁ : Application₂₂₁ simple₁ simple₂ trans

  open Application₂₂₁ application₂₂₁ public

  abstract

    -- A variant of suc-/∋-↑.

    suc-/⊢⋆-↑⋆ :
      ∀ {Γ Δ} {ρ̂ : Γ ⇨̂ Δ}
      σ {τ} (x : Γ ∋ τ) (ρs : Subs T₁ ρ̂) →
      var₂ · suc[ σ ] x /⊢⋆ ρs ↑⋆₁ ≅-⊢₂
      var₂ · x /⊢⋆ (ρs ▻ wk₁[ σ /⋆ ρs ])
    suc-/⊢⋆-↑⋆ σ x ε = begin
      [ var₂ · suc x    ]  ≡⟨ P.sym $ var-/⊢-wk-↑⁺ ε x ⟩
      [ var₂ · x /⊢ wk₁ ]  ∎
    suc-/⊢⋆-↑⋆ σ x (ρs ▻ ρ) = begin
      [ var₂ · suc[ σ ] x /⊢⋆ ρs ↑⋆₁ /⊢ ρ ↑₁      ]  ≡⟨ /⊢-cong (suc-/⊢⋆-↑⋆ σ x ρs) (P.refl {x = [ ρ ↑₁ ]}) ⟩
      [ var₂ · x /⊢⋆ ρs /⊢ wk₁[ σ /⋆ ρs ] /⊢ ρ ↑₁ ]  ≡⟨ P.sym $ /⊢-/⊢-wk (σ /⋆ ρs) (var₂ · x /⊢⋆ ρs) ρ ⟩
      [ var₂ · x /⊢⋆ ρs /⊢ ρ /⊢ wk₁               ]  ∎

    -- The antecedent of var-/⊢⋆-↑⁺⋆-⇒-/⊢⋆-↑⁺⋆ follows from a less
    -- complicated statement.

    var-/⊢⋆-⇒-var-/⊢⋆-↑⁺⋆ :
      ∀ {Γ Δ} {ρ̂ : Γ ⇨̂ Δ} {ρs₁ : Subs T₁ ρ̂} {ρs₂ : Subs T₁ ρ̂} →
      (∀ {σ} (x : Γ ∋ σ) → var₂ · x /⊢⋆ ρs₁ ≅-⊢₂ var₂ · x /⊢⋆ ρs₂) →
      ∀ Γ⁺ {σ} (x : Γ ++⁺ Γ⁺ ∋ σ) →
      var₂ · x /⊢⋆ ρs₁ ↑⁺⋆₁ Γ⁺ ≅-⊢₂ var₂ · x /⊢⋆ ρs₂ ↑⁺⋆₁ Γ⁺
    var-/⊢⋆-⇒-var-/⊢⋆-↑⁺⋆                   hyp ε        x    = hyp x
    var-/⊢⋆-⇒-var-/⊢⋆-↑⁺⋆ {ρs₁ = ρs₁} {ρs₂} hyp (Γ⁺ ▻ σ) zero = begin
      [ var₂ · zero /⊢⋆ ρs₁ ↑⁺⋆₁ (Γ⁺ ▻ σ) ]  ≡⟨ zero-/⊢⋆-↑⋆ σ (ρs₁ ↑⁺⋆₁ Γ⁺) ⟩
      [ var₂ · zero                       ]  ≡⟨ P.sym $ zero-/⊢⋆-↑⋆ σ (ρs₂ ↑⁺⋆₁ Γ⁺) ⟩
      [ var₂ · zero /⊢⋆ ρs₂ ↑⁺⋆₁ (Γ⁺ ▻ σ) ]  ∎
    var-/⊢⋆-⇒-var-/⊢⋆-↑⁺⋆ {ρs₁ = ρs₁} {ρs₂} hyp (Γ⁺ ▻ σ) (suc x) = begin
      [ var₂ · suc x /⊢⋆ ρs₁ ↑⁺⋆₁ (Γ⁺ ▻ σ)  ]  ≡⟨ suc-/⊢⋆-↑⋆ σ x (ρs₁ ↑⁺⋆₁ Γ⁺) ⟩
      [ var₂ · x     /⊢⋆ ρs₁ ↑⁺⋆₁ Γ⁺ /⊢ wk₁ ]  ≡⟨ /⊢-cong (var-/⊢⋆-⇒-var-/⊢⋆-↑⁺⋆ hyp Γ⁺ x) (P.refl {x = [ wk₁ ]}) ⟩
      [ var₂ · x     /⊢⋆ ρs₂ ↑⁺⋆₁ Γ⁺ /⊢ wk₁ ]  ≡⟨ P.sym $ suc-/⊢⋆-↑⋆ σ x (ρs₂ ↑⁺⋆₁ Γ⁺) ⟩
      [ var₂ · suc x /⊢⋆ ρs₂ ↑⁺⋆₁ (Γ⁺ ▻ σ)  ]  ∎

    -- Variants of var-/⊢⋆-↑⁺⋆-⇒-/⊢⋆-↑⁺⋆ which may be easier to use.

    var-/⊢⋆-⇒-/⊢⋆-↑⁺⋆ :
      ∀ {Γ Δ} {ρ̂ : Γ ⇨̂ Δ} (ρs₁ : Subs T₁ ρ̂) (ρs₂ : Subs T₁ ρ̂) →
      (∀ {σ} (x : Γ ∋ σ) → var₂ · x /⊢⋆ ρs₁ ≅-⊢₂ var₂ · x /⊢⋆ ρs₂) →
      ∀ Γ⁺ {σ} (t : Γ ++⁺ Γ⁺ ⊢₂ σ) →
      t /⊢⋆ ρs₁ ↑⁺⋆₁ Γ⁺ ≅-⊢₂ t /⊢⋆ ρs₂ ↑⁺⋆₁ Γ⁺
    var-/⊢⋆-⇒-/⊢⋆-↑⁺⋆ ρs₁ ρs₂ hyp =
      var-/⊢⋆-↑⁺⋆-⇒-/⊢⋆-↑⁺⋆ ρs₁ ρs₂ (var-/⊢⋆-⇒-var-/⊢⋆-↑⁺⋆ hyp)

    var-/⊢⋆-⇒-/⊢⋆ :
      ∀ {Γ Δ} {ρ̂ : Γ ⇨̂ Δ} (ρs₁ : Subs T₁ ρ̂) (ρs₂ : Subs T₁ ρ̂) →
      (∀ {σ} (x : Γ ∋ σ) → var₂ · x /⊢⋆ ρs₁ ≅-⊢₂ var₂ · x /⊢⋆ ρs₂) →
      ∀ {σ} (t : Γ ⊢₂ σ) → t /⊢⋆ ρs₁ ≅-⊢₂ t /⊢⋆ ρs₂
    var-/⊢⋆-⇒-/⊢⋆ ρs₁ ρs₂ hyp = var-/⊢⋆-⇒-/⊢⋆-↑⁺⋆ ρs₁ ρs₂ hyp ε

    -- The identity substitution has no effect.

    /⊢-id : ∀ {Γ σ} (t : Γ ⊢₂ σ) → t /⊢ id₁ ≅-⊢₂ t
    /⊢-id = var-/⊢⋆-⇒-/⊢⋆ (ε ▻ id₁) ε var-/⊢-id

    -- id is a right identity of _∘_.

    ∘-id : ∀ {Γ Δ} {ρ̂ : Γ ⇨̂ Δ} (ρ : Sub T₂ ρ̂) → ρ ∘ id₁ ≅-⇨ ρ
    ∘-id ρ = extensionality P.refl λ x → begin
        [ x /∋ ρ ∘ id₁  ]  ≡⟨ /∋-∘ x ρ id₁ ⟩
        [ x /∋ ρ /⊢ id₁ ]  ≡⟨ /⊢-id (x /∋ ρ) ⟩
        [ x /∋ ρ        ]  ∎

    -- Lifting distributes over composition.

    ∘-↑ : ∀ {Γ Δ Ε} σ {ρ̂₁ : Γ ⇨̂ Δ} {ρ̂₂ : Δ ⇨̂ Ε}
          (ρ₁ : Sub T₂ ρ̂₁) (ρ₂ : Sub T₁ ρ̂₂) →
          (ρ₁ ∘ ρ₂) ↑₂ σ ≅-⇨ ρ₁ ↑₂ σ ∘ ρ₂ ↑₁
    ∘-↑ σ ρ₁ ρ₂ =
      let ρ₂↑ = ρ₂ ↑₁ (σ / ρ₁)

          lemma₁ = begin
            [ wk-subst₂ (ρ₁ ∘ ρ₂)              ]  ≡⟨ P.refl ⟩
            [ map weaken₂ (map (app ρ₂) ρ₁)    ]  ≡⟨ P.sym $ map-[∘] weaken₂ (app ρ₂) ρ₁ ⟩
            [ map (weaken₂ [∘] app ρ₂) ρ₁      ]  ≡⟨ map-cong-ext₁ P.refl
                                                       (λ t → begin
                                                          [ weaken₂ · (t /⊢ ρ₂) ]  ≡⟨ P.sym $ /⊢-wk (t /⊢ ρ₂) ⟩
                                                          [ t /⊢ ρ₂ /⊢ wk₁      ]  ≡⟨ /⊢-/⊢-wk (σ / ρ₁) t ρ₂ ⟩
                                                          [ t /⊢ wk₁ /⊢ ρ₂↑     ]  ≡⟨ /⊢-cong (/⊢-wk t) P.refl ⟩
                                                          [ weaken₂ · t /⊢ ρ₂↑  ]  ∎)
                                                       (P.refl {x = [ ρ₁ ]}) ⟩
            [ map (app ρ₂↑ [∘] weaken₂) ρ₁     ]  ≡⟨ map-[∘] (app ρ₂↑) weaken₂ ρ₁ ⟩
            [ map (app ρ₂↑) (map (weaken₂) ρ₁) ]  ∎

          lemma₂ = begin
            [ var₂ · zero           ]  ≡⟨ P.sym $ trans-var zero ⟩
            [ trans · (var₁ · zero) ]  ≡⟨ trans-cong (P.sym $ Simple.zero-/∋-↑ simple₁ (σ / ρ₁) ρ₂) ⟩
            [ trans · (zero /∋ ρ₂↑) ]  ≡⟨ P.sym $ var-/⊢ zero ρ₂↑ ⟩
            [ var₂ · zero /⊢ ρ₂↑    ]  ∎

      in begin
      [ (ρ₁ ∘ ρ₂) ↑₂                                                  ]  ≡⟨ Simple.unfold-↑ simple₂ (ρ₁ ∘ ρ₂) ⟩
      [ wk-subst₂ (ρ₁ ∘ ρ₂) ▻ var₂ · zero                             ]  ≡⟨ ▻⇨-cong P.refl lemma₁ lemma₂ ⟩
      [ map (app ρ₂↑) (map weaken₂[ σ / ρ₁ ] ρ₁) ▻ var₂ · zero /⊢ ρ₂↑ ]  ≡⟨ P.sym $
                                                                              map-▻ (app ρ₂↑) (wk-subst₂[ σ / ρ₁ ] ρ₁) (var₂ · zero) ⟩
      [ map (app ρ₂↑) (wk-subst₂[ σ / ρ₁ ] ρ₁ ▻ var₂ · zero)          ]  ≡⟨ map-cong (app ρ₂↑ ∎-⟶)
                                                                                     (P.sym $ Simple.unfold-↑ simple₂ ρ₁) ⟩
      [ map (app ρ₂↑) (ρ₁ ↑₂)                                         ]  ≡⟨ P.refl ⟩
      [ ρ₁ ↑₂ ∘ ρ₂ ↑₁                                                 ]  ∎

    -- N-ary lifting distributes over composition.

    ∘-↑⁺ : ∀ {Γ Δ Ε} {ρ̂₁ : Γ ⇨̂ Δ} {ρ̂₂ : Δ ⇨̂ Ε}
           (ρ₁ : Sub T₂ ρ̂₁) (ρ₂ : Sub T₁ ρ̂₂) Γ⁺ →
           (ρ₁ ∘ ρ₂) ↑⁺₂ Γ⁺ ≅-⇨ ρ₁ ↑⁺₂ Γ⁺ ∘ ρ₂ ↑⁺₁ (Γ⁺ /⁺ ρ₁)
    ∘-↑⁺ ρ₁ ρ₂ ε        = P.refl
    ∘-↑⁺ ρ₁ ρ₂ (Γ⁺ ▻ σ) = begin
      [ ((ρ₁ ∘ ρ₂) ↑⁺₂ Γ⁺) ↑₂                   ]  ≡⟨ Simple.↑-cong simple₂ (∘-↑⁺ ρ₁ ρ₂ Γ⁺) P.refl ⟩
      [ (ρ₁ ↑⁺₂ Γ⁺ ∘ ρ₂ ↑⁺₁ (Γ⁺ /⁺ ρ₁)) ↑₂      ]  ≡⟨ ∘-↑ σ (ρ₁ ↑⁺₂ Γ⁺) (ρ₂ ↑⁺₁ (Γ⁺ /⁺ ρ₁)) ⟩
      [ (ρ₁ ↑⁺₂ Γ⁺) ↑₂ ∘ (ρ₂ ↑⁺₁ (Γ⁺ /⁺ ρ₁)) ↑₁ ]  ∎

    ∘-↑₊ : ∀ {Γ Δ Ε} {ρ̂₁ : Γ ⇨̂ Δ} {ρ̂₂ : Δ ⇨̂ Ε}
           (ρ₁ : Sub T₂ ρ̂₁) (ρ₂ : Sub T₁ ρ̂₂) Γ₊ →
           (ρ₁ ∘ ρ₂) ↑₊₂ Γ₊ ≅-⇨ ρ₁ ↑₊₂ Γ₊ ∘ ρ₂ ↑₊₁ (Γ₊ /₊ ρ₁)
    ∘-↑₊ ρ₁ ρ₂ ε        = P.refl
    ∘-↑₊ ρ₁ ρ₂ (σ ◅ Γ₊) = begin
      [ (ρ₁             ∘ ρ₂   ) ↑₂ σ ↑₊₂ Γ₊      ]  ≡⟨ Simple.↑₊-cong simple₂ (∘-↑ σ ρ₁ ρ₂) (P.refl {x = [ Γ₊ ]}) ⟩
      [ (ρ₁ ↑₂ σ        ∘ ρ₂ ↑₁)      ↑₊₂ Γ₊      ]  ≡⟨ ∘-↑₊ (ρ₁ ↑₂ σ) (ρ₂ ↑₁) Γ₊ ⟩
      [ ρ₁ ↑₊₂ (σ ◅ Γ₊) ∘ ρ₂ ↑₊₁ ((σ ◅ Γ₊) /₊ ρ₁) ]  ∎

    -- First weakening and then substituting something for the first
    -- variable is equivalent to doing nothing.

    /⊢-wk-/⊢-sub : ∀ {Γ σ τ} (t : Γ ⊢₂ τ) (t′ : Γ ⊢₁ σ) →
                   t /⊢ wk₁ /⊢ sub₁ t′ ≅-⊢₂ t
    /⊢-wk-/⊢-sub t t′ = var-/⊢⋆-⇒-/⊢⋆ (ε ▻ wk₁ ▻ sub₁ t′) ε (λ x → begin
      [ var₂ · x /⊢ wk₁ /⊢ sub₁ t′ ]  ≡⟨ /⊢-cong (/∋-≅-⊢-var x wk₁ (Simple./∋-wk simple₁ x)) P.refl ⟩
      [ var₂ · suc x /⊢ sub₁ t′    ]  ≡⟨ suc-/⊢-sub x t′ ⟩
      [ var₂ · x                   ]  ∎) t

    -- Weakening a substitution and composing with sub is the same as
    -- doing nothing.

    wk-subst-∘-sub : ∀ {Γ Δ σ} {ρ̂ : Γ ⇨̂ Δ} (ρ : Sub T₂ ρ̂) (t : Δ ⊢₁ σ) →
                     wk-subst₂ ρ ∘ sub₁ t ≅-⇨ ρ
    wk-subst-∘-sub ρ t = extensionality P.refl λ x →
      let lemma = begin
            [ x /∋ wk-subst₂ ρ   ]  ≡⟨ Simple./∋-wk-subst simple₂ x ρ ⟩
            [ weaken₂ · (x /∋ ρ) ]  ≡⟨ P.sym $ /⊢-wk (x /∋ ρ) ⟩
            [ x /∋ ρ /⊢ wk₁      ]  ∎
      in begin
        [ x /∋ wk-subst₂ ρ ∘ sub₁ t    ]  ≡⟨ /∋-∘ x (wk-subst₂ ρ) (sub₁ t) ⟩
        [ x /∋ wk-subst₂ ρ /⊢ sub₁ t   ]  ≡⟨ /⊢-cong lemma P.refl ⟩
        [ x /∋ ρ /⊢ wk₁ /⊢ sub₁ t      ]  ≡⟨ /⊢-wk-/⊢-sub (x /∋ ρ) t ⟩
        [ x /∋ ρ                       ]  ∎
