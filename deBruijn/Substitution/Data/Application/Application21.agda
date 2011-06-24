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
import Relation.Binary.PropositionalEquality as P

open Context Uni
open P.≡-Reasoning
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

  open Term-like T₁ using () renaming (_⊢_ to _⊢₁_; _≅-⊢_ to _≅-⊢₁_)
  open Term-like T₂ using ([_]) renaming (_⊢_ to _⊢₂_; _≅-⊢_ to _≅-⊢₂_)
  open Simple simple₁
    using ()
    renaming ( id to id₁; sub to sub₁; var to var₁
             ; weaken to weaken₁; wk to wk₁; wk-subst to wk-subst₁
             ; _↑ to _↑₁; _↑_ to _↑₁_; _↑⁺_ to _↑⁺₁_
             ; _↑⋆_ to _↑⋆₁_; _↑⁺⋆_ to _↑⁺⋆₁_
             )
  open Simple simple₂
    using ()
    renaming ( id to id₂; var to var₂
             ; weaken to weaken₂; wk to wk₂; wk-subst to wk-subst₂
             ; _↑ to _↑₂; _↑_ to _↑₂_
             )

  field
    application : Application T₁ T₂

  open Application application

  field
    -- The two weakening functions coincide.
    trans-weaken : ∀ {Γ σ τ} (t : Γ ⊢₁ τ) →
                   trans · (weaken₁ {σ = σ} · t) ≅-⊢₂
                   weaken₂ {σ = σ} · (trans · t)

    -- The two variable inclusion functions coincide.
    trans-var : ∀ {Γ σ} (x : Γ ∋ σ) → trans · (var₁ · x) ≅-⊢₂ var₂ · x

    -- _/⊢_ and _/∋₁_ coincide for variables.
    var-/⊢ : ∀ {Γ Δ σ} {ρ̂ : Γ ⇨̂ Δ} (x : Γ ∋ σ) (ρ : Sub T₁ ρ̂) →
             var₂ · x /⊢ ρ ≅-⊢₂ trans · (x /∋ ρ)

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
               t₁ ≅-⊢₁ t₂ → trans · t₁ ≅-⊢₂ trans · t₂
  trans-cong P.refl = P.refl

  app∋⋆-cong : ∀ {Γ₁ Δ₁} {ρ̂₁ : Γ₁ ⇨̂ Δ₁} {ρs₁ : Subs T₁ ρ̂₁}
                 {Γ₂ Δ₂} {ρ̂₂ : Γ₂ ⇨̂ Δ₂} {ρs₂ : Subs T₁ ρ̂₂} →
               ρs₁ ≅-⇨⋆ ρs₂ → app∋⋆ ρs₁ ≅-⟶ app∋⋆ ρs₂
  app∋⋆-cong P.refl = P.refl

  /∋⋆-cong :
    ∀ {Γ₁ Δ₁ σ₁} {x₁ : Γ₁ ∋ σ₁} {ρ̂₁ : Γ₁ ⇨̂ Δ₁} {ρs₁ : Subs T₁ ρ̂₁}
      {Γ₂ Δ₂ σ₂} {x₂ : Γ₂ ∋ σ₂} {ρ̂₂ : Γ₂ ⇨̂ Δ₂} {ρs₂ : Subs T₁ ρ̂₂} →
    x₁ ≅-∋ x₂ → ρs₁ ≅-⇨⋆ ρs₂ → x₁ /∋⋆ ρs₁ ≅-⊢₂ x₂ /∋⋆ ρs₂
  /∋⋆-cong P.refl P.refl = P.refl

  ∘⋆-cong : ∀ {Γ₁ Δ₁} {ρ̂₁ : Γ₁ ⇨̂ Δ₁} {ρs₁ : Subs T₁ ρ̂₁}
              {Γ₂ Δ₂} {ρ̂₂ : Γ₂ ⇨̂ Δ₂} {ρs₂ : Subs T₁ ρ̂₂} →
            ρs₁ ≅-⇨⋆ ρs₂ → ∘⋆ ρs₁ ≅-⇨ ∘⋆ ρs₂
  ∘⋆-cong P.refl = P.refl

  abstract

    -- Applying a composed substitution to a variable is equivalent to
    -- applying all the substitutions one after another.
    --
    -- TODO: Remove this lemma?

    /∋-∘⋆ : ∀ {Γ Δ σ} {ρ̂ : Γ ⇨̂ Δ} (x : Γ ∋ σ) (ρs : Subs T₁ ρ̂) →
            x /∋ ∘⋆ ρs ≅-⊢₂ var₂ · x /⊢⋆ ρs
    /∋-∘⋆ x ε = begin
      [ x /∋ id₂ ]  ≡⟨ Simple./∋-id simple₂ x ⟩
      [ var₂ · x ]  ∎
    /∋-∘⋆ x (ρs ▻ ρ) = begin
      [ x /∋ ∘⋆ ρs ∘ ρ       ]  ≡⟨ /∋-∘ x (∘⋆ ρs) ρ ⟩
      [ x /∋ ∘⋆ ρs /⊢ ρ      ]  ≡⟨ /⊢-cong (/∋-∘⋆ x ρs) P.refl ⟩
      [ var₂ · x /⊢⋆ ρs /⊢ ρ ]  ∎

    -- x /∋⋆ ρs is synonymous with var₂ · x /⊢⋆ ρs.
    --
    -- TODO: Remove?

    var-/⊢⋆ : ∀ {Γ Δ σ} {ρ̂ : Γ ⇨̂ Δ} (x : Γ ∋ σ) (ρs : Subs T₁ ρ̂) →
              var₂ · x /⊢⋆ ρs ≅-⊢₂ x /∋⋆ ρs
    var-/⊢⋆ x ε       = P.refl
    var-/⊢⋆ x (ε ▻ ρ) = begin
      [ var₂ · x /⊢ ρ    ]  ≡⟨ var-/⊢ x ρ ⟩
      [ trans · (x /∋ ρ) ]  ∎
    var-/⊢⋆ x (ρs ▻ ρ₁ ▻ ρ₂) = begin
      [ var₂ · x /⊢⋆ (ρs ▻ ρ₁) /⊢ ρ₂ ]  ≡⟨ /⊢-cong (var-/⊢⋆ x (ρs ▻ ρ₁)) P.refl ⟩
      [ x /∋⋆ (ρs ▻ ρ₁) /⊢ ρ₂        ]  ∎

    -- A helper lemma.

    /∋-≅-⊢-var : ∀ {Γ Δ σ} {ρ̂ : Γ ⇨̂ Δ}
                 (x : Γ ∋ σ) (ρ : Sub T₁ ρ̂) {y : Δ ∋ σ / ρ} →
                 x /∋ ρ ≅-⊢₁ var₁ · y →
                 var₂ · x /⊢ ρ ≅-⊢₂ var₂ · y
    /∋-≅-⊢-var x ρ {y} hyp = begin
      [ var₂ · x /⊢ ρ      ]  ≡⟨ var-/⊢ x ρ ⟩
      [ trans · (x /∋ ρ)   ]  ≡⟨ trans-cong hyp ⟩
      [ trans · (var₁ · y) ]  ≡⟨ trans-var y ⟩
      [ var₂ · y           ]  ∎

    -- A variant of /∋-id.

    var-/⊢-id : ∀ {Γ σ} (x : Γ ∋ σ) → var₂ · x /⊢ id₁ ≅-⊢₂ var₂ · x
    var-/⊢-id x = /∋-≅-⊢-var x id₁ (Simple./∋-id simple₁ x)

    -- A variant of /∋-wk-↑⁺.

    var-/⊢-wk-↑⁺ : ∀ {Γ σ} Γ⁺ {τ} (x : Γ ++ Γ⁺ ∋ τ) →
                   var₂ · x /⊢ wk₁ {σ = σ} ↑⁺₁ Γ⁺ ≅-⊢₂
                   var₂ · (lift (weaken∋ {σ = σ}) Γ⁺ · x)
    var-/⊢-wk-↑⁺ Γ⁺ x =
      /∋-≅-⊢-var x (wk₁ ↑⁺₁ Γ⁺) (Simple./∋-wk-↑⁺ simple₁ Γ⁺ x)

    -- A variant of /∋-wk-↑⁺-↑⁺.

    var-/⊢-wk-↑⁺-↑⁺ : ∀ {Γ σ} Γ⁺ Γ⁺⁺ {τ} (x : Γ ++ Γ⁺ ++ Γ⁺⁺ ∋ τ) →
                      var₂ · x /⊢ wk₁ {σ = σ} ↑⁺₁ Γ⁺ ↑⁺₁ Γ⁺⁺ ≅-⊢₂
                      var₂ · (lift (lift (weaken∋ {σ = σ}) Γ⁺) Γ⁺⁺ · x)
    var-/⊢-wk-↑⁺-↑⁺ Γ⁺ Γ⁺⁺ x =
      /∋-≅-⊢-var x (wk₁ ↑⁺₁ Γ⁺ ↑⁺₁ Γ⁺⁺)
                 (Simple./∋-wk-↑⁺-↑⁺ simple₁ Γ⁺ Γ⁺⁺ x)

    -- Variants of zero-/∋-↑.

    zero-/⊢-↑ : ∀ {Γ Δ} {ρ̂ : Γ ⇨̂ Δ} σ (ρ : Sub T₁ ρ̂) →
                var₂ · zero /⊢ ρ ↑₁ σ ≅-⊢₂ var₂ · zero {σ = σ / ρ}
    zero-/⊢-↑ σ ρ =
      /∋-≅-⊢-var zero (ρ ↑₁ σ) (Simple.zero-/∋-↑ simple₁ σ ρ)

    zero-/⊢⋆-↑⋆ : ∀ {Γ Δ} {ρ̂ : Γ ⇨̂ Δ} σ (ρs : Subs T₁ ρ̂) →
                  var₂ · zero /⊢⋆ ρs ↑⋆₁ σ ≅-⊢₂
                  var₂ · zero {σ = σ /⋆ ρs}
    zero-/⊢⋆-↑⋆ σ ε        = P.refl
    zero-/⊢⋆-↑⋆ σ (ρs ▻ ρ) = begin
      [ var₂ · zero /⊢⋆ ρs ↑⋆₁ σ /⊢ ρ ↑₁ ]  ≡⟨ /⊢-cong (zero-/⊢⋆-↑⋆ σ ρs) (P.refl {x = [ ρ ↑₁ (σ /⋆ ρs) ]}) ⟩
      [ var₂ · zero /⊢ ρ ↑₁ (σ /⋆ ρs)    ]  ≡⟨ zero-/⊢-↑ (σ /⋆ ρs) ρ ⟩
      [ var₂ · zero                      ]  ∎

    -- A corollary of ε-↑⁺⋆.

    /⊢⋆-ε-↑⁺⋆ : ∀ {Γ} Γ⁺ {σ} (t : Γ ++ Γ⁺ ⊢₂ σ) →
                t /⊢⋆ ε ↑⁺⋆₁ Γ⁺ ≅-⊢₂ t
    /⊢⋆-ε-↑⁺⋆ Γ⁺ t = begin
      [ t /⊢⋆ ε ↑⁺⋆₁ Γ⁺ ]  ≡⟨ /⊢⋆-cong (P.refl {x = [ t ]}) (Simple.ε-↑⁺⋆ simple₁ Γ⁺) ⟩
      [ t /⊢⋆ ε         ]  ≡⟨ P.refl ⟩
      [ t               ]  ∎

    -- A corollary of ▻-↑⁺⋆.

    /⊢⋆-▻-↑⁺⋆ :
      ∀ {Γ Δ Ε} {ρ̂₁ : Γ ⇨̂ Δ} {ρ̂₂ : Δ ⇨̂ Ε} Γ⁺ {σ}
      (t : Γ ++ Γ⁺ ⊢₂ σ) (ρs : Subs T₁ ρ̂₁) (ρ : Sub T₁ ρ̂₂) →
      t /⊢⋆ (ρs ▻ ρ) ↑⁺⋆₁ Γ⁺ ≅-⊢₂ t /⊢⋆ ρs ↑⁺⋆₁ Γ⁺ /⊢ ρ ↑⁺₁ (Γ⁺ /⁺⋆ ρs)
    /⊢⋆-▻-↑⁺⋆ Γ⁺ t ρs ρ =
      /⊢⋆-cong (P.refl {x = [ t ]}) (Simple.▻-↑⁺⋆ simple₁ ρs ρ Γ⁺)

    -- A corollary of ε-↑⁺⋆ and ▻-↑⁺⋆.

    /⊢⋆-ε-▻-↑⁺⋆ : ∀ {Γ Δ} {ρ̂ : Γ ⇨̂ Δ} Γ⁺ {σ}
                  (t : Γ ++ Γ⁺ ⊢₂ σ) (ρ : Sub T₁ ρ̂) →
                  t /⊢⋆ (ε ▻ ρ) ↑⁺⋆₁ Γ⁺ ≅-⊢₂ t /⊢ ρ ↑⁺₁ Γ⁺
    /⊢⋆-ε-▻-↑⁺⋆ Γ⁺ t ρ = begin
      [ t /⊢⋆ (ε ▻ ρ) ↑⁺⋆₁ Γ⁺               ]  ≡⟨ /⊢⋆-cong (P.refl {x = [ t ]}) (Simple.▻-↑⁺⋆ simple₁ ε ρ Γ⁺) ⟩
      [ t /⊢⋆ ε ↑⁺⋆₁ Γ⁺ /⊢ ρ ↑⁺₁ (Γ⁺ /̂⁺ îd) ]  ≡⟨ /⊢-cong (/⊢⋆-ε-↑⁺⋆ Γ⁺ t) (Simple.↑⁺-cong simple₁ P.refl (/̂⁺-îd Γ⁺)) ⟩
      [ t               /⊢ ρ ↑⁺₁ Γ⁺         ]  ∎

    -- Another corollary of ε-↑⁺⋆ and ▻-↑⁺⋆.

    /⊢⋆-ε-▻-▻-↑⁺⋆ :
      ∀ {Γ Δ Ε} {ρ̂₁ : Γ ⇨̂ Δ} {ρ̂₂ : Δ ⇨̂ Ε} Γ⁺ {σ}
      (t : Γ ++ Γ⁺ ⊢₂ σ) (ρ₁ : Sub T₁ ρ̂₁) (ρ₂ : Sub T₁ ρ̂₂) →
      t /⊢⋆ (ε ▻ ρ₁ ▻ ρ₂) ↑⁺⋆₁ Γ⁺ ≅-⊢₂
      t /⊢ ρ₁ ↑⁺₁ Γ⁺ /⊢ ρ₂ ↑⁺₁ (Γ⁺ /⁺ ρ₁)
    /⊢⋆-ε-▻-▻-↑⁺⋆ Γ⁺ t ρ₁ ρ₂ = begin
      [ t /⊢⋆ (ε ▻ ρ₁ ▻ ρ₂) ↑⁺⋆₁ Γ⁺                 ]  ≡⟨ /⊢⋆-cong (P.refl {x = [ t ]}) (Simple.▻-↑⁺⋆ simple₁ (ε ▻ ρ₁) ρ₂ Γ⁺) ⟩
      [ t /⊢⋆ (ε ▻ ρ₁) ↑⁺⋆₁ Γ⁺ /⊢ ρ₂ ↑⁺₁ (Γ⁺ /⁺ ρ₁) ]  ≡⟨ /⊢-cong (/⊢⋆-ε-▻-↑⁺⋆ Γ⁺ t ρ₁) P.refl ⟩
      [ t /⊢ ρ₁ ↑⁺₁ Γ⁺ /⊢ ρ₂ ↑⁺₁ (Γ⁺ /⁺ ρ₁)         ]  ∎

    -- Application of sub cancels one occurrence of suc.

    suc-/⊢-sub : ∀ {Γ σ τ} (x : Γ ∋ σ) (t : Γ ⊢₁ τ) →
                 var₂ · suc x /⊢ sub₁ t ≅-⊢₂ var₂ · x
    suc-/⊢-sub x t = begin
      [ var₂ · suc x /⊢ sub₁ t    ]  ≡⟨ var-/⊢ (suc x) (sub₁ t) ⟩
      [ trans · (suc x /∋ sub₁ t) ]  ≡⟨ P.refl ⟩
      [ trans · (x /∋ id₁)        ]  ≡⟨ trans-cong (Simple./∋-id simple₁ x) ⟩
      [ trans · (var₁ · x)        ]  ≡⟨ trans-var x ⟩
      [ var₂ · x                  ]  ∎

    -- First weakening and then substituting something for the first
    -- variable is equivalent to doing nothing.

    wk-∘-sub : ∀ {Γ σ} (t : Γ ⊢₁ σ) → wk₂ ∘ sub₁ t ≅-⇨ id₂ {Γ = Γ}
    wk-∘-sub t = extensionality P.refl λ x → begin
      [ x /∋ wk₂ ∘ sub₁ t      ]  ≡⟨ /∋-∘ x wk₂ (sub₁ t) ⟩
      [ x /∋ wk₂ /⊢ sub₁ t     ]  ≡⟨ /⊢-cong (Simple./∋-wk simple₂ x) P.refl ⟩
      [ var₂ · suc x /⊢ sub₁ t ]  ≡⟨ suc-/⊢-sub x t ⟩
      [ var₂ · x               ]  ≡⟨ P.sym $ Simple./∋-id simple₂ x ⟩
      [ x /∋ id₂               ]  ∎

    -- id is a left identity of _∘_ (more or less).

    id-∘ : ∀ {Γ Δ} {ρ̂ : Γ ⇨̂ Δ} (ρ : Sub T₁ ρ̂) → id₂ ∘ ρ ≅-⇨ map trans ρ
    id-∘ ρ = extensionality P.refl λ x → begin
      [ x /∋ id₂ ∘ ρ     ]  ≡⟨ /∋-∘ x id₂ ρ ⟩
      [ x /∋ id₂ /⊢ ρ    ]  ≡⟨ /⊢-cong (Simple./∋-id simple₂ x) (P.refl {x = [ ρ ]}) ⟩
      [ var₂ · x /⊢ ρ    ]  ≡⟨ var-/⊢ x ρ ⟩
      [ trans · (x /∋ ρ) ]  ≡⟨ P.sym $ /∋-map x trans ρ ⟩
      [ x /∋ map trans ρ ]  ∎

    -- One can translate a substitution either before or after
    -- weakening it.

    map-trans-wk-subst : ∀ {Γ Δ σ} {ρ̂ : Γ ⇨̂ Δ} (ρ : Sub T₁ ρ̂) →
                         map trans (wk-subst₁ {σ = σ} ρ) ≅-⇨
                         wk-subst₂ {σ = σ} (map trans ρ)
    map-trans-wk-subst {σ = σ} ρ = begin
      [ map trans (wk-subst₁ {σ = σ} ρ)   ]  ≡⟨ P.sym $ map-[∘] trans (weaken₁ {σ = σ}) ρ ⟩
      [ map (trans [∘] weaken₁ {σ = σ}) ρ ]  ≡⟨ map-cong-ext₁ P.refl trans-weaken (P.refl {x = [ ρ ]}) ⟩
      [ map (weaken₂ [∘] trans) ρ         ]  ≡⟨ map-[∘] weaken₂ trans ρ ⟩
      [ wk-subst₂ (map trans ρ)           ]  ∎

    -- One can translate a substitution either before or after lifting
    -- it.

    map-trans-↑ : ∀ {Γ Δ σ} {ρ̂ : Γ ⇨̂ Δ} (ρ : Sub T₁ ρ̂) →
                  map trans (ρ ↑₁ σ) ≅-⇨ map trans ρ ↑₂ σ
    map-trans-↑ {σ = σ} ρ = begin
      [ map trans (ρ ↑₁ σ)                                          ]  ≡⟨ map-cong (P.refl {x = [ trans ]})
                                                                                   (Simple.unfold-↑ simple₁ ρ) ⟩
      [ map trans (wk-subst₁ {σ = σ / ρ} ρ ▻ var₁ · zero)           ]  ≡⟨ map-▻ trans (wk-subst₁ ρ) _ ⟩
      [ map trans (wk-subst₁ {σ = σ / ρ} ρ) ▻ trans · (var₁ · zero) ]  ≡⟨ ▻⇨-cong P.refl (map-trans-wk-subst ρ) (trans-var zero) ⟩
      [ wk-subst₂ (map trans ρ) ▻ var₂ · zero                       ]  ≡⟨ P.sym $ Simple.unfold-↑ simple₂ (map trans ρ) ⟩
      [ map trans ρ ↑₂                                              ]  ∎

  open Application application public
