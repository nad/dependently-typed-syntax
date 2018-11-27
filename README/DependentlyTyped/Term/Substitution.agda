------------------------------------------------------------------------
-- Application of substitutions to terms
------------------------------------------------------------------------

import Level
open import Universe

module README.DependentlyTyped.Term.Substitution
  (Uni₀ : Universe Level.zero Level.zero) where

open import Data.Product as Prod renaming (curry to c; uncurry to uc)
open import deBruijn.Substitution.Data
open import Function as F using (_$_; _ˢ_) renaming (const to k)
import README.DependentlyTyped.Term as Term; open Term Uni₀
import Relation.Binary.PropositionalEquality as P

open P.≡-Reasoning

-- Code for applying substitutions.
--
-- Note that the _↦_ record ensures that we already have access to
-- operations such as lifting.

module Apply {T : Term-like Level.zero} (T↦Tm : T ↦ Tm) where

  open _↦_ T↦Tm hiding (var)

  mutual

    infixl 8 _/⊢_ _/⊢-lemma_

    -- Applies a substitution to a term. TODO: Generalise and allow
    -- the codomain to be any suitable applicative structure?

    _/⊢_ : ∀ {Γ Δ σ} {ρ̂ : Γ ⇨̂ Δ} → Γ ⊢ σ → Sub T ρ̂ → Δ ⊢ σ /̂ ρ̂
    var x             /⊢ ρ = trans ⊙ (x /∋ ρ)
    ƛ t               /⊢ ρ = ƛ (t /⊢ ρ ↑)
    _·_ {σ = σ} t₁ t₂ /⊢ ρ =
      P.subst (λ v → _ ⊢ snd σ /̂ ⟦ ρ ⟧⇨ ↑̂ /̂ ŝub v)
              (≅-Value-⇒-≡ $ P.sym $ t₂ /⊢-lemma ρ)
              ((t₁ /⊢ ρ) · (t₂ /⊢ ρ))

    abstract

      -- An unfolding lemma.

      ·-/⊢ : ∀ {Γ Δ sp₁ sp₂ σ} {ρ̂ : Γ ⇨̂ Δ}
             (t₁ : Γ ⊢ π sp₁ sp₂ , σ) (t₂ : Γ ⊢ fst σ) (ρ : Sub T ρ̂) →
             t₁ · t₂ /⊢ ρ ≅-⊢ (t₁ /⊢ ρ) · (t₂ /⊢ ρ)
      ·-/⊢ {σ = σ} t₁ t₂ ρ =
        drop-subst-⊢ (λ v → snd σ /̂ ⟦ ρ ⟧⇨ ↑̂ /̂ ŝub v)
                     (≅-Value-⇒-≡ $ P.sym $ t₂ /⊢-lemma ρ)

      -- The application operation is well-behaved.

      _/⊢-lemma_ : ∀ {Γ Δ σ} {ρ̂ : Γ ⇨̂ Δ} (t : Γ ⊢ σ) (ρ : Sub T ρ̂) →
                   ⟦ t ⟧ /Val ρ ≅-Value ⟦ t /⊢ ρ ⟧
      var x /⊢-lemma ρ = /̂∋-⟦⟧⇨ x ρ
      ƛ t   /⊢-lemma ρ = begin
        [ c ⟦ t ⟧ /Val ρ     ]  ≡⟨ P.refl ⟩
        [ c (⟦ t ⟧ /Val ρ ↑) ]  ≡⟨ curry-cong (t /⊢-lemma (ρ ↑)) ⟩
        [ c ⟦ t /⊢ ρ ↑ ⟧     ]  ∎
      t₁ · t₂ /⊢-lemma ρ = begin
        [ ⟦ t₁ · t₂ ⟧ /Val ρ                ]  ≡⟨ P.refl ⟩
        [ (⟦ t₁ ⟧ /Val ρ) ˢ (⟦ t₂ ⟧ /Val ρ) ]  ≡⟨ ˢ-cong (t₁ /⊢-lemma ρ) (t₂ /⊢-lemma ρ) ⟩
        [ ⟦ t₁ /⊢ ρ ⟧ ˢ ⟦ t₂ /⊢ ρ ⟧         ]  ≡⟨ P.refl ⟩
        [ ⟦ (t₁ /⊢ ρ) · (t₂ /⊢ ρ) ⟧         ]  ≡⟨ ⟦⟧-cong (P.sym $ ·-/⊢ t₁ t₂ ρ) ⟩
        [ ⟦ t₁ · t₂ /⊢ ρ ⟧                  ]  ∎

  app : ∀ {Γ Δ} {ρ̂ : Γ ⇨̂ Δ} → Sub T ρ̂ → [ Tm ⟶ Tm ] ρ̂
  app ρ = record
    { function    = λ _ t → t /⊢ ρ
    ; corresponds = λ _ t → t /⊢-lemma ρ
    }

  -- Application of substitutions to syntactic types. TODO: Remove?

  infixl 8 _/⊢t_ _/⊢t⋆_

  _/⊢t_ : ∀ {Γ Δ σ} {ρ̂ : Γ ⇨̂ Δ} → Γ ⊢ σ type → Sub T ρ̂ → Δ ⊢ σ /̂ ρ̂ type
  ⋆       /⊢t ρ = ⋆
  el t    /⊢t ρ = P.subst (λ v → _ ⊢ -, k U-el ˢ v type)
                          (≅-Value-⇒-≡ $ P.sym $ t /⊢-lemma ρ) $
                    el (t /⊢ ρ)
  π σ′ τ′ /⊢t ρ = π (σ′ /⊢t ρ) (τ′ /⊢t ρ ↑)

  _/⊢t⋆_ : ∀ {Γ Δ σ} {ρ̂ : Γ ⇨̂ Δ} →
           Γ ⊢ σ type → Subs T ρ̂ → Δ ⊢ σ /̂ ρ̂ type
  σ′ /⊢t⋆ ε        = σ′
  σ′ /⊢t⋆ (ρs ▻ ρ) = σ′ /⊢t⋆ ρs /⊢t ρ

  -- Congruence lemmas.

  /⊢t-cong :
    ∀ {Γ₁ Δ₁ σ₁} {σ′₁ : Γ₁ ⊢ σ₁ type} {ρ̂₁ : Γ₁ ⇨̂ Δ₁} {ρ₁ : Sub T ρ̂₁}
      {Γ₂ Δ₂ σ₂} {σ′₂ : Γ₂ ⊢ σ₂ type} {ρ̂₂ : Γ₂ ⇨̂ Δ₂} {ρ₂ : Sub T ρ̂₂} →
    σ′₁ ≅-type σ′₂ → ρ₁ ≅-⇨ ρ₂ → σ′₁ /⊢t ρ₁ ≅-type σ′₂ /⊢t ρ₂
  /⊢t-cong P.refl P.refl = P.refl

  /⊢t⋆-cong :
    ∀ {Γ₁ Δ₁ σ₁} {σ′₁ : Γ₁ ⊢ σ₁ type} {ρ̂₁ : Γ₁ ⇨̂ Δ₁} {ρs₁ : Subs T ρ̂₁}
      {Γ₂ Δ₂ σ₂} {σ′₂ : Γ₂ ⊢ σ₂ type} {ρ̂₂ : Γ₂ ⇨̂ Δ₂} {ρs₂ : Subs T ρ̂₂} →
    σ′₁ ≅-type σ′₂ → ρs₁ ≅-⇨⋆ ρs₂ → σ′₁ /⊢t⋆ ρs₁ ≅-type σ′₂ /⊢t⋆ ρs₂
  /⊢t⋆-cong P.refl P.refl = P.refl

substitution₁ : Substitution₁ Tm
substitution₁ = record
  { var      = record { function    = λ _ → var
                      ; corresponds = λ _ _ → P.refl
                      }
  ; app′     = Apply.app
  ; app′-var = λ _ _ _ → P.refl
  }

open Substitution₁ substitution₁ hiding (var)

-- Some unfolding lemmas.

module Unfolding-lemmas
  {T : Term-like Level.zero}
  (T↦Tm : Translation-from T)
  where

  open Translation-from T↦Tm
  open Apply translation hiding (_/⊢_; app)

  abstract

    ƛ-/⊢⋆ : ∀ {Γ Δ σ τ} {ρ̂ : Γ ⇨̂ Δ} (t : Γ ▻ σ ⊢ τ) (ρs : Subs T ρ̂) →
            ƛ t /⊢⋆ ρs ≅-⊢ ƛ (t /⊢⋆ ρs ↑⋆)
    ƛ-/⊢⋆ t ε        = P.refl
    ƛ-/⊢⋆ t (ρs ▻ ρ) = begin
      [ ƛ t /⊢⋆ ρs /⊢ ρ       ]  ≡⟨ /⊢-cong (ƛ-/⊢⋆ t ρs) (P.refl {x = [ ρ ]}) ⟩
      [ ƛ (t /⊢⋆ ρs ↑⋆) /⊢ ρ  ]  ≡⟨ P.refl ⟩
      [ ƛ (t /⊢⋆ (ρs ▻ ρ) ↑⋆) ]  ∎

    ·-/⊢⋆ : ∀ {Γ Δ} {ρ̂ : Γ ⇨̂ Δ} {sp₁ sp₂ σ}
            (t₁ : Γ ⊢ π sp₁ sp₂ , σ) (t₂ : Γ ⊢ fst σ) (ρs : Subs T ρ̂) →
            t₁ · t₂ /⊢⋆ ρs ≅-⊢ (t₁ /⊢⋆ ρs) · (t₂ /⊢⋆ ρs)
    ·-/⊢⋆ t₁ t₂ ε        = P.refl
    ·-/⊢⋆ t₁ t₂ (ρs ▻ ρ) = begin
        [ t₁ · t₂ /⊢⋆ ρs /⊢ ρ                   ]  ≡⟨ /⊢-cong (·-/⊢⋆ t₁ t₂ ρs) P.refl ⟩
        [ (t₁ /⊢⋆ ρs) · (t₂ /⊢⋆ ρs) /⊢ ρ        ]  ≡⟨ ·-/⊢ (t₁ /⊢⋆ ρs) (t₂ /⊢⋆ ρs) ρ ⟩
        [ (t₁ /⊢⋆ (ρs ▻ ρ)) · (t₂ /⊢⋆ (ρs ▻ ρ)) ]  ∎

    -- TODO: Remove the following lemmas?

    ⋆-/⊢t⋆ : ∀ {Γ Δ} {ρ̂ : Γ ⇨̂ Δ} (ρs : Subs T ρ̂) →
             ⋆ /⊢t⋆ ρs ≅-type ⋆ {Γ = Δ}
    ⋆-/⊢t⋆ ε        = P.refl
    ⋆-/⊢t⋆ (ρs ▻ ρ) = begin
      [ ⋆ /⊢t⋆ ρs /⊢t ρ ]  ≡⟨ /⊢t-cong (⋆-/⊢t⋆ ρs) (P.refl {x = [ ρ ]}) ⟩
      [ ⋆ /⊢t ρ         ]  ≡⟨ P.refl ⟩
      [ ⋆               ]  ∎

    el-/⊢t : ∀ {Γ Δ} {ρ̂ : Γ ⇨̂ Δ} (t : Γ ⊢ -, k U-⋆) (ρ : Sub T ρ̂) →
             el t /⊢t ρ ≅-type el (t /⊢ ρ)
    el-/⊢t t ρ =
      drop-subst-⊢-type (λ v → -, k U-el ˢ v)
                        (≅-Value-⇒-≡ $ P.sym $ t /⊢-lemma ρ)

    el-/⊢t⋆ : ∀ {Γ Δ} {ρ̂ : Γ ⇨̂ Δ} (t : Γ ⊢ -, k U-⋆) (ρs : Subs T ρ̂) →
              el t /⊢t⋆ ρs ≅-type el (t /⊢⋆ ρs)
    el-/⊢t⋆ t ε        = P.refl
    el-/⊢t⋆ t (ρs ▻ ρ) = begin
      [ el t /⊢t⋆ ρs /⊢t ρ  ]  ≡⟨ /⊢t-cong (el-/⊢t⋆ t ρs) (P.refl {x = [ ρ ]}) ⟩
      [ el (t /⊢⋆ ρs) /⊢t ρ ]  ≡⟨ el-/⊢t (t /⊢⋆ ρs) ρ ⟩
      [ el (t /⊢⋆ ρs /⊢ ρ)  ]  ∎

    π-/⊢t⋆ : ∀ {Γ Δ σ τ} {ρ̂ : Γ ⇨̂ Δ}
             (σ′ : Γ ⊢ σ type) (τ′ : Γ ▻ σ ⊢ τ type) (ρs : Subs T ρ̂) →
             π σ′ τ′ /⊢t⋆ ρs ≅-type π (σ′ /⊢t⋆ ρs) (τ′ /⊢t⋆ ρs ↑⋆)
    π-/⊢t⋆ σ′ τ′ ε        = P.refl
    π-/⊢t⋆ σ′ τ′ (ρs ▻ ρ) = begin
      [ π σ′ τ′ /⊢t⋆ ρs /⊢t ρ                        ]  ≡⟨ /⊢t-cong (π-/⊢t⋆ σ′ τ′ ρs) (P.refl {x = [ ρ ]}) ⟩
      [ π (σ′ /⊢t⋆ ρs) (τ′ /⊢t⋆ ρs ↑⋆) /⊢t ρ         ]  ≡⟨ P.refl ⟩
      [ π (σ′ /⊢t⋆ ρs /⊢t ρ) (τ′ /⊢t⋆ ρs ↑⋆ /⊢t ρ ↑) ]  ∎

-- Another lemma.

module Apply-lemma
  {T₁ T₂ : Term-like Level.zero}
  (T₁↦T : Translation-from T₁) (T₂↦T : Translation-from T₂)
  {Γ Δ} {ρ̂ : Γ ⇨̂ Δ} (ρs₁ : Subs T₁ ρ̂) (ρs₂ : Subs T₂ ρ̂) where

  open Translation-from T₁↦T
    using () renaming (_↑⁺⋆_ to _↑⁺⋆₁_; _/⊢⋆_ to _/⊢⋆₁_)
  open Apply (Translation-from.translation T₁↦T)
    using () renaming (_/⊢t⋆_ to _/⊢t⋆₁_)
  open Translation-from T₂↦T
    using () renaming (_↑⁺⋆_ to _↑⁺⋆₂_; _/⊢⋆_ to _/⊢⋆₂_)
  open Apply (Translation-from.translation T₂↦T)
    using () renaming (_/⊢t⋆_ to _/⊢t⋆₂_)

  abstract

    var-/⊢⋆-↑⁺⋆-⇒-/⊢⋆-↑⁺⋆ :
      (∀ Γ⁺ {σ} (x : Γ ++⁺ Γ⁺ ∋ σ) →
         var x /⊢⋆₁ ρs₁ ↑⁺⋆₁ Γ⁺ ≅-⊢ var x /⊢⋆₂ ρs₂ ↑⁺⋆₂ Γ⁺) →
      ∀ Γ⁺ {σ} (t : Γ ++⁺ Γ⁺ ⊢ σ) →
      t /⊢⋆₁ ρs₁ ↑⁺⋆₁ Γ⁺ ≅-⊢ t /⊢⋆₂ ρs₂ ↑⁺⋆₂ Γ⁺
    var-/⊢⋆-↑⁺⋆-⇒-/⊢⋆-↑⁺⋆ hyp Γ⁺ (var x)  = hyp Γ⁺ x
    var-/⊢⋆-↑⁺⋆-⇒-/⊢⋆-↑⁺⋆ hyp Γ⁺ (ƛ {σ = σ} t) = begin
      [ ƛ t /⊢⋆₁ ρs₁ ↑⁺⋆₁ Γ⁺         ]  ≡⟨ Unfolding-lemmas.ƛ-/⊢⋆ T₁↦T t (ρs₁ ↑⁺⋆₁ Γ⁺) ⟩
      [ ƛ (t /⊢⋆₁ ρs₁ ↑⁺⋆₁ (Γ⁺ ▻ σ)) ]  ≡⟨ ƛ-cong (var-/⊢⋆-↑⁺⋆-⇒-/⊢⋆-↑⁺⋆ hyp (Γ⁺ ▻ σ) t) ⟩
      [ ƛ (t /⊢⋆₂ ρs₂ ↑⁺⋆₂ (Γ⁺ ▻ σ)) ]  ≡⟨ P.sym $ Unfolding-lemmas.ƛ-/⊢⋆ T₂↦T t (ρs₂ ↑⁺⋆₂ Γ⁺) ⟩
      [ ƛ t /⊢⋆₂ ρs₂ ↑⁺⋆₂ Γ⁺         ]  ∎
    var-/⊢⋆-↑⁺⋆-⇒-/⊢⋆-↑⁺⋆ hyp Γ⁺ (t₁ · t₂) = begin
      [ t₁ · t₂ /⊢⋆₁ ρs₁ ↑⁺⋆₁ Γ⁺                      ]  ≡⟨ Unfolding-lemmas.·-/⊢⋆ T₁↦T t₁ t₂ (ρs₁ ↑⁺⋆₁ Γ⁺) ⟩
      [ (t₁ /⊢⋆₁ ρs₁ ↑⁺⋆₁ Γ⁺) · (t₂ /⊢⋆₁ ρs₁ ↑⁺⋆₁ Γ⁺) ]  ≡⟨ ·-cong (var-/⊢⋆-↑⁺⋆-⇒-/⊢⋆-↑⁺⋆ hyp Γ⁺ t₁)
                                                                   (var-/⊢⋆-↑⁺⋆-⇒-/⊢⋆-↑⁺⋆ hyp Γ⁺ t₂) ⟩
      [ (t₁ /⊢⋆₂ ρs₂ ↑⁺⋆₂ Γ⁺) · (t₂ /⊢⋆₂ ρs₂ ↑⁺⋆₂ Γ⁺) ]  ≡⟨ P.sym $ Unfolding-lemmas.·-/⊢⋆ T₂↦T t₁ t₂ (ρs₂ ↑⁺⋆₂ Γ⁺) ⟩
      [ t₁ · t₂ /⊢⋆₂ ρs₂ ↑⁺⋆₂ Γ⁺                      ]  ∎

-- Term substitutions, along with a number of lemmas.

substitution₂ : Substitution₂ Tm
substitution₂ = record
  { substitution₁          = substitution₁
  ; var-/⊢⋆-↑⁺⋆-⇒-/⊢⋆-↑⁺⋆′ = Apply-lemma.var-/⊢⋆-↑⁺⋆-⇒-/⊢⋆-↑⁺⋆
  }

open Apply (Translation-from.translation no-translation) public
  using (·-/⊢; _/⊢t_; /⊢t-cong; _/⊢t⋆_; /⊢t⋆-cong)
open Unfolding-lemmas no-translation public
open Substitution₂ substitution₂ public hiding (var; substitution₁)
