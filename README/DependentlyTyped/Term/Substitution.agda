------------------------------------------------------------------------
-- Application of substitutions to terms
------------------------------------------------------------------------

import Level
open import Universe

module README.DependentlyTyped.Term.Substitution
  {Uni₀ : Universe Level.zero Level.zero} where

import README.DependentlyTyped.Term as Term; open Term Uni₀

open import Data.Product as Prod renaming (curry to c; uncurry to uc)
open import deBruijn.Substitution.Data
import deBruijn.TermLike as TermLike
open import Function as F using (_$_; _ˢ_) renaming (const to k)
import Relation.Binary.PropositionalEquality as P

open P.≡-Reasoning
open TermLike Uni hiding (·-cong) renaming (_·_ to _⊙_)

-- Code for applying substitutions.
--
-- Note that the _↦_ record ensures that we already have access to
-- operations such as lifting.

module Apply {T : Term-like Level.zero} (T↦Tm : T ↦ Tm) where

  open _↦_ T↦Tm hiding (var)

  mutual

    infixl 8 _/⊢t_ _/⊢_ _/⊢-lemma_

    -- Applies a substitution to a (syntactic) type.

    _/⊢t_ : ∀ {Γ Δ σ} {ρ̂ : Γ ⇨̂ Δ} → Γ ⊢ σ type → Sub T ρ̂ → Δ ⊢ σ /̂ ρ̂ type
    ⋆       /⊢t ρ = ⋆
    el t    /⊢t ρ = P.subst (λ v → _ ⊢ , k U.el ˢ v type)
                            (≅-Value-⇒-≡ $ P.sym $ t /⊢-lemma ρ) $
                      el (t /⊢ ρ)
    π σ′ τ′ /⊢t ρ = π (σ′ /⊢t ρ) (τ′ /⊢t ρ ↑)

    -- Applies a substitution to a term.

    _/⊢_ : ∀ {Γ Δ σ} {ρ̂ : Γ ⇨̂ Δ} → Γ ⊢ σ → Sub T ρ̂ → Δ ⊢ σ /̂ ρ̂
    var x             /⊢ ρ = trans ⊙ (x /∋ ρ)
    ƛ σ′ t            /⊢ ρ = ƛ (σ′ /⊢t ρ) (t /⊢ ρ ↑)
    _·_ {τ = τ} t₁ t₂ /⊢ ρ =
      P.subst (λ v → _ ⊢ Prod.map F.id uc τ /̂ ⟦ ρ ⟧⇨ ↑̂ /̂ ŝub v)
              (≅-Value-⇒-≡ $ P.sym $ t₂ /⊢-lemma ρ)
              ((t₁ /⊢ ρ) · (t₂ /⊢ ρ))

    abstract

      -- An unfolding lemma.

      ·-/⊢ : ∀ {Γ Δ σ} {ρ̂ : Γ ⇨̂ Δ}
               {τ : ∃ λ sp → (γ : Env Γ) → El (indexed-type σ γ) → U sp}
             (t₁ : Γ ⊢ , k U.π ˢ indexed-type σ ˢ proj₂ τ) (t₂ : Γ ⊢ σ)
             (ρ : Sub T ρ̂) →
             t₁ · t₂ /⊢ ρ ≅-⊢ (t₁ /⊢ ρ) · (t₂ /⊢ ρ)
      ·-/⊢ {τ = τ} t₁ t₂ ρ =
        drop-subst-⊢ (λ v → Prod.map F.id uc τ /̂ ⟦ ρ ⟧⇨ ↑̂ /̂ ŝub v)
                     (≅-Value-⇒-≡ $ P.sym $ t₂ /⊢-lemma ρ)

      -- The application operation is well-behaved.

      _/⊢-lemma_ : ∀ {Γ Δ σ} {ρ̂ : Γ ⇨̂ Δ} (t : Γ ⊢ σ) (ρ : Sub T ρ̂) →
                   ⟦ t ⟧ /Val ρ ≅-Value ⟦ t /⊢ ρ ⟧
      var x  /⊢-lemma ρ = /̂∋-⟦⟧⇨ x ρ
      ƛ σ′ t /⊢-lemma ρ = begin
        [ c ⟦ t ⟧ /Val ρ     ]  ≡⟨ P.refl ⟩
        [ c (⟦ t ⟧ /Val ρ ↑) ]  ≡⟨ curry-cong (t /⊢-lemma (ρ ↑)) ⟩
        [ c ⟦ t /⊢ ρ ↑ ⟧     ]  ∎
      _·_ {τ = τ} t₁ t₂ /⊢-lemma ρ = begin
        [ ⟦ t₁ · t₂ ⟧ /Val ρ                ]  ≡⟨ P.refl ⟩
        [ (⟦ t₁ ⟧ /Val ρ) ˢ (⟦ t₂ ⟧ /Val ρ) ]  ≡⟨ ˢ-cong (P.refl {x = [ Prod.map F.id uc τ / ρ ↑ ]})
                                                         (t₁ /⊢-lemma ρ) (t₂ /⊢-lemma ρ) ⟩
        [ ⟦ t₁ /⊢ ρ ⟧ ˢ ⟦ t₂ /⊢ ρ ⟧         ]  ≡⟨ P.refl ⟩
        [ ⟦ (t₁ /⊢ ρ) · (t₂ /⊢ ρ) ⟧         ]  ≡⟨ ⟦⟧-cong (P.sym $ ·-/⊢ t₁ t₂ ρ) ⟩
        [ ⟦ t₁ · t₂ /⊢ ρ ⟧                  ]  ∎

  app : ∀ {Γ Δ} {ρ̂ : Γ ⇨̂ Δ} → Sub T ρ̂ → [ Tm ⟶ Tm ] ρ̂
  app ρ = record
    { function    = λ _ t → t /⊢ ρ
    ; corresponds = λ _ t → t /⊢-lemma ρ
    }

  -- Application of multiple substitutions to syntactic types.

  infixl 8 _/⊢t⋆_

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

    ⋆-/⊢t⋆ : ∀ {Γ Δ} {ρ̂ : Γ ⇨̂ Δ} (ρs : Subs T ρ̂) →
             ⋆ /⊢t⋆ ρs ≅-type ⋆ {Γ = Δ}
    ⋆-/⊢t⋆ ε        = P.refl
    ⋆-/⊢t⋆ (ρs ▻ ρ) = begin
      [ ⋆ /⊢t⋆ ρs /⊢t ρ ]  ≡⟨ /⊢t-cong (⋆-/⊢t⋆ ρs) (P.refl {x = [ ρ ]}) ⟩
      [ ⋆ /⊢t ρ         ]  ≡⟨ P.refl ⟩
      [ ⋆               ]  ∎

    el-/⊢t : ∀ {Γ Δ} {ρ̂ : Γ ⇨̂ Δ} (t : Γ ⊢ , k ⋆) (ρ : Sub T ρ̂) →
             el t /⊢t ρ ≅-type el (t /⊢ ρ)
    el-/⊢t t ρ =
      drop-subst-⊢-type (λ v → , k U.el ˢ v)
                        (≅-Value-⇒-≡ $ P.sym $ t /⊢-lemma ρ)

    el-/⊢t⋆ : ∀ {Γ Δ} {ρ̂ : Γ ⇨̂ Δ} (t : Γ ⊢ , k ⋆) (ρs : Subs T ρ̂) →
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

    ƛ-/⊢⋆ : ∀ {Γ Δ σ τ} {ρ̂ : Γ ⇨̂ Δ}
            (σ′ : Γ ⊢ σ type) (t : Γ ▻ σ ⊢ τ) (ρs : Subs T ρ̂) →
            ƛ σ′ t /⊢⋆ ρs ≅-⊢ ƛ (σ′ /⊢t⋆ ρs) (t /⊢⋆ ρs ↑⋆)
    ƛ-/⊢⋆ σ′ t ε        = P.refl
    ƛ-/⊢⋆ σ′ t (ρs ▻ ρ) = begin
      [ ƛ σ′ t /⊢⋆ ρs /⊢ ρ                       ]  ≡⟨ /⊢-cong (ƛ-/⊢⋆ σ′ t ρs) (P.refl {x = [ ρ ]}) ⟩
      [ ƛ (σ′ /⊢t⋆ ρs) (t /⊢⋆ ρs ↑⋆) /⊢ ρ        ]  ≡⟨ P.refl ⟩
      [ ƛ (σ′ /⊢t⋆ (ρs ▻ ρ)) (t /⊢⋆ (ρs ▻ ρ) ↑⋆) ]  ∎

    ·-/⊢⋆ : ∀ {Γ Δ} {ρ̂ : Γ ⇨̂ Δ} {σ}
              {τ : ∃ λ sp → (γ : Env Γ) → El (indexed-type σ γ) → U sp}
            (t₁ : Γ ⊢ , k U.π ˢ indexed-type σ ˢ proj₂ τ)
            (t₂ : Γ ⊢ σ) (ρs : Subs T ρ̂) →
            t₁ · t₂ /⊢⋆ ρs ≅-⊢ (t₁ /⊢⋆ ρs) · (t₂ /⊢⋆ ρs)
    ·-/⊢⋆ t₁ t₂ ε        = P.refl
    ·-/⊢⋆ t₁ t₂ (ρs ▻ ρ) = begin
        [ t₁ · t₂ /⊢⋆ ρs /⊢ ρ                   ]  ≡⟨ /⊢-cong (·-/⊢⋆ t₁ t₂ ρs) P.refl ⟩
        [ (t₁ /⊢⋆ ρs) · (t₂ /⊢⋆ ρs) /⊢ ρ        ]  ≡⟨ ·-/⊢ (t₁ /⊢⋆ ρs) (t₂ /⊢⋆ ρs) ρ ⟩
        [ (t₁ /⊢⋆ (ρs ▻ ρ)) · (t₂ /⊢⋆ (ρs ▻ ρ)) ]  ∎

-- Another lemma.

module Apply-lemmas
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

    mutual

      var-/⊢⋆-↑⁺⋆-⇒-/⊢t⋆-↑⁺⋆ :
        (∀ Γ⁺ {σ} (x : Γ ++ Γ⁺ ∋ σ) →
           var x /⊢⋆₁ ρs₁ ↑⁺⋆₁ Γ⁺ ≅-⊢ var x /⊢⋆₂ ρs₂ ↑⁺⋆₂ Γ⁺) →
        ∀ Γ⁺ {σ} (σ′ : Γ ++ Γ⁺ ⊢ σ type) →
        σ′ /⊢t⋆₁ ρs₁ ↑⁺⋆₁ Γ⁺ ≅-type σ′ /⊢t⋆₂ ρs₂ ↑⁺⋆₂ Γ⁺
      var-/⊢⋆-↑⁺⋆-⇒-/⊢t⋆-↑⁺⋆ hyp Γ⁺ ⋆ = begin
        [ ⋆ /⊢t⋆₁ ρs₁ ↑⁺⋆₁ Γ⁺ ]  ≡⟨ Unfolding-lemmas.⋆-/⊢t⋆ T₁↦T (ρs₁ ↑⁺⋆₁ Γ⁺) ⟩
        [ ⋆                   ]  ≡⟨ P.sym $ Unfolding-lemmas.⋆-/⊢t⋆ T₂↦T (ρs₂ ↑⁺⋆₂ Γ⁺) ⟩
        [ ⋆ /⊢t⋆₂ ρs₂ ↑⁺⋆₂ Γ⁺ ]  ∎
      var-/⊢⋆-↑⁺⋆-⇒-/⊢t⋆-↑⁺⋆ hyp Γ⁺ (el t) = begin
        [ el t /⊢t⋆₁ ρs₁ ↑⁺⋆₁ Γ⁺  ]  ≡⟨ Unfolding-lemmas.el-/⊢t⋆ T₁↦T t (ρs₁ ↑⁺⋆₁ Γ⁺) ⟩
        [ el (t /⊢⋆₁ ρs₁ ↑⁺⋆₁ Γ⁺) ]  ≡⟨ el-cong (var-/⊢⋆-↑⁺⋆-⇒-/⊢⋆-↑⁺⋆ hyp Γ⁺ t) ⟩
        [ el (t /⊢⋆₂ ρs₂ ↑⁺⋆₂ Γ⁺) ]  ≡⟨ P.sym $ Unfolding-lemmas.el-/⊢t⋆ T₂↦T t (ρs₂ ↑⁺⋆₂ Γ⁺) ⟩
        [ el t /⊢t⋆₂ ρs₂ ↑⁺⋆₂ Γ⁺  ]  ∎
      var-/⊢⋆-↑⁺⋆-⇒-/⊢t⋆-↑⁺⋆ hyp Γ⁺ (π σ′ τ′) = begin
        [ π σ′ τ′ /⊢t⋆₁ ρs₁ ↑⁺⋆₁ Γ⁺                                      ]  ≡⟨ Unfolding-lemmas.π-/⊢t⋆ T₁↦T σ′ τ′ (ρs₁ ↑⁺⋆₁ Γ⁺) ⟩
        [ π (σ′ /⊢t⋆₁ ρs₁ ↑⁺⋆₁ Γ⁺) (τ′ /⊢t⋆₁ ρs₁ ↑⁺⋆₁ (Γ⁺ ▻ ⟦ σ′ ⟧type)) ]  ≡⟨ π-cong
                                                                                 (var-/⊢⋆-↑⁺⋆-⇒-/⊢t⋆-↑⁺⋆ hyp Γ⁺ σ′)
                                                                                 (var-/⊢⋆-↑⁺⋆-⇒-/⊢t⋆-↑⁺⋆ hyp (Γ⁺ ▻ ⟦ σ′ ⟧type) τ′) ⟩
        [ π (σ′ /⊢t⋆₂ ρs₂ ↑⁺⋆₂ Γ⁺) (τ′ /⊢t⋆₂ ρs₂ ↑⁺⋆₂ (Γ⁺ ▻ ⟦ σ′ ⟧type)) ]  ≡⟨ P.sym $ Unfolding-lemmas.π-/⊢t⋆ T₂↦T σ′ τ′ (ρs₂ ↑⁺⋆₂ Γ⁺) ⟩
        [ π σ′ τ′ /⊢t⋆₂ ρs₂ ↑⁺⋆₂ Γ⁺                                      ]  ∎

      var-/⊢⋆-↑⁺⋆-⇒-/⊢⋆-↑⁺⋆ :
        (∀ Γ⁺ {σ} (x : Γ ++ Γ⁺ ∋ σ) →
           var x /⊢⋆₁ ρs₁ ↑⁺⋆₁ Γ⁺ ≅-⊢ var x /⊢⋆₂ ρs₂ ↑⁺⋆₂ Γ⁺) →
        ∀ Γ⁺ {σ} (t : Γ ++ Γ⁺ ⊢ σ) →
        t /⊢⋆₁ ρs₁ ↑⁺⋆₁ Γ⁺ ≅-⊢ t /⊢⋆₂ ρs₂ ↑⁺⋆₂ Γ⁺
      var-/⊢⋆-↑⁺⋆-⇒-/⊢⋆-↑⁺⋆ hyp Γ⁺ (var x)  = hyp Γ⁺ x
      var-/⊢⋆-↑⁺⋆-⇒-/⊢⋆-↑⁺⋆ hyp Γ⁺ (ƛ σ′ t) = begin
        [ ƛ σ′ t /⊢⋆₁ ρs₁ ↑⁺⋆₁ Γ⁺                                      ]  ≡⟨ Unfolding-lemmas.ƛ-/⊢⋆ T₁↦T σ′ t (ρs₁ ↑⁺⋆₁ Γ⁺) ⟩
        [ ƛ (σ′ /⊢t⋆₁ ρs₁ ↑⁺⋆₁ Γ⁺) (t /⊢⋆₁ ρs₁ ↑⁺⋆₁ (Γ⁺ ▻ ⟦ σ′ ⟧type)) ]  ≡⟨ ƛ-cong (var-/⊢⋆-↑⁺⋆-⇒-/⊢t⋆-↑⁺⋆ hyp Γ⁺ σ′)
                                                                                    (var-/⊢⋆-↑⁺⋆-⇒-/⊢⋆-↑⁺⋆ hyp (Γ⁺ ▻ ⟦ σ′ ⟧type) t) ⟩
        [ ƛ (σ′ /⊢t⋆₂ ρs₂ ↑⁺⋆₂ Γ⁺) (t /⊢⋆₂ ρs₂ ↑⁺⋆₂ (Γ⁺ ▻ ⟦ σ′ ⟧type)) ]  ≡⟨ P.sym $ Unfolding-lemmas.ƛ-/⊢⋆ T₂↦T σ′ t (ρs₂ ↑⁺⋆₂ Γ⁺) ⟩
        [ ƛ σ′ t /⊢⋆₂ ρs₂ ↑⁺⋆₂ Γ⁺                                      ]  ∎
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
  ; var-/⊢⋆-↑⁺⋆-⇒-/⊢⋆-↑⁺⋆′ = Apply-lemmas.var-/⊢⋆-↑⁺⋆-⇒-/⊢⋆-↑⁺⋆
  }

open Apply (Translation-from.translation no-translation) public
  using (·-/⊢; _/⊢t_; /⊢t-cong; _/⊢t⋆_; /⊢t⋆-cong)
open Unfolding-lemmas no-translation public
open Apply-lemmas no-translation no-translation public
  hiding (var-/⊢⋆-↑⁺⋆-⇒-/⊢⋆-↑⁺⋆)
open Substitution₂ substitution₂ public hiding (var; substitution₁)
