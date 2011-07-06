------------------------------------------------------------------------
-- Application of substitutions to normal and neutral terms
------------------------------------------------------------------------

open import Level using (zero)
open import Universe

module README.DependentlyTyped.NormalForm.Substitution
  {Uni₀ : Universe zero zero} where

open import Data.Product as Prod renaming (curry to c; uncurry to uc)
open import deBruijn.Substitution.Data
import deBruijn.TermLike as TermLike
open import Function as F renaming (const to k)
open import README.DependentlyTyped.NormalForm
open import README.DependentlyTyped.Term.Substitution
  using (module Apply)
import README.DependentlyTyped.Term as Term; open Term Uni₀
import Relation.Binary.PropositionalEquality as P

open P.≡-Reasoning
open TermLike Uni renaming (_·_ to _⊙_)

-- Code for applying substitutions containing terms which can be
-- transformed into /neutral/ terms.

module Apply-n {T : Term-like Level.zero} (T↦Ne : T ↦ Tm-n ne) where

  open _↦_ T↦Ne hiding (var)

  T↦Tm : T ↦ Tm
  T↦Tm = record
    { trans  = forget-n [∘] trans
    ; simple = simple
    }

  open Apply T↦Tm using (_/⊢_; _/⊢t_; app)

  -- Applies a substitution to an atomic type.

  infixl 8 _/⊢a_

  _/⊢a_ : ∀ {Γ Δ σ} {ρ̂ : Γ ⇨̂ Δ} →
          Γ ⊢ σ atomic-type → (ρ : Sub T ρ̂) → Δ ⊢ σ / ρ atomic-type
  ⋆    /⊢a ρ = ⋆
  el t /⊢a ρ =
    P.subst (λ v → _ ⊢ , k U.el ˢ v atomic-type)
            (≅-Value-⇒-≡ $ P.sym $ corresponds (app ρ) t)
            (el (t /⊢ ρ))

  mutual

    -- Applies a renaming to a normal or neutral term.

    infixl 8 _/⊢n_ _/⊢n-lemma_

    _/⊢n_ : ∀ {Γ Δ σ k} {ρ̂ : Γ ⇨̂ Δ} →
            Γ ⊢ σ ⟨ k ⟩ → (ρ : Sub T ρ̂) → Δ ⊢ σ / ρ ⟨ k ⟩
    ne σ′ t           /⊢n ρ = ne (σ′ /⊢a ρ) (t /⊢n ρ)
    var x             /⊢n ρ = trans ⊙ (x /∋ ρ)
    ƛ σ′ t            /⊢n ρ = ƛ (σ′ /⊢t ρ) (t /⊢n ρ ↑)
    _·_ {τ = τ} t₁ t₂ /⊢n ρ =
      P.subst (λ v → _ ⊢ Prod.map F.id uc τ /̂ ⟦ ρ ⟧⇨ ↑̂ /̂ ŝub v ⟨ ne ⟩)
              (≅-Value-⇒-≡ $ P.sym (t₂ /⊢n-lemma ρ))
              ((t₁ /⊢n ρ) · (t₂ /⊢n ρ))

    abstract

      -- An unfolding lemma.

      ·-/⊢n :
        ∀ {Γ Δ σ} {ρ̂ : Γ ⇨̂ Δ}
          {τ : ∃ λ sp → (γ : Env Γ) → El (indexed-type σ γ) → U sp}
        (t₁ : Γ ⊢ , k U.π ˢ indexed-type σ ˢ proj₂ τ ⟨ ne ⟩)
        (t₂ : Γ ⊢ σ ⟨ no ⟩) (ρ : Sub T ρ̂) →
        t₁ · t₂ /⊢n ρ ≅-⊢n (t₁ /⊢n ρ) · (t₂ /⊢n ρ)
      ·-/⊢n {τ = τ} t₁ t₂ ρ =
        drop-subst-⊢n (λ v → Prod.map F.id uc τ /̂ ⟦ ρ ⟧⇨ ↑̂ /̂ ŝub v)
                      (≅-Value-⇒-≡ $ P.sym $ t₂ /⊢n-lemma ρ)

      -- The application operation is well-behaved.

      _/⊢n-lemma_ : ∀ {Γ Δ σ k} {ρ̂ : Γ ⇨̂ Δ}
                    (t : Γ ⊢ σ ⟨ k ⟩) (ρ : Sub T ρ̂) →
                    ⟦ t ⟧n /Val ρ ≅-Value ⟦ t /⊢n ρ ⟧n
      ne σ′ t /⊢n-lemma ρ = begin
        [ ⟦ t ⟧n /Val ρ ]  ≡⟨ t /⊢n-lemma ρ ⟩
        [ ⟦ t /⊢n ρ ⟧n  ]  ∎
      var x  /⊢n-lemma ρ = /̂∋-⟦⟧⇨ x ρ
      ƛ σ′ t /⊢n-lemma ρ = begin
        [ c ⟦ t ⟧n /Val ρ     ]  ≡⟨ P.refl ⟩
        [ c (⟦ t ⟧n /Val ρ ↑) ]  ≡⟨ curry-cong (t /⊢n-lemma (ρ ↑)) ⟩
        [ c ⟦ t /⊢n ρ ↑ ⟧n    ]  ∎
      _·_ {τ = τ} t₁ t₂ /⊢n-lemma ρ = begin
        [ ⟦ t₁ · t₂ ⟧n /Val ρ                 ]  ≡⟨ P.refl ⟩
        [ (⟦ t₁ ⟧n /Val ρ) ˢ (⟦ t₂ ⟧n /Val ρ) ]  ≡⟨ ˢ-cong (P.refl {x = [ Prod.map F.id uc τ / ρ ↑ ]})
                                                           (t₁ /⊢n-lemma ρ) (t₂ /⊢n-lemma ρ) ⟩
        [ ⟦ t₁ /⊢n ρ ⟧n ˢ ⟦ t₂ /⊢n ρ ⟧n       ]  ≡⟨ P.refl ⟩
        [ ⟦ (t₁ /⊢n ρ) · (t₂ /⊢n ρ) ⟧n        ]  ≡⟨ ⟦⟧n-cong (P.sym $ ·-/⊢n t₁ t₂ ρ) ⟩
        [ ⟦ t₁ · t₂ /⊢n ρ ⟧n                  ]  ∎

  app-n : ∀ {Γ Δ} {ρ̂ : Γ ⇨̂ Δ} → Sub T ρ̂ → [ Tm-n ne ⟶ Tm-n ne ] ρ̂
  app-n ρ = record
    { function    = λ _ t → t /⊢n ρ
    ; corresponds = λ _ t → t /⊢n-lemma ρ
    }

substitution₁-n : Substitution₁ (Tm-n ne)
substitution₁-n = record
  { var      = record { function    = λ _ → var
                      ; corresponds = λ _ _ → P.refl
                      }
  ; app′     = Apply-n.app-n
  ; app′-var = λ _ _ _ → P.refl
  }

open Substitution₁ substitution₁-n public hiding (var)

-- Let us make _/⊢n_ and friends immediately available for use with
-- /renamings/.

open Apply-n (Translation-from.translation Var-↦) public
