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
  ⋆  /⊢a ρ = ⋆
  el /⊢a ρ = el

  mutual

    -- Applies a renaming to a normal or neutral term.

    infixl 8 _/⊢n_ _/⊢n-lemma_

    _/⊢n_ : ∀ {Γ Δ σ k} {ρ̂ : Γ ⇨̂ Δ} →
            Γ ⊢ σ ⟨ k ⟩ → (ρ : Sub T ρ̂) → Δ ⊢ σ / ρ ⟨ k ⟩
    ne σ′ t           /⊢n ρ = ne (σ′ /⊢a ρ) (t /⊢n ρ)
    var x             /⊢n ρ = trans ⊙ (x /∋ ρ)
    ƛ t               /⊢n ρ = ƛ (t /⊢n ρ ↑)
    _·_ {σ = σ} t₁ t₂ /⊢n ρ =
      P.subst (λ v → _ ⊢ snd σ /̂ ⟦ ρ ⟧⇨ ↑̂ /̂ ŝub v ⟨ ne ⟩)
              (≅-Value-⇒-≡ $ P.sym (t₂ /⊢n-lemma ρ))
              ((t₁ /⊢n ρ) · (t₂ /⊢n ρ))

    abstract

      -- An unfolding lemma.

      ·-/⊢n :
        ∀ {Γ Δ sp₁ sp₂ σ} {ρ̂ : Γ ⇨̂ Δ}
        (t₁ : Γ ⊢ π sp₁ sp₂ , σ ⟨ ne ⟩) (t₂ : Γ ⊢ fst σ ⟨ no ⟩)
        (ρ : Sub T ρ̂) →
        t₁ · t₂ /⊢n ρ ≅-⊢n (t₁ /⊢n ρ) · (t₂ /⊢n ρ)
      ·-/⊢n {σ = σ} t₁ t₂ ρ =
        drop-subst-⊢n (λ v → snd σ /̂ ⟦ ρ ⟧⇨ ↑̂ /̂ ŝub v)
                      (≅-Value-⇒-≡ $ P.sym $ t₂ /⊢n-lemma ρ)

      -- The application operation is well-behaved.

      _/⊢n-lemma_ : ∀ {Γ Δ σ k} {ρ̂ : Γ ⇨̂ Δ}
                    (t : Γ ⊢ σ ⟨ k ⟩) (ρ : Sub T ρ̂) →
                    ⟦ t ⟧n /Val ρ ≅-Value ⟦ t /⊢n ρ ⟧n
      ne σ′ t /⊢n-lemma ρ = begin
        [ ⟦ t ⟧n /Val ρ ]  ≡⟨ t /⊢n-lemma ρ ⟩
        [ ⟦ t /⊢n ρ ⟧n  ]  ∎
      var x /⊢n-lemma ρ = /̂∋-⟦⟧⇨ x ρ
      ƛ t   /⊢n-lemma ρ = begin
        [ c ⟦ t ⟧n /Val ρ     ]  ≡⟨ P.refl ⟩
        [ c (⟦ t ⟧n /Val ρ ↑) ]  ≡⟨ curry-cong (t /⊢n-lemma (ρ ↑)) ⟩
        [ c ⟦ t /⊢n ρ ↑ ⟧n    ]  ∎
      t₁ · t₂ /⊢n-lemma ρ = begin
        [ ⟦ t₁ · t₂ ⟧n /Val ρ                 ]  ≡⟨ P.refl ⟩
        [ (⟦ t₁ ⟧n /Val ρ) ˢ (⟦ t₂ ⟧n /Val ρ) ]  ≡⟨ ˢ-cong (t₁ /⊢n-lemma ρ) (t₂ /⊢n-lemma ρ) ⟩
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
