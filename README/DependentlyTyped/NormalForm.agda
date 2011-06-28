------------------------------------------------------------------------
-- Normal and neutral terms
------------------------------------------------------------------------

open import Level using (zero)
open import Universe

module README.DependentlyTyped.NormalForm
  {Uni₀ : Universe zero zero} where

open import Data.Product renaming (curry to c; uncurry to uc)
open import deBruijn.Substitution.Data
import deBruijn.TermLike as TermLike
open import Function renaming (const to k; _∘_ to _⊚_)
open import README.DependentlyTyped.Substitution
  using (module Apply)
import README.DependentlyTyped.Term as Term; open Term Uni₀
import Relation.Binary.PropositionalEquality as P

open P.≡-Reasoning
open TermLike Uni renaming (_·_ to _⊙_; ·-cong to ⊙-cong)

------------------------------------------------------------------------
-- Normal and neutral terms

-- Atomic types (types for which the normaliser does not do
-- η-expansion).

data _⊢_atomic-type (Γ : Ctxt) : Type Γ → Set where
  ⋆  : Γ ⊢ k ⋆ atomic-type
  el : (t : Γ ⊢ k ⋆) → Γ ⊢ k U.el ˢ ⟦ t ⟧ atomic-type

-- Two kinds: normal and neutral.

data Kind : Set where
  no ne : Kind

mutual

  -- Γ ⊢ σ ⟨ no ⟩ represents η-long, β-normal terms, Γ ⊢ σ ⟨ ne ⟩
  -- represents neutral terms.

  infix 4 _⊢_⟨_⟩

  data _⊢_⟨_⟩ (Γ : Ctxt) : Type Γ → Kind → Set where
    ne  : ∀ {σ} (σ′ : Γ ⊢ σ atomic-type) (t : Γ ⊢ σ ⟨ ne ⟩) →
          Γ ⊢ σ ⟨ no ⟩
    var : ∀ {σ} (x : Γ ∋ σ) → Γ ⊢ σ ⟨ ne ⟩
    ƛ   : ∀ {σ τ} (σ′ : Γ ⊢ σ type) (t : Γ ▻ σ ⊢ τ ⟨ no ⟩) →
          Γ ⊢ k U.π ˢ σ ˢ c τ ⟨ no ⟩
    _·_ : ∀ {σ τ} (t₁ : Γ ⊢ k U.π ˢ σ ˢ τ ⟨ ne ⟩) (t₂ : Γ ⊢ σ ⟨ no ⟩) →
          Γ ⊢ uc τ /̂ ŝub ⟦ ⌊ t₂ ⌋ ⟧ ⟨ ne ⟩

  -- Normal and neutral terms can be turned into ordinary terms.

  ⌊_⌋ : ∀ {Γ σ k} → Γ ⊢ σ ⟨ k ⟩ → Γ ⊢ σ
  ⌊ ne σ′ t ⌋ = ⌊ t ⌋
  ⌊ var x   ⌋ = var x
  ⌊ ƛ σ′ t  ⌋ = ƛ σ′ ⌊ t ⌋
  ⌊ t₁ · t₂ ⌋ = ⌊ t₁ ⌋ · ⌊ t₂ ⌋

-- Normal and neutral terms are "term-like".

Tm-n : Kind → Term-like _
Tm-n k = record { _⊢_ = λ Γ σ → Γ ⊢ σ ⟨ k ⟩; ⟦_⟧ = ⟦_⟧ ⊚ ⌊_⌋ }

private
  open module T {k} = Term-like (Tm-n k) public
    using ([_])
    renaming ( ⟦_⟧ to ⟦_⟧n; _≅-⊢_ to _≅-⊢n_
             ; drop-subst-⊢ to drop-subst-⊢n; ⟦⟧-cong to ⟦⟧n-cong
             )

-- As mentioned above normal and neutral terms can be turned into
-- ordinary terms.

forget-n : ∀ {k} → [ Tm-n k ⟶⁼ Tm ]
forget-n = record
  { function    = λ _ → ⌊_⌋
  ; corresponds = λ _ _ → P.refl
  }

-- Various congruences.

ne-cong : ∀ {Γ σ} {σ′ : Γ ⊢ σ atomic-type}
            {t₁ t₂ : Γ ⊢ σ ⟨ ne ⟩} →
          t₁ ≅-⊢n t₂ → ne σ′ t₁ ≅-⊢n ne σ′ t₂
ne-cong P.refl = P.refl

var-n-cong : ∀ {Γ₁ σ₁} {x₁ : Γ₁ ∋ σ₁}
               {Γ₂ σ₂} {x₂ : Γ₂ ∋ σ₂} →
             x₁ ≅-∋ x₂ → var x₁ ≅-⊢n var x₂
var-n-cong P.refl = P.refl

ƛn-cong : ∀ {Γ₁ σ₁ τ₁} {σ′₁ : Γ₁ ⊢ σ₁ type} {t₁ : Γ₁ ▻ σ₁ ⊢ τ₁ ⟨ no ⟩}
            {Γ₂ σ₂ τ₂} {σ′₂ : Γ₂ ⊢ σ₂ type} {t₂ : Γ₂ ▻ σ₂ ⊢ τ₂ ⟨ no ⟩} →
          σ′₁ ≅-type σ′₂ → t₁ ≅-⊢n t₂ → ƛ σ′₁ t₁ ≅-⊢n ƛ σ′₂ t₂
ƛn-cong P.refl P.refl = P.refl

·n-cong : ∀ {Γ σ τ} {t₁₁ t₁₂ : Γ ⊢ k U.π ˢ σ ˢ τ ⟨ ne ⟩}
           {t₂₁ t₂₂ : Γ ⊢ σ ⟨ no ⟩} →
         t₁₁ ≅-⊢n t₁₂ → t₂₁ ≅-⊢n t₂₂ → t₁₁ · t₂₁ ≅-⊢n t₁₂ · t₂₂
·n-cong P.refl P.refl = P.refl

------------------------------------------------------------------------
-- Application of substitutions

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

  infixl 8 _/⊢b_

  _/⊢b_ : ∀ {Γ Δ σ} {ρ̂ : Γ ⇨̂ Δ} →
          Γ ⊢ σ atomic-type → (ρ : Sub T ρ̂) → Δ ⊢ σ / ρ atomic-type
  ⋆    /⊢b ρ = ⋆
  el t /⊢b ρ =
    P.subst (λ v → _ ⊢ k U.el ˢ v atomic-type)
            (≅-Value-⇒-≡ $ P.sym $ corresponds (app ρ) t)
            (el (t /⊢ ρ))

  mutual

    -- Applies a renaming to a normal or neutral term.

    infixl 8 _/⊢n_ _/⊢n-lemma_

    _/⊢n_ : ∀ {Γ Δ σ k} {ρ̂ : Γ ⇨̂ Δ} →
            Γ ⊢ σ ⟨ k ⟩ → (ρ : Sub T ρ̂) → Δ ⊢ σ / ρ ⟨ k ⟩
    ne σ′ t           /⊢n ρ = ne (σ′ /⊢b ρ) (t /⊢n ρ)
    var x             /⊢n ρ = trans ⊙ (x /∋ ρ)
    ƛ σ′ t            /⊢n ρ = ƛ (σ′ /⊢t ρ) (t /⊢n ρ ↑)
    _·_ {τ = τ} t₁ t₂ /⊢n ρ =
      P.subst (λ v → _ ⊢ uc τ /̂ ⟦ ρ ⟧⇨ ↑̂ /̂ ŝub v ⟨ ne ⟩)
              (≅-Value-⇒-≡ $ P.sym (t₂ /⊢n-lemma ρ))
              ((t₁ /⊢n ρ) · (t₂ /⊢n ρ))

    abstract

      -- An unfolding lemma.

      ·-/⊢n : ∀ {Γ Δ σ τ} {ρ̂ : Γ ⇨̂ Δ}
              (t₁ : Γ ⊢ k U.π ˢ σ ˢ τ ⟨ ne ⟩) (t₂ : Γ ⊢ σ ⟨ no ⟩)
              (ρ : Sub T ρ̂) →
              t₁ · t₂ /⊢n ρ ≅-⊢n (t₁ /⊢n ρ) · (t₂ /⊢n ρ)
      ·-/⊢n {τ = τ} t₁ t₂ ρ =
        drop-subst-⊢n (λ v → uc τ /̂ ⟦ ρ ⟧⇨ ↑̂ /̂ ŝub v)
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
        [ (⟦ t₁ ⟧n /Val ρ) ˢ (⟦ t₂ ⟧n /Val ρ) ]  ≡⟨ ˢ-cong (P.refl {x = [ uc τ / ρ ↑ ]})
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
