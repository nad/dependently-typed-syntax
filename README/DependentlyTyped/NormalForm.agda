------------------------------------------------------------------------
-- Normal and neutral terms
------------------------------------------------------------------------

open import Level using (zero)
open import Universe

module README.DependentlyTyped.NormalForm
  (Uni₀ : Universe zero zero) where

import README.DependentlyTyped.Term as Term
import README.DependentlyTyped.Substitution as Substitution
open Term Uni₀
open Substitution Uni₀

open import Data.Product renaming (curry to c; uncurry to uc)
import deBruijn.Substitution; open deBruijn.Substitution Uni
open import Function renaming (const to k)
open import Relation.Binary.HeterogeneousEquality as H using (_≅_)
open import Relation.Binary.PropositionalEquality as P using (_≡_)

-- Atomic types (types for which the normaliser does not do
-- η-expansion).

data _⊢_atomic-type (Γ : Ctxt) : Type Γ → Set where
  ⋆  : Γ ⊢ k ⋆ atomic-type
  el : (t : Γ ⊢ k ⋆) → Γ ⊢ k U.el ˢ ⟦ t ⟧ atomic-type

-- Two kinds: normal and neutral.

data Kind : Set where
  no ne : Kind

mutual

  -- Γ ⊢ σ [ no ] represents η-long, β-normal terms, Γ ⊢ σ [ ne ]
  -- represents neutral terms.

  infix 4 _⊢_[_]

  data _⊢_[_] (Γ : Ctxt) : Type Γ → Kind → Set where
    ne  : ∀ {σ} (σ′ : Γ ⊢ σ atomic-type) (t : Γ ⊢ σ [ ne ]) →
          Γ ⊢ σ [ no ]
    var : ∀ {σ} (x : Γ ∋ σ) → Γ ⊢ σ [ ne ]
    ƛ   : ∀ {σ τ} (σ′ : Γ ⊢ σ type) (t : Γ ▻ σ ⊢ uc τ [ no ]) →
          Γ ⊢ k U.π ˢ σ ˢ τ [ no ]
    _·_ : ∀ {σ τ} (t₁ : Γ ⊢ k U.π ˢ σ ˢ τ [ ne ]) (t₂ : Γ ⊢ σ [ no ]) →
          Γ ⊢ uc τ /̂ ŝub ⟦ ⌊ t₂ ⌋ ⟧ [ ne ]

  -- Normal and neutral terms can be turned into ordinary terms.

  ⌊_⌋ : ∀ {Γ σ k} → Γ ⊢ σ [ k ] → Γ ⊢ σ
  ⌊ ne σ′ t ⌋ = ⌊ t ⌋
  ⌊ var x   ⌋ = var x
  ⌊ ƛ σ′ t  ⌋ = ƛ σ′ ⌊ t ⌋
  ⌊ t₁ · t₂ ⌋ = ⌊ t₁ ⌋ · ⌊ t₂ ⌋

-- A congruence lemma.

⌊⌋-cong : ∀ {Γ₁ σ₁ k₁} {t₁ : Γ₁ ⊢ σ₁ [ k₁ ]}
            {Γ₂ σ₂ k₂} {t₂ : Γ₂ ⊢ σ₂ [ k₂ ]} →
          Γ₁ ≡ Γ₂ → σ₁ ≅ σ₂ → k₁ ≡ k₂ → t₁ ≅ t₂ → ⌊ t₁ ⌋ ≅ ⌊ t₂ ⌋
⌊⌋-cong P.refl H.refl P.refl H.refl = H.refl

-- In the remainder of this module _⇨_ refers to /renamings/.

open Var-subst hiding (var)
open Tm-subst using (_/Var_; _/Var-lemma_; _/⊢t-Var_)

-- Applies a renaming to an atomic type.

infixl 8 _/⊢b_

_/⊢b_ : ∀ {Γ Δ σ} →
        Γ ⊢ σ atomic-type → (ρ : Γ ⇨ Δ) → Δ ⊢ σ / ρ atomic-type
⋆    /⊢b ρ = ⋆
el t /⊢b ρ =
  P.subst (λ v → _ ⊢ k U.el ˢ v atomic-type)
          (P.sym $ t /Var-lemma ρ)
          (el (t /Var ρ))

mutual

  -- Applies a renaming to a normal or neutral term.

  infixl 8 _/⊢n_ _/⊢n-lemma_

  _/⊢n_ : ∀ {Γ Δ σ k} →
          Γ ⊢ σ [ k ] → (ρ : Γ ⇨ Δ) → Δ ⊢ σ / ρ [ k ]
  ne σ′ t           /⊢n ρ = ne (σ′ /⊢b ρ) (t /⊢n ρ)
  var x             /⊢n ρ = var (x /∋ ρ)
  ƛ {τ = τ} σ′ t    /⊢n ρ = ƛ (σ′ /⊢t-Var ρ)
                              (P.subst (λ ρ′ → _ ⊢ uc τ /̂ ρ′ [ no ])
                                       (P.sym (ρ ↑-lemma))
                                       (t /⊢n ρ ↑))
  _·_ {τ = τ} t₁ t₂ /⊢n ρ =
    P.subst (λ v → _ ⊢ uc τ /̂ ⟦ ρ ⟧⇨ ↑̂ /̂ ŝub v [ ne ])
            (P.sym (t₂ /⊢n-lemma ρ))
            ((t₁ /⊢n ρ) · (t₂ /⊢n ρ))

  abstract

    -- The application operation is well-behaved.

    _/⊢n-lemma_ : ∀ {Γ Δ σ k} (t : Γ ⊢ σ [ k ]) (ρ : Γ ⇨ Δ) →
                  ⟦ ⌊ t ⌋ ⟧ /Val ⟦ ρ ⟧⇨ ≡ ⟦ ⌊ t /⊢n ρ ⌋ ⟧
    ne σ′ t /⊢n-lemma ρ = begin
      ⟦ ⌊ t ⌋ ⟧ /Val ⟦ ρ ⟧⇨  ≡⟨ t /⊢n-lemma ρ ⟩
      ⟦ ⌊ t /⊢n ρ ⌋ ⟧        ∎
      where open P.≡-Reasoning

    var x /⊢n-lemma ρ = begin
      x /̂∋ ⟦ ρ ⟧⇨       ≡⟨ x /∋-lemma ρ ⟩
      lookup (x /∋ ρ)   ≡⟨ P.refl ⟩
      ⟦ var (x /∋ ρ) ⟧  ∎
      where open P.≡-Reasoning

    ƛ {σ = σ} {τ = τ} σ′ t /⊢n-lemma ρ = H.≅-to-≡ (begin
      c ⟦ ⌊ t ⌋ ⟧ /Val ⟦ ρ ⟧⇨                      ≡⟨ P.refl ⟩
      c (⟦ ⌊ t ⌋ ⟧ /Val ⟦ ρ ⟧⇨ ↑̂)                  ≅⟨ curry-cong P.refl H.refl lemma
                                                                 (/Val-cong P.refl P.refl H.refl (H.refl {x = ⟦ ⌊ t ⌋ ⟧})
                                                                            (H.≡-to-≅ $ ρ ↑-lemma)) ⟩
      c (⟦ ⌊ t ⌋ ⟧ /Val ⟦ ρ ↑ ⟧⇨)                  ≡⟨ P.cong c (t /⊢n-lemma ρ ↑) ⟩
      c ⟦ ⌊ t /⊢n ρ ↑ ⌋ ⟧                          ≅⟨ curry-cong P.refl H.refl (H.sym lemma)
                                                                 (⟦⟧-cong P.refl (H.sym lemma)
                                                                          (⌊⌋-cong P.refl (H.sym lemma) P.refl
                                                                                   (H.sym $ H.≡-subst-removable
                                                                                              (λ ρ′ → _ ⊢ uc τ /̂ ρ′ [ no ])
                                                                                              (P.sym (ρ ↑-lemma)) _))) ⟩
      c ⟦ ⌊ P.subst (λ ρ′ → _ ⊢ uc τ /̂ ρ′ [ no ])
                  (P.sym (ρ ↑-lemma))
                  (t /⊢n ρ ↑) ⌋ ⟧                  ∎)
      where
      open H.≅-Reasoning

      lemma = /̂-cong P.refl P.refl (H.refl {x = uc τ})
                     (H.≡-to-≅ $ ρ ↑-lemma)

    _·_ {τ = τ} t₁ t₂ /⊢n-lemma ρ = H.≅-to-≡ (begin
       ⟦ ⌊ t₁ · t₂ ⌋ ⟧ /Val ⟦ ρ ⟧⇨                             ≡⟨ P.refl ⟩
       (⟦ ⌊ t₁ ⌋ ⟧ /Val ⟦ ρ ⟧⇨) ˢ (⟦ ⌊ t₂ ⌋ ⟧ /Val ⟦ ρ ⟧⇨)     ≅⟨ ˢ-cong P.refl H.refl
                                                                         (H.refl {x = uc τ /̂ ⟦ ρ ⟧⇨ ↑̂})
                                                                         (H.≡-to-≅ $ t₁ /⊢n-lemma ρ)
                                                                         (H.≡-to-≅ $ t₂ /⊢n-lemma ρ) ⟩
       ⟦ ⌊ t₁ /⊢n ρ ⌋ ⟧ ˢ ⟦ ⌊ t₂ /⊢n ρ ⌋ ⟧                     ≡⟨ P.refl ⟩
       ⟦ ⌊ (t₁ /⊢n ρ) · (t₂ /⊢n ρ) ⌋ ⟧                         ≅⟨ ⟦⟧-cong P.refl
                                                                          lemma
                                                                          (⌊⌋-cong P.refl lemma P.refl
                                                                                   (H.sym $ H.≡-subst-removable
                                                                                              (λ v → _ ⊢ uc τ /̂ ⟦ ρ ⟧⇨ ↑̂ /̂ ŝub v [ ne ])
                                                                                              (P.sym (t₂ /⊢n-lemma ρ)) _)) ⟩
       ⟦ ⌊ P.subst (λ v → _ ⊢ uc τ /̂ ⟦ ρ ⟧⇨ ↑̂ /̂ ŝub v [ ne ])
                 (P.sym (t₂ /⊢n-lemma ρ))
                 ((t₁ /⊢n ρ) · (t₂ /⊢n ρ)) ⌋ ⟧                 ∎)
      where
      open H.≅-Reasoning

      lemma = /̂-cong P.refl P.refl (H.refl {x = uc τ /̂ ⟦ ρ ⟧⇨ ↑̂})
                     (ŝub-cong P.refl H.refl
                               (H.≡-to-≅ $ P.sym $ t₂ /⊢n-lemma ρ))
