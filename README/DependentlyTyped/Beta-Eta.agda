------------------------------------------------------------------------
-- Inductively defined beta-eta-equality
------------------------------------------------------------------------

import Level
open import Universe

module README.DependentlyTyped.Beta-Eta
  (Uni₀ : Universe Level.zero Level.zero)
  where

open import Data.Product renaming (curry to c)
open import Function hiding (_∋_)
import README.DependentlyTyped.Term as Term; open Term Uni₀
import README.DependentlyTyped.Term.Substitution as S; open S Uni₀
import Relation.Binary.PropositionalEquality as P

open P.≡-Reasoning

-- βη-equality.

infixl 9 _·_
infix  4 _≈_
infixr 2 _≈⟨_⟩_

data _≈_ : ∀ {Γ₁ σ₁} → Γ₁ ⊢ σ₁ → ∀ {Γ₂ σ₂} → Γ₂ ⊢ σ₂ → Set where

  -- β and η.

  β : ∀ {Γ sp₁ sp₂} {σ : IType Γ (π sp₁ sp₂)}
      (t₁ : Γ ▻ fst σ ⊢ snd σ) (t₂ : Γ ⊢ fst σ) →
      ƛ t₁ · t₂ ≈ t₁ /⊢ sub t₂
  η : ∀ {Γ sp₁ sp₂ σ} (t : Γ ⊢ (π sp₁ sp₂ , σ)) →
      ƛ ((t /⊢ wk[ fst σ ]) · var zero) ≈ t

  -- The relation is an equivalence (reflexivity is proved below).

  sym    : ∀ {Γ₁ σ₁} {t₁ : Γ₁ ⊢ σ₁}
             {Γ₂ σ₂} {t₂ : Γ₂ ⊢ σ₂}
           (t₁≈t₂ : t₁ ≈ t₂) → t₂ ≈ t₁
  _≈⟨_⟩_ : ∀ {Γ₁ σ₁} (t₁ : Γ₁ ⊢ σ₁)
             {Γ₂ σ₂} {t₂ : Γ₂ ⊢ σ₂}
             {Γ₃ σ₃} {t₃ : Γ₃ ⊢ σ₃}
           (t₁≈t₂ : t₁ ≈ t₂) (t₂≈t₃ : t₂ ≈ t₃) → t₁ ≈ t₃

  -- The relation is a congruence.

  var : ∀ {Γ₁ σ₁} {x₁ : Γ₁ ∋ σ₁}
          {Γ₂ σ₂} {x₂ : Γ₂ ∋ σ₂}
        (x₁≅x₂ : x₁ ≅-∋ x₂) → var x₁ ≈ var x₂
  ƛ   : ∀ {Γ₁ σ₁ τ₁} {t₁ : Γ₁ ▻ σ₁ ⊢ τ₁}
          {Γ₂ σ₂ τ₂} {t₂ : Γ₂ ▻ σ₂ ⊢ τ₂}
        (t₁≈t₂ : t₁ ≈ t₂) → ƛ t₁ ≈ ƛ t₂
  _·_ : ∀ {Γ₁ sp₁₁ sp₂₁ σ₁}
          {t₁₁ : Γ₁ ⊢ π sp₁₁ sp₂₁ , σ₁} {t₂₁ : Γ₁ ⊢ fst σ₁}
          {Γ₂ sp₁₂ sp₂₂ σ₂}
          {t₁₂ : Γ₂ ⊢ π sp₁₂ sp₂₂ , σ₂} {t₂₂ : Γ₂ ⊢ fst σ₂}
        (t₁₁≈t₁₂ : t₁₁ ≈ t₁₂) (t₂₁≈t₂₂ : t₂₁ ≈ t₂₂) →
        t₁₁ · t₂₁ ≈ t₁₂ · t₂₂

-- Reflexivity.

infix 2 _□

_□ : ∀ {Γ σ} (t : Γ ⊢ σ) → t ≈ t
var x   □ = var P.refl
ƛ t     □ = ƛ (t □)
t₁ · t₂ □ = (t₁ □) · (t₂ □)

abstract

  -- βη-equal terms have the same semantics.

  ≈-sound : ∀ {Γ₁ σ₁} {t₁ : Γ₁ ⊢ σ₁} {Γ₂ σ₂} {t₂ : Γ₂ ⊢ σ₂} →
            t₁ ≈ t₂ → ⟦ t₁ ⟧ ≅-Value ⟦ t₂ ⟧
  ≈-sound (β t₁ t₂) = begin
    [ c ⟦ t₁ ⟧ ˢ ⟦ t₂ ⟧ ]  ≡⟨ corresponds (app (sub t₂)) t₁ ⟩
    [ ⟦ t₁ /⊢ sub t₂ ⟧  ]  ∎
  ≈-sound (η t) = begin
    [ c (⟦ t /⊢ wk ⟧     ˢ lookup zero) ]  ≡⟨ curry-cong $ ˢ-cong (P.sym $ corresponds (app wk) t)
                                                                  (P.refl {x = [ lookup zero ]}) ⟩
    [ c ((⟦ t ⟧ /̂Val ŵk) ˢ lookup zero) ]  ≡⟨ P.refl ⟩
    [ ⟦ t ⟧                             ]  ∎
  ≈-sound (sym t₁≈t₂)           = P.sym $ ≈-sound t₁≈t₂
  ≈-sound (t₁ ≈⟨ t₁≈t₂ ⟩ t₂≈t₃) = P.trans (≈-sound t₁≈t₂) (≈-sound t₂≈t₃)
  ≈-sound (var P.refl)          = P.refl
  ≈-sound (ƛ t₁≈t₂)             = curry-cong (≈-sound t₁≈t₂)
  ≈-sound (t₁₁≈t₁₂ · t₂₁≈t₂₂)   = ˢ-cong (≈-sound t₁₁≈t₁₂) (≈-sound t₂₁≈t₂₂)

  -- βη-equal terms have identical contexts.

  ≈-⇒-≅-Ctxt : ∀ {Γ₁ σ₁} {t₁ : Γ₁ ⊢ σ₁} {Γ₂ σ₂} {t₂ : Γ₂ ⊢ σ₂} →
               t₁ ≈ t₂ → Γ₁ ≅-Ctxt Γ₂
  ≈-⇒-≅-Ctxt t₁≈t₂ = P.cong [Value].Γ $ ≈-sound t₁≈t₂

  -- βη-equal terms have identical types.

  ≈-⇒-≅-Type : ∀ {Γ₁ σ₁} {t₁ : Γ₁ ⊢ σ₁} {Γ₂ σ₂} {t₂ : Γ₂ ⊢ σ₂} →
               t₁ ≈ t₂ → σ₁ ≅-Type σ₂
  ≈-⇒-≅-Type {t₁ = t₁} {t₂ = t₂} t₁≈t₂
    with ⟦ t₂ ⟧ | ≈-sound t₁≈t₂
  ... | .(⟦ t₁ ⟧) | P.refl = P.refl
