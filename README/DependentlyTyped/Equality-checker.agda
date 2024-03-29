------------------------------------------------------------------------
-- Various equality checkers (some complete, all sound)
------------------------------------------------------------------------

import Axiom.Extensionality.Propositional as E
import Level
open import Data.Universe

-- The code makes use of the assumption that propositional equality of
-- functions is extensional.

module README.DependentlyTyped.Equality-checker
  (Uni₀ : Universe Level.zero Level.zero)
  (ext : E.Extensionality Level.zero Level.zero)
  where

open import Data.Maybe
import Data.Maybe.Effectful as Maybe
open import Data.Product
open import Effect.Monad
open import Function hiding (_∋_) renaming (const to k)
import README.DependentlyTyped.NBE as NBE; open NBE Uni₀ ext
import README.DependentlyTyped.NormalForm as NF; open NF Uni₀
import README.DependentlyTyped.Term as Term; open Term Uni₀
open import Relation.Binary.PropositionalEquality as P using (_≡_)
open import Relation.Nullary as Dec using (Dec; yes)
import Relation.Nullary.Decidable as Dec

open P.≡-Reasoning
open RawMonadZero (Maybe.monadZero {f = Level.zero})

-- Decides if two "atomic type proofs" are equal.

infix 4 _≟-atomic-type_

_≟-atomic-type_ :
  ∀ {Γ σ} (σ′₁ σ′₂ : Γ ⊢ σ atomic-type) → Dec (σ′₁ ≡ σ′₂)
⋆  ≟-atomic-type ⋆  = yes P.refl
el ≟-atomic-type el = yes P.refl

mutual

  private

    -- A helper lemma.

    helper-lemma :
      ∀ {Γ₁ sp₁₁ sp₂₁ σ₁}
        (t₁₁ : Γ₁ ⊢ π sp₁₁ sp₂₁ , σ₁ ⟨ ne ⟩) (t₂₁ : Γ₁ ⊢ fst σ₁ ⟨ no ⟩)
        {Γ₂ sp₁₂ sp₂₂ σ₂}
        (t₁₂ : Γ₂ ⊢ π sp₁₂ sp₂₂ , σ₂ ⟨ ne ⟩) (t₂₂ : Γ₂ ⊢ fst σ₂ ⟨ no ⟩) →
      t₁₁ · t₂₁ ≅-⊢n t₁₂ · t₂₂ → t₁₁ ≅-⊢n t₁₂ × t₂₁ ≅-⊢n t₂₂
    helper-lemma _ _ ._ ._ P.refl = P.refl , P.refl

  -- Decides if two neutral terms are identical. Note that the terms
  -- must have the same context, but they do not need to have the same
  -- type.

  infix 4 _≟-⊢ne_

  _≟-⊢ne_ : ∀ {Γ σ₁} (t₁ : Γ ⊢ σ₁ ⟨ ne ⟩)
                {σ₂} (t₂ : Γ ⊢ σ₂ ⟨ ne ⟩) →
            Dec (t₁ ≅-⊢n t₂)
  var x₁ ≟-⊢ne var x₂ = Dec.map′ var-n-cong helper (x₁ ≟-∋ x₂)
    where
    helper : ∀ {Γ₁ σ₁} {x₁ : Γ₁ ∋ σ₁}
               {Γ₂ σ₂} {x₂ : Γ₂ ∋ σ₂} →
             var x₁ ≅-⊢n var x₂ → x₁ ≅-∋ x₂
    helper P.refl = P.refl

  t₁₁ · t₂₁ ≟-⊢ne t₁₂ · t₂₂ with t₁₁ ≟-⊢ne t₁₂
  ... | Dec.no neq = Dec.no (neq ∘ proj₁ ∘ helper-lemma _ t₂₁ _ t₂₂)
  ... | yes eq     = Dec.map′
    (·n-cong eq)
    (proj₂ ∘ helper-lemma t₁₁ _ t₁₂ _)
    (t₂₁ ≟-⊢no t₂₂ [ fst-cong $ indexed-type-cong $ helper eq ])
    where
    helper : ∀ {Γ₁ σ₁} {t₁ : Γ₁ ⊢ σ₁ ⟨ ne ⟩}
               {Γ₂ σ₂} {t₂ : Γ₂ ⊢ σ₂ ⟨ ne ⟩} →
             t₁ ≅-⊢n t₂ → σ₁ ≅-Type σ₂
    helper P.refl = P.refl

  var _ ≟-⊢ne _ · _ = Dec.no λ ()
  _ · _ ≟-⊢ne var _ = Dec.no λ ()

  -- Decides if two normal forms are identical. Note that the terms
  -- must have the same type.

  infix 4 _≟-⊢no_[_]

  _≟-⊢no_[_] : ∀ {Γ₁ σ₁} (t₁ : Γ₁ ⊢ σ₁ ⟨ no ⟩)
                 {Γ₂ σ₂} (t₂ : Γ₂ ⊢ σ₂ ⟨ no ⟩) →
              σ₁ ≅-Type σ₂ → Dec (t₁ ≅-⊢n t₂)
  ne σ′₁ t₁ ≟-⊢no ne σ′₂ t₂ [ P.refl ] = ne≟ne σ′₁ σ′₂ (t₁ ≟-⊢ne t₂)
    where
    ne≟ne : ∀ {Γ σ} {t₁ t₂ : Γ ⊢ σ ⟨ ne ⟩}
            (σ′₁ : Γ ⊢ σ atomic-type) (σ′₂ : Γ ⊢ σ atomic-type) →
            Dec (t₁ ≅-⊢n t₂) → Dec (ne σ′₁ t₁ ≅-⊢n ne σ′₂ t₂)
    ne≟ne ⋆  ⋆  (yes P.refl) = yes P.refl
    ne≟ne el el (yes P.refl) = yes P.refl
    ne≟ne _  _  (Dec.no neq) = Dec.no (neq ∘ helper)
      where
      helper :
        ∀ {Γ₁ σ₁ σ′₁} {t₁ : Γ₁ ⊢ σ₁ ⟨ ne ⟩}
          {Γ₂ σ₂ σ′₂} {t₂ : Γ₂ ⊢ σ₂ ⟨ ne ⟩} →
        ne σ′₁ t₁ ≅-⊢n ne σ′₂ t₂ → t₁ ≅-⊢n t₂
      helper P.refl = P.refl

  ƛ t₁ ≟-⊢no ƛ t₂ [ eq ] =
    Dec.map′ ƛn-cong helper
             (t₁ ≟-⊢no t₂ [ snd-cong $ indexed-type-cong eq ])
    where
    helper :
      ∀ {Γ₁ σ₁ τ₁} {t₁ : Γ₁ ▻ σ₁ ⊢ τ₁ ⟨ no ⟩}
        {Γ₂ σ₂ τ₂} {t₂ : Γ₂ ▻ σ₂ ⊢ τ₂ ⟨ no ⟩} →
      ƛ t₁ ≅-⊢n ƛ t₂ → t₁ ≅-⊢n t₂
    helper P.refl = P.refl

  ne _ _ ≟-⊢no ƛ _    [ _ ] = Dec.no λ ()
  ƛ _    ≟-⊢no ne _ _ [ _ ] = Dec.no λ ()

-- Tries to prove that two terms have the same semantics. The terms
-- must have the same type.

⟦_⟧≟⟦_⟧ : ∀ {Γ σ} (t₁ t₂ : Γ ⊢ σ) →
          Maybe (⟦ t₁ ⟧ ≅-Value ⟦ t₂ ⟧)
⟦ t₁ ⟧≟⟦ t₂ ⟧ with normalise t₁ ≟-⊢no normalise t₂ [ P.refl ]
... | Dec.no _ = ∅
... | yes eq   = pure (begin
  [ ⟦ t₁ ⟧            ]  ≡⟨ normalise-lemma t₁ ⟩
  [ ⟦ normalise t₁ ⟧n ]  ≡⟨ ⟦⟧n-cong eq ⟩
  [ ⟦ normalise t₂ ⟧n ]  ≡⟨ P.sym $ normalise-lemma t₂ ⟩
  [ ⟦ t₂ ⟧            ]  ∎)

-- Tries to prove that two semantic types are equal, given
-- corresponding syntactic types. The types must have the same
-- context.

infix 4 _≟-Type_

_≟-Type_ : ∀ {Γ σ₁} (σ₁′ : Γ ⊢ σ₁ type)
               {σ₂} (σ₂′ : Γ ⊢ σ₂ type) →
           Maybe (σ₁ ≅-Type σ₂)
⋆ ≟-Type ⋆ = pure P.refl

el t₁ ≟-Type el t₂ = helper <$> ⟦ t₁ ⟧≟⟦ t₂ ⟧
  where
  helper : ∀ {Γ₁} {v₁ : Value Γ₁ (⋆ , _)}
             {Γ₂} {v₂ : Value Γ₂ (⋆ , _)} →
           v₁ ≅-Value v₂ → (el , v₁) ≅-Type (el , v₂)
  helper P.refl = P.refl
π σ′₁ τ′₁ ≟-Type π σ′₂ τ′₂ = helper τ′₁ τ′₂ =<< σ′₁ ≟-Type σ′₂
  where
  helper :
    ∀ {Γ₁ σ₁ τ₁} (τ′₁ : Γ₁ ▻ σ₁ ⊢ τ₁ type)
      {Γ₂ σ₂ τ₂} (τ′₂ : Γ₂ ▻ σ₂ ⊢ τ₂ type) →
    σ₁ ≅-Type σ₂ → Maybe (Type-π σ₁ τ₁ ≅-Type Type-π σ₂ τ₂)
  helper τ′₁ τ′₂ P.refl = Type-π-cong <$> (τ′₁ ≟-Type τ′₂)

_ ≟-Type _ = ∅
