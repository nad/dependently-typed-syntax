------------------------------------------------------------------------
-- Normalisation by evaluation
------------------------------------------------------------------------

import Level
import Relation.Binary.PropositionalEquality as P
open import Universe

-- The code makes use of the assumption that propositional equality of
-- functions is extensional.

module README.DependentlyTyped.NBE
  {Uni₀ : Universe Level.zero Level.zero}
  (ext : P.Extensionality Level.zero Level.zero)
  where

open import Data.Empty
open import Data.Product renaming (curry to c)
open import deBruijn.Substitution.Data
open import Function renaming (const to k)
open import README.DependentlyTyped.NormalForm
  renaming ([_] to [_]n)
import README.DependentlyTyped.Term as Term; open Term Uni₀
open import README.DependentlyTyped.Term.Substitution
open import Relation.Nullary

open P.≡-Reasoning

-- The values that are used by the NBE algorithm.

import README.DependentlyTyped.NBE.Value as Value
open Value {Uni₀} public

-- Weakening for the values.

import README.DependentlyTyped.NBE.Weakening as Weakening
open Weakening {Uni₀} ext public

-- Application.

infix 9 [_]_·̌_

[_]_·̌_ : ∀ {Γ sp₁ sp₂} σ →
         V̌alue Γ (π sp₁ sp₂ , σ) → (v : V̌alue Γ (fst σ)) →
         V̌alue Γ (snd σ /̂ ŝub ⟦̌ v ⟧)
[ _ ] f ·̌ v = proj₁ f ε v

abstract

  -- Lifting can be expressed using žero.

  ∘̂-ŵk-▻̂-žero : ∀ {Γ Δ} (ρ̂ : Γ ⇨̂ Δ) σ →
                ρ̂ ∘̂ ŵk ▻̂[ σ ] ⟦ žero _ (proj₂ σ /̂I ρ̂) ⟧n ≅-⇨̂ ρ̂ ↑̂ σ
  ∘̂-ŵk-▻̂-žero ρ̂ σ = begin
    [ ρ̂ ∘̂ ŵk ▻̂ ⟦ žero _ _ ⟧n ]  ≡⟨ ▻̂-cong P.refl P.refl (ňeutral-to-normal-identity _ (var zero)) ⟩
    [ ρ̂ ∘̂ ŵk ▻̂ ⟦ var zero ⟧  ]  ≡⟨ P.refl ⟩
    [ ρ̂ ↑̂                    ]  ∎

mutual

  -- Evaluation.

  eval : ∀ {Γ Δ σ} {ρ̂ : Γ ⇨̂ Δ} →
         Γ ⊢ σ → Sub V̌al ρ̂ → V̌alue Δ (σ /̂ ρ̂)
  eval (var x)   ρ = x /∋ ρ
  eval (ƛ t)     ρ = (eval[ƛ t ] ρ) , eval[ƛ t ] ρ well-behaved
  eval (t₁ · t₂) ρ = eval[ t₁ · t₂ ] ρ

  -- Some abbreviations.

  eval[ƛ_] : ∀ {Γ Δ σ τ} {ρ̂ : Γ ⇨̂ Δ} →
             Γ ▻ σ ⊢ τ → Sub V̌al ρ̂ → V̌alue-π Δ _ _ (IType-π σ τ /̂I ρ̂)
  eval[ƛ t ] ρ Γ₊ v = eval t (V̌al-subst.wk-subst₊ Γ₊ ρ ▻ v)

  eval[_·_] : ∀ {Γ Δ sp₁ sp₂ σ} {ρ̂ : Γ ⇨̂ Δ} →
              Γ ⊢ (π sp₁ sp₂ , σ) → (t₂ : Γ ⊢ fst σ) → Sub V̌al ρ̂ →
              V̌alue Δ (snd σ /̂ ŝub ⟦ t₂ ⟧ ∘̂ ρ̂)
  eval[_·_] {σ = σ} t₁ t₂ ρ =
    cast ([ σ /I ρ ] eval t₁ ρ ·̌ eval t₂ ρ)
    where
    cast = P.subst (λ v → V̌alue _ (snd σ /̂ ⟦ ρ ⟧⇨ ↑̂ /̂ ŝub v))
                   (≅-Value-⇒-≡ $ P.sym $ eval-lemma t₂ ρ)

  abstract

    -- The ƛ case is well-behaved.

    eval[ƛ_]_well-behaved :
      ∀ {Γ Δ σ τ} {ρ̂ : Γ ⇨̂ Δ} (t : Γ ▻ σ ⊢ τ) (ρ : Sub V̌al ρ̂) →
      W̌ell-behaved _ _ (IType-π σ τ /I ρ) (eval[ƛ t ] ρ)
    eval[ƛ_]_well-behaved {σ = σ} {τ = τ} t ρ Γ₊ v =
      let υ  = IType-π σ τ /I ρ in begin
      [ (⟦̌ υ ∣ eval[ƛ t ] ρ ⟧-π /̂Val ŵk₊ Γ₊) ˢ ⟦̌ v ⟧ ]  ≡⟨ ˢ-cong (/̂Val-cong (P.sym $ eval-lemma-ƛ t ρ) P.refl) P.refl ⟩
      [ (c ⟦ t ⟧ /̂Val ⟦ ρ ⟧⇨ ∘̂ ŵk₊ Γ₊) ˢ ⟦̌ v ⟧       ]  ≡⟨ P.refl ⟩
      [ ⟦ t ⟧ /̂Val (⟦ ρ ⟧⇨ ∘̂ ŵk₊ Γ₊ ▻̂ ⟦̌ v ⟧)         ]  ≡⟨ eval-lemma t _ ⟩
      [ ⟦̌ eval t (V̌al-subst.wk-subst₊ Γ₊ ρ ▻ v) ⟧    ]  ∎

    -- An unfolding lemma.

    eval-· :
      ∀ {Γ Δ sp₁ sp₂ σ} {ρ̂ : Γ ⇨̂ Δ}
      (t₁ : Γ ⊢ π sp₁ sp₂ , σ) (t₂ : Γ ⊢ fst σ) (ρ : Sub V̌al ρ̂) →
      eval[ t₁ · t₂ ] ρ ≅-V̌alue [ σ /I ρ ] eval t₁ ρ ·̌ eval t₂ ρ
    eval-· {σ = σ} t₁ t₂ ρ =
      drop-subst-V̌alue (λ v → snd σ /̂ ⟦ ρ ⟧⇨ ↑̂ /̂ ŝub v)
                       (≅-Value-⇒-≡ $ P.sym $ eval-lemma t₂ ρ)

    -- The evaluator is correct (with respect to the standard
    -- semantics).

    eval-lemma : ∀ {Γ Δ σ} {ρ̂ : Γ ⇨̂ Δ} (t : Γ ⊢ σ) (ρ : Sub V̌al ρ̂) →
                 ⟦ t ⟧ /Val ρ ≅-Value ⟦̌ eval t ρ ⟧
    eval-lemma (var x)             ρ = V̌al-subst./̂∋-⟦⟧⇨ x ρ
    eval-lemma (ƛ t)               ρ = eval-lemma-ƛ t ρ
    eval-lemma (_·_ {σ = σ} t₁ t₂) ρ = begin
      [ ⟦ t₁ · t₂ ⟧ /Val ρ                           ]  ≡⟨ P.refl ⟩
      [ (⟦ t₁ ⟧ /Val ρ) ˢ (⟦ t₂ ⟧ /Val ρ)            ]  ≡⟨ ˢ-cong (eval-lemma t₁ ρ) (eval-lemma t₂ ρ) ⟩
      [ ⟦̌_⟧ {σ = σ /I ρ} (eval t₁ ρ) ˢ ⟦̌ eval t₂ ρ ⟧ ]  ≡⟨ proj₂ (eval t₁ ρ) ε (eval t₂ ρ) ⟩
      [ ⟦̌ [ σ /I ρ ] eval t₁ ρ ·̌ eval t₂ ρ ⟧         ]  ≡⟨ ⟦̌⟧-cong (P.sym $ eval-· t₁ t₂ ρ) ⟩
      [ ⟦̌ eval[ t₁ · t₂ ] ρ ⟧                        ]  ∎

    private

      eval-lemma-ƛ :
        ∀ {Γ Δ σ τ} {ρ̂ : Γ ⇨̂ Δ} (t : Γ ▻ σ ⊢ τ) (ρ : Sub V̌al ρ̂) →
        ⟦ ƛ t ⟧ /Val ρ ≅-Value ⟦̌ IType-π σ τ /I ρ ∣ eval[ƛ t ] ρ ⟧-π
      eval-lemma-ƛ {σ = σ} {τ = τ} t ρ =
        let υ  = IType-π σ τ /I ρ
            ρ↑ = V̌al-subst.wk-subst₊ (σ / ρ ◅ ε) ρ ▻ v̌ar ⊙ zero

        in begin
        [ c ⟦ t ⟧ /Val ρ          ]  ≡⟨ P.refl ⟩
        [ c (⟦ t ⟧ /̂Val ⟦ ρ ⟧⇨ ↑̂) ]  ≡⟨ curry-cong $ /̂Val-cong (P.refl {x = [ ⟦ t ⟧ ]})
                                                                         (P.sym $ ∘̂-ŵk-▻̂-žero ⟦ ρ ⟧⇨ _) ⟩
        [ c (⟦ t ⟧ /Val ρ↑)       ]  ≡⟨ curry-cong (eval-lemma t ρ↑) ⟩
        [ c ⟦̌ eval t ρ↑ ⟧         ]  ≡⟨ P.sym $ unfold-⟦̌∣⟧-π υ (eval[ƛ t ] ρ) ⟩
        [ ⟦̌ υ ∣ eval[ƛ t ] ρ ⟧-π  ]  ∎

-- Normalisation.

normalise : ∀ {Γ σ} → Γ ⊢ σ → Γ ⊢ σ ⟨ no ⟩
normalise t = řeify _ (eval t V̌al-subst.id)

-- Normalisation is semantics-preserving.

normalise-lemma : ∀ {Γ σ} (t : Γ ⊢ σ) → ⟦ t ⟧ ≅-Value ⟦ normalise t ⟧n
normalise-lemma t = eval-lemma t V̌al-subst.id

-- Some congruence lemmas.

·̌-cong :
  ∀ {Γ₁ sp₁₁ sp₂₁ σ₁}
    {f₁ : V̌alue Γ₁ (π sp₁₁ sp₂₁ , σ₁)} {v₁ : V̌alue Γ₁ (fst σ₁)}
    {Γ₂ sp₁₂ sp₂₂ σ₂}
    {f₂ : V̌alue Γ₂ (π sp₁₂ sp₂₂ , σ₂)} {v₂ : V̌alue Γ₂ (fst σ₂)} →
  σ₁ ≅-IType σ₂ → _≅-V̌alue_ {σ₁ = , σ₁} f₁ {σ₂ = , σ₂} f₂ →
  v₁ ≅-V̌alue v₂ →
  [ σ₁ ] f₁ ·̌ v₁ ≅-V̌alue [ σ₂ ] f₂ ·̌ v₂
·̌-cong P.refl P.refl P.refl = P.refl

eval-cong :
  ∀ {Γ₁ Δ₁ σ₁} {ρ̂₁ : Γ₁ ⇨̂ Δ₁} {t₁ : Γ₁ ⊢ σ₁} {ρ₁ : Sub V̌al ρ̂₁}
    {Γ₂ Δ₂ σ₂} {ρ̂₂ : Γ₂ ⇨̂ Δ₂} {t₂ : Γ₂ ⊢ σ₂} {ρ₂ : Sub V̌al ρ̂₂} →
  t₁ ≅-⊢ t₂ → ρ₁ ≅-⇨ ρ₂ → eval t₁ ρ₁ ≅-V̌alue eval t₂ ρ₂
eval-cong P.refl P.refl = P.refl

normalise-cong :
  ∀ {Γ₁ σ₁} {t₁ : Γ₁ ⊢ σ₁}
    {Γ₂ σ₂} {t₂ : Γ₂ ⊢ σ₂} →
  t₁ ≅-⊢ t₂ → normalise t₁ ≅-⊢n normalise t₂
normalise-cong P.refl = P.refl

abstract

  -- Note that we can /not/ prove that normalise takes semantically
  -- equal terms to identical normal forms, assuming extensionality
  -- and the existence of a universe code which decodes to an empty
  -- type:

  normal-forms-not-unique :
    P.Extensionality Level.zero Level.zero →
    (∃ λ (bot : U₀) → ¬ El₀ bot) →
    ¬ (∀ {Γ σ} (t₁ t₂ : Γ ⊢ σ) →
       ⟦ t₁ ⟧ ≅-Value ⟦ t₂ ⟧ → normalise t₁ ≅-⊢n normalise t₂)
  normal-forms-not-unique ext (bot , empty) hyp = ⊥-elim (x₁≇x₂ x₁≅x₂)
    where
    Γ : Ctxt
    Γ = ε ▻ (⋆ , _) ▻ (⋆ , _) ▻ (el , k bot)

    x₁ : Γ ∋ (⋆ , _)
    x₁ = suc (suc zero)

    x₂ : Γ ∋ (⋆ , _)
    x₂ = suc zero

    x₁≇x₂ : ¬ (ne ⋆ (var x₁) ≅-⊢n ne ⋆ (var x₂))
    x₁≇x₂ ()

    ⟦x₁⟧≡⟦x₂⟧ : ⟦ var x₁ ⟧ ≅-Value ⟦ var x₂ ⟧
    ⟦x₁⟧≡⟦x₂⟧ = P.cong [_] (ext λ γ → ⊥-elim $ empty $ proj₂ γ)

    norm-x₁≅norm-x₂ : normalise (var x₁) ≅-⊢n normalise (var x₂)
    norm-x₁≅norm-x₂ = hyp (var x₁) (var x₂) ⟦x₁⟧≡⟦x₂⟧

    lemma : (x : Γ ∋ (⋆ , _)) → normalise (var x) ≅-⊢n ne ⋆ (var x)
    lemma x = begin
      [ normalise (var x)        ]n  ≡⟨ P.refl ⟩
      [ ne ⋆ (x /∋ V̌al-subst.id) ]n  ≡⟨ ne-cong $ ≅-Value-⋆-⇒-≅-⊢n $ V̌al-subst./∋-id x ⟩
      [ ne ⋆ (var x)             ]n  ∎

    x₁≅x₂ : ne ⋆ (var x₁) ≅-⊢n ne ⋆ (var x₂)
    x₁≅x₂ = begin
      [ ne ⋆ (var x₁)      ]n  ≡⟨ P.sym $ lemma x₁ ⟩
      [ normalise (var x₁) ]n  ≡⟨ norm-x₁≅norm-x₂ ⟩
      [ normalise (var x₂) ]n  ≡⟨ lemma x₂ ⟩
      [ ne ⋆ (var x₂)      ]n  ∎
