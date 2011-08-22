------------------------------------------------------------------------
-- A Kripke model
------------------------------------------------------------------------

import Level
import Relation.Binary.PropositionalEquality as P
open import Universe

-- The code makes use of the assumption that propositional equality of
-- functions is extensional.

module README.DependentlyTyped.Kripke-model
  {Uni₀ : Universe Level.zero Level.zero}
  (ext : P.Extensionality Level.zero Level.zero)
  where

open import Data.Product renaming (curry to c)
open import deBruijn.Substitution.Data
open import Function renaming (const to k)
open import README.DependentlyTyped.NormalForm
import README.DependentlyTyped.Term as Term; open Term Uni₀

open P.≡-Reasoning

-- The family of types which forms a Kripke model.

import README.DependentlyTyped.Kripke-model.Definition as Definition
open Definition {Uni₀} public

-- Weakening.

import README.DependentlyTyped.Kripke-model.Weakening as Weakening
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

-- Evaluation.

mutual

  eval : ∀ {Γ Δ σ} {ρ̂ : Γ ⇨̂ Δ} →
         Γ ⊢ σ → Sub V̌al ρ̂ → V̌alue Δ (σ /̂ ρ̂)
  eval (var x)             ρ = x /∋ ρ
  eval (_·_ {σ = σ} t₁ t₂) ρ =
    cast ([ σ /I ρ ] eval t₁ ρ ·̌ eval t₂ ρ)
    where
    cast = P.subst (λ v → V̌alue _ (snd σ /̂ ⟦ ρ ⟧⇨ ↑̂ /̂ ŝub v))
                   (≅-Value-⇒-≡ $ P.sym $ eval-lemma t₂ ρ)
  eval (ƛ t) ρ = (λ Γ₊ v → eval t (V̌al-subst.wk-subst₊ Γ₊ ρ ▻ v)) ,
                 eval-ƛ-well-behaved t ρ

  abstract

    eval-ƛ-well-behaved :
      ∀ {Γ Δ σ τ} {ρ̂ : Γ ⇨̂ Δ} (t : Γ ▻ σ ⊢ τ) (ρ : Sub V̌al ρ̂) →
      W̌ell-behaved _ _
        ((k U-π ˢ indexed-type σ ˢ c (indexed-type τ)) /I ρ)
        (λ Γ₊ v → eval t (V̌al-subst.wk-subst₊ Γ₊ ρ ▻ v))
    eval-ƛ-well-behaved {σ = σ} {τ = τ} t ρ Γ₊ v =
      let υ  = (k U-π ˢ indexed-type σ ˢ c (indexed-type τ)) /I ρ
          f  = λ Γ₊ v → eval t (V̌al-subst.wk-subst₊ Γ₊ ρ ▻ v)

      in begin
      [ (⟦ řeify-π _ _ υ f ⟧n /̂Val ŵk₊ Γ₊) ˢ ⟦̌ v ⟧ ]  ≡⟨ ˢ-cong (/̂Val-cong (P.sym $ eval-lemma-ƛ t ρ) P.refl) P.refl ⟩
      [ (c ⟦ t ⟧ /̂Val ⟦ ρ ⟧⇨ ∘̂ ŵk₊ Γ₊) ˢ ⟦̌ v ⟧     ]  ≡⟨ P.refl ⟩
      [ ⟦ t ⟧ /̂Val (⟦ ρ ⟧⇨ ∘̂ ŵk₊ Γ₊ ▻̂ ⟦̌ v ⟧)       ]  ≡⟨ eval-lemma t _ ⟩
      [ ⟦̌ eval t (V̌al-subst.wk-subst₊ Γ₊ ρ ▻ v) ⟧  ]  ∎

    -- An unfolding lemma.

    eval-· :
      ∀ {Γ Δ sp₁ sp₂ σ} {ρ̂ : Γ ⇨̂ Δ}
      (t₁ : Γ ⊢ π sp₁ sp₂ , σ) (t₂ : Γ ⊢ fst σ) (ρ : Sub V̌al ρ̂) →
      eval (t₁ · t₂) ρ ≅-V̌alue [ σ /I ρ ] eval t₁ ρ ·̌ eval t₂ ρ
    eval-· {σ = σ} t₁ t₂ ρ =
      drop-subst-V̌alue (λ v → snd σ /̂ ⟦ ρ ⟧⇨ ↑̂ /̂ ŝub v)
                       (≅-Value-⇒-≡ $ P.sym $ eval-lemma t₂ ρ)

    -- The evaluator is well-behaved.

    eval-lemma : ∀ {Γ Δ σ} {ρ̂ : Γ ⇨̂ Δ} (t : Γ ⊢ σ) (ρ : Sub V̌al ρ̂) →
                 ⟦ t ⟧ /Val ρ ≅-Value ⟦̌ eval t ρ ⟧
    eval-lemma (var x)             ρ = V̌al-subst./̂∋-⟦⟧⇨ x ρ
    eval-lemma (ƛ t)               ρ = eval-lemma-ƛ t ρ
    eval-lemma (_·_ {σ = σ} t₁ t₂) ρ = begin
      [ ⟦ t₁ · t₂ ⟧ /Val ρ                           ]  ≡⟨ P.refl ⟩
      [ (⟦ t₁ ⟧ /Val ρ) ˢ (⟦ t₂ ⟧ /Val ρ)            ]  ≡⟨ ˢ-cong (eval-lemma t₁ ρ) (eval-lemma t₂ ρ) ⟩
      [ ⟦̌_⟧ {σ = σ /I ρ} (eval t₁ ρ) ˢ ⟦̌ eval t₂ ρ ⟧ ]  ≡⟨ proj₂ (eval t₁ ρ) ε (eval t₂ ρ) ⟩
      [ ⟦̌ [ σ /I ρ ] eval t₁ ρ ·̌ eval t₂ ρ ⟧         ]  ≡⟨ ⟦̌⟧-cong (P.sym $ eval-· t₁ t₂ ρ) ⟩
      [ ⟦̌ eval (t₁ · t₂) ρ ⟧                         ]  ∎

    private

      eval-lemma-ƛ :
        ∀ {Γ Δ σ τ} {ρ̂ : Γ ⇨̂ Δ} (t : Γ ▻ σ ⊢ τ) (ρ : Sub V̌al ρ̂) →
        let υ = (k U-π ˢ indexed-type σ ˢ c (indexed-type τ)) /I ρ in
        ⟦ ƛ t ⟧ /Val ρ ≅-Value ⟦̌_⟧ {σ = υ} (eval (ƛ t) ρ)
      eval-lemma-ƛ {σ = σ} {τ = τ} t ρ =
        let υ  = (k U-π ˢ indexed-type σ ˢ c (indexed-type τ)) /I ρ
            f  = λ Γ₊ v → eval t (V̌al-subst.wk-subst₊ Γ₊ ρ ▻ v)
            ρ↑ = V̌al-subst.wk-subst₊ (σ / ρ ◅ ε) ρ ▻ v̌ar ⊙ zero

        in begin
        [ c ⟦ t ⟧ /Val ρ          ]  ≡⟨ P.refl ⟩
        [ c (⟦ t ⟧ /̂Val ⟦ ρ ⟧⇨ ↑̂) ]  ≡⟨ curry-cong (/̂Val-cong (P.refl {x = [ ⟦ t ⟧ ]}) (P.sym $ ∘̂-ŵk-▻̂-žero ⟦ ρ ⟧⇨ _)) ⟩
        [ c (⟦ t ⟧ /Val ρ↑)       ]  ≡⟨ curry-cong (eval-lemma t ρ↑) ⟩
        [ c ⟦̌ eval t ρ↑ ⟧         ]  ≡⟨ P.sym $ unfold-řeify-π υ f ⟩
        [ ⟦ řeify-π _ _ υ f ⟧n    ]  ∎

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

-- Can the following statements be proved?

-- open P using (_≡_)

-- goal : ∀ {Γ σ} (t₁ t₂ : Γ ⊢ σ) →
--        ⟦ t₁ ⟧ ≅-Value ⟦ t₂ ⟧ →
--        ∀ {Δ} {ρ̂ : Γ ⇨̂ Δ} (ρ : Sub V̌al ρ̂) → eval t₁ ρ ≡ eval t₂ ρ
-- goal t₁ t₂ ⟦t₁⟧≅⟦t₂⟧ ρ = {!!}

-- corollary : ∀ {Γ σ} (t₁ t₂ : Γ ⊢ σ) →
--             ⟦ t₁ ⟧ ≅-Value ⟦ t₂ ⟧ → normalise t₁ ≡ normalise t₂
-- corollary t₁ t₂ ⟦t₁⟧≅⟦t₂⟧ =
--   P.cong (řeify _) (goal t₁ t₂ ⟦t₁⟧≅⟦t₂⟧ V̌al-subst.id)

-- abstract

--   -- Properties required of a Kripke model (taken from Mitchell and
--   -- Moggi's "Kripke-style models for typed lambda calculus" and
--   -- adapted to the present setting).

--   -- No weakening amounts to nothing.

--   w̌k₊-ε : ∀ {Γ σ} (σ′ : Γ ⊢ σ type) (v : V̌alue Γ σ′) →
--           w̌k₊ σ′ ε v ≅-V̌alue v
--   w̌k₊-ε σ′ v = ?

--   -- Repeated weakening can be consolidated into one.
--   --
--   -- TODO: State in a pointfree way?

--   w̌k₊-w̌k₊ : ∀ {Γ σ} (σ′ : Γ ⊢ σ type) (v : V̌alue Γ σ′) Γ₊ Γ₊₊ →
--             w̌k₊ (σ′ /⊢t wk₊ Γ₊) Γ₊₊ (w̌k₊ σ′ Γ₊ v) ≅-V̌alue
--             w̌k₊ σ′ (Γ₊ ₊++₊ Γ₊₊) v
--   w̌k₊-w̌k₊ σ′ v Γ₊ Γ₊₊ = ?

--   -- Naturality.

--   w̌k₊-·̌ : ∀ {Γ σ τ} {σ′ : Γ ⊢ σ type} {τ′ : Γ ▻ σ ⊢ τ type} →
--           (f : V̌alue Γ (π σ′ τ′)) (v : V̌alue Γ σ′) Γ₊ →
--           w̌k₊ (τ′ /⊢t sub ⌊ řeify σ′ v ⌋) Γ₊ (f ·̌ v) ≅-V̌alue
--           w̌k₊ (π σ′ τ′) Γ₊ f ·̌ w̌k₊ σ′ Γ₊ v
--   w̌k₊-·̌ f v Γ₊ = ?

--   -- Extensionality.

--   -- Enough elements.
