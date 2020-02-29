------------------------------------------------------------------------
-- Context extensions with the rightmost element in the outermost
-- position
------------------------------------------------------------------------

open import Data.Universe.Indexed

module deBruijn.Context.Extension.Right
  {i u e} (Uni : IndexedUniverse i u e) where

import deBruijn.Context.Basics as Basics
open import Data.Product
open import Function
open import Level using (_⊔_)
open import Relation.Binary.PropositionalEquality as P using (_≡_)

open Basics Uni
open P.≡-Reasoning

------------------------------------------------------------------------
-- Context extensions along with various operations making use of them

mutual

  -- Context extensions.

  infixl 5 _▻_

  data Ctxt⁺ (Γ : Ctxt) : Set (i ⊔ u ⊔ e) where
    ε   : Ctxt⁺ Γ
    _▻_ : (Γ⁺ : Ctxt⁺ Γ) (σ : Type (Γ ++⁺ Γ⁺)) → Ctxt⁺ Γ

  -- Appends a context extension to a context.

  infixl 5 _++⁺_

  _++⁺_ : (Γ : Ctxt) → Ctxt⁺ Γ → Ctxt
  Γ ++⁺ ε        = Γ
  Γ ++⁺ (Γ⁺ ▻ σ) = (Γ ++⁺ Γ⁺) ▻ σ

-- A synonym.

ε⁺[_] : (Γ : Ctxt) → Ctxt⁺ Γ
ε⁺[ _ ] = ε

mutual

  -- Appends a context extension to a context extension.

  infixl 5 _⁺++⁺_

  _⁺++⁺_ : ∀ {Γ} (Γ⁺ : Ctxt⁺ Γ) → Ctxt⁺ (Γ ++⁺ Γ⁺) → Ctxt⁺ Γ
  Γ⁺ ⁺++⁺ ε         = Γ⁺
  Γ⁺ ⁺++⁺ (Γ⁺⁺ ▻ σ) = (Γ⁺ ⁺++⁺ Γ⁺⁺) ▻ P.subst Type (++⁺-++⁺ Γ⁺ Γ⁺⁺) σ

  abstract

    -- _++⁺_/_⁺++⁺_ are associative.

    ++⁺-++⁺ : ∀ {Γ} Γ⁺ Γ⁺⁺ →
              Γ ++⁺ Γ⁺ ++⁺ Γ⁺⁺ ≅-Ctxt Γ ++⁺ (Γ⁺ ⁺++⁺ Γ⁺⁺)
    ++⁺-++⁺ Γ⁺ ε         = P.refl
    ++⁺-++⁺ Γ⁺ (Γ⁺⁺ ▻ σ) =
      ▻-cong (P.sym $ drop-subst-Type id (++⁺-++⁺ Γ⁺ Γ⁺⁺))

mutual

  -- Application of context morphisms to context extensions.

  infixl 8 _/̂⁺_

  _/̂⁺_ : ∀ {Γ Δ} → Ctxt⁺ Γ → Γ ⇨̂ Δ → Ctxt⁺ Δ
  ε        /̂⁺ ρ̂ = ε
  (Γ⁺ ▻ σ) /̂⁺ ρ̂ = Γ⁺ /̂⁺ ρ̂ ▻ σ /̂ ρ̂ ↑̂⁺ Γ⁺

  -- N-ary lifting of context morphisms.

  infixl 10 _↑̂⁺_

  _↑̂⁺_ : ∀ {Γ Δ} (ρ̂ : Γ ⇨̂ Δ) Γ⁺ → Γ ++⁺ Γ⁺ ⇨̂ Δ ++⁺ Γ⁺ /̂⁺ ρ̂
  ρ̂ ↑̂⁺ ε        = ρ̂
  ρ̂ ↑̂⁺ (Γ⁺ ▻ σ) = (ρ̂ ↑̂⁺ Γ⁺) ↑̂

-- N-ary weakening.

ŵk⁺ : ∀ {Γ} Γ⁺ → Γ ⇨̂ Γ ++⁺ Γ⁺
ŵk⁺ ε        = îd
ŵk⁺ (Γ⁺ ▻ σ) = ŵk⁺ Γ⁺ ∘̂ ŵk[ σ ]

------------------------------------------------------------------------
-- Equality

-- Equality of context extensions.

record [Ctxt⁺] : Set (i ⊔ u ⊔ e) where
  constructor [_]
  field
    {Γ} : Ctxt
    Γ⁺  : Ctxt⁺ Γ

infix 4 _≅-Ctxt⁺_

_≅-Ctxt⁺_ : ∀ {Γ₁} (Γ⁺₁ : Ctxt⁺ Γ₁)
              {Γ₂} (Γ⁺₂ : Ctxt⁺ Γ₂) → Set _
Γ⁺₁ ≅-Ctxt⁺ Γ⁺₂ = _≡_ {A = [Ctxt⁺]} [ Γ⁺₁ ] [ Γ⁺₂ ]

≅-Ctxt⁺-⇒-≡ : ∀ {Γ} {Γ⁺₁ Γ⁺₂ : Ctxt⁺ Γ} →
              Γ⁺₁ ≅-Ctxt⁺ Γ⁺₂ → Γ⁺₁ ≡ Γ⁺₂
≅-Ctxt⁺-⇒-≡ P.refl = P.refl

-- Certain uses of substitutivity can be removed.

drop-subst-Ctxt⁺ : ∀ {a} {A : Set a} {x₁ x₂}
                   (f : A → Ctxt) {Γ⁺} (x₁≡x₂ : x₁ ≡ x₂) →
                   P.subst (λ x → Ctxt⁺ (f x)) x₁≡x₂ Γ⁺ ≅-Ctxt⁺ Γ⁺
drop-subst-Ctxt⁺ f P.refl = P.refl

------------------------------------------------------------------------
-- Some congruences

ε⁺-cong : ∀ {Γ₁ Γ₂} → Γ₁ ≅-Ctxt Γ₂ → ε⁺[ Γ₁ ] ≅-Ctxt⁺ ε⁺[ Γ₂ ]
ε⁺-cong P.refl = P.refl

▻⁺-cong : ∀ {Γ₁} {Γ⁺₁ : Ctxt⁺ Γ₁} {σ₁}
            {Γ₂} {Γ⁺₂ : Ctxt⁺ Γ₂} {σ₂} →
          Γ⁺₁ ≅-Ctxt⁺ Γ⁺₂ → σ₁ ≅-Type σ₂ →
          Γ⁺₁ ▻ σ₁ ≅-Ctxt⁺ Γ⁺₂ ▻ σ₂
▻⁺-cong P.refl P.refl = P.refl

++⁺-cong : ∀ {Γ₁} {Γ⁺₁ : Ctxt⁺ Γ₁} {Γ₂} {Γ⁺₂ : Ctxt⁺ Γ₂} →
           Γ⁺₁ ≅-Ctxt⁺ Γ⁺₂ → Γ₁ ++⁺ Γ⁺₁ ≅-Ctxt Γ₂ ++⁺ Γ⁺₂
++⁺-cong P.refl = P.refl

⁺++⁺-cong : ∀ {Γ₁ Γ⁺₁} {Γ⁺⁺₁ : Ctxt⁺ (Γ₁ ++⁺ Γ⁺₁)}
              {Γ₂ Γ⁺₂} {Γ⁺⁺₂ : Ctxt⁺ (Γ₂ ++⁺ Γ⁺₂)} →
            Γ⁺₁ ≅-Ctxt⁺ Γ⁺₂ → Γ⁺⁺₁ ≅-Ctxt⁺ Γ⁺⁺₂ →
            Γ⁺₁ ⁺++⁺ Γ⁺⁺₁ ≅-Ctxt⁺ Γ⁺₂ ⁺++⁺ Γ⁺⁺₂
⁺++⁺-cong P.refl P.refl = P.refl

/̂⁺-cong : ∀ {Γ₁ Δ₁} {Γ⁺₁ : Ctxt⁺ Γ₁} {ρ̂₁ : Γ₁ ⇨̂ Δ₁}
            {Γ₂ Δ₂} {Γ⁺₂ : Ctxt⁺ Γ₂} {ρ̂₂ : Γ₂ ⇨̂ Δ₂} →
          Γ⁺₁ ≅-Ctxt⁺ Γ⁺₂ → ρ̂₁ ≅-⇨̂ ρ̂₂ → Γ⁺₁ /̂⁺ ρ̂₁ ≅-Ctxt⁺ Γ⁺₂ /̂⁺ ρ̂₂
/̂⁺-cong P.refl P.refl = P.refl

↑̂⁺-cong : ∀ {Γ₁ Δ₁} {ρ̂₁ : Γ₁ ⇨̂ Δ₁} {Γ⁺₁ : Ctxt⁺ Γ₁}
            {Γ₂ Δ₂} {ρ̂₂ : Γ₂ ⇨̂ Δ₂} {Γ⁺₂ : Ctxt⁺ Γ₂} →
          ρ̂₁ ≅-⇨̂ ρ̂₂ → Γ⁺₁ ≅-Ctxt⁺ Γ⁺₂ → ρ̂₁ ↑̂⁺ Γ⁺₁ ≅-⇨̂ ρ̂₂ ↑̂⁺ Γ⁺₂
↑̂⁺-cong P.refl P.refl = P.refl

ŵk⁺-cong : ∀ {Γ₁} {Γ⁺₁ : Ctxt⁺ Γ₁} {Γ₂} {Γ⁺₂ : Ctxt⁺ Γ₂} →
           Γ⁺₁ ≅-Ctxt⁺ Γ⁺₂ → ŵk⁺ Γ⁺₁ ≅-⇨̂ ŵk⁺ Γ⁺₂
ŵk⁺-cong P.refl = P.refl

------------------------------------------------------------------------
-- Some properties

abstract

  -- Γ ++⁺_ has at most one right identity.

  ++⁺-right-identity-unique :
    ∀ {Γ} (Γ⁺ : Ctxt⁺ Γ) → Γ ≅-Ctxt Γ ++⁺ Γ⁺ → Γ⁺ ≅-Ctxt⁺ ε⁺[ Γ ]
  ++⁺-right-identity-unique         ε        _  = P.refl
  ++⁺-right-identity-unique {ε}     (Γ⁺ ▻ σ) ()
  ++⁺-right-identity-unique {Γ ▻ τ} (Γ⁺ ▻ σ) eq
    with ++⁺-right-identity-unique (ε ▻ τ ⁺++⁺ Γ⁺) (begin
           Γ                      ≡⟨ proj₁ $ ▻-injective eq ⟩
           Γ ▻ τ ++⁺ Γ⁺           ≡⟨ ++⁺-++⁺ (ε ▻ τ) Γ⁺ ⟩
           Γ ++⁺ (ε ▻ τ ⁺++⁺ Γ⁺)  ∎)
  ++⁺-right-identity-unique {Γ ▻ τ} (ε     ▻ σ) eq | ()
  ++⁺-right-identity-unique {Γ ▻ τ} (_ ▻ _ ▻ σ) eq | ()

  -- _++⁺_ is left cancellative.

  cancel-++⁺-left : ∀ {Γ} (Γ⁺₁ Γ⁺₂ : Ctxt⁺ Γ) →
                    Γ ++⁺ Γ⁺₁ ≅-Ctxt Γ ++⁺ Γ⁺₂ → Γ⁺₁ ≅-Ctxt⁺ Γ⁺₂
  cancel-++⁺-left ε          ε          _  = P.refl
  cancel-++⁺-left (Γ⁺₁ ▻ σ₁) (Γ⁺₂ ▻ σ₂) eq with ▻-injective eq
  ... | eq₁ , eq₂ = ▻⁺-cong (cancel-++⁺-left Γ⁺₁ Γ⁺₂ eq₁) eq₂
  cancel-++⁺-left ε (Γ⁺₂ ▻ σ₂) eq
    with ++⁺-right-identity-unique (Γ⁺₂ ▻ σ₂) eq
  ... | ()
  cancel-++⁺-left (Γ⁺₁ ▻ σ₁) ε eq
    with ++⁺-right-identity-unique (Γ⁺₁ ▻ σ₁) (P.sym eq)
  ... | ()

  mutual

    -- The identity substitution has no effect.

    /̂⁺-îd : ∀ {Γ} (Γ⁺ : Ctxt⁺ Γ) → Γ⁺ /̂⁺ îd ≅-Ctxt⁺ Γ⁺
    /̂⁺-îd ε        = P.refl
    /̂⁺-îd (Γ⁺ ▻ σ) = ▻⁺-cong (/̂⁺-îd Γ⁺) (/̂-cong P.refl (îd-↑̂⁺ Γ⁺))

    -- The n-ary lifting of the identity substitution is the identity
    -- substitution.

    îd-↑̂⁺ : ∀ {Γ} (Γ⁺ : Ctxt⁺ Γ) → îd ↑̂⁺ Γ⁺ ≅-⇨̂ îd[ Γ ++⁺ Γ⁺ ]
    îd-↑̂⁺ ε        = P.refl
    îd-↑̂⁺ (Γ⁺ ▻ σ) = begin
      [ (îd ↑̂⁺ Γ⁺) ↑̂ ]  ≡⟨ ↑̂-cong (îd-↑̂⁺ Γ⁺) P.refl ⟩
      [ îd ↑̂         ]  ≡⟨ P.refl ⟩
      [ îd           ]  ∎

  -- The identity substitution has no effect even if lifted.

  /̂-îd-↑̂⁺ : ∀ {Γ} Γ⁺ (σ : Type (Γ ++⁺ Γ⁺)) → σ /̂ îd ↑̂⁺ Γ⁺ ≅-Type σ
  /̂-îd-↑̂⁺ Γ⁺ σ = begin
    [ σ /̂ îd ↑̂⁺ Γ⁺ ]  ≡⟨ /̂-cong (P.refl {x = [ σ ]}) (îd-↑̂⁺ Γ⁺) ⟩
    [ σ /̂ îd       ]  ≡⟨ P.refl ⟩
    [ σ            ]  ∎

  mutual

    -- Applying two substitutions is equivalent to applying their
    -- composition.

    /̂⁺-∘̂ : ∀ {Γ Δ Ε} Γ⁺ (ρ̂₁ : Γ ⇨̂ Δ) (ρ̂₂ : Δ ⇨̂ Ε) →
           Γ⁺ /̂⁺ ρ̂₁ ∘̂ ρ̂₂ ≅-Ctxt⁺ Γ⁺ /̂⁺ ρ̂₁ /̂⁺ ρ̂₂
    /̂⁺-∘̂ ε        ρ̂₁ ρ̂₂ = P.refl
    /̂⁺-∘̂ (Γ⁺ ▻ σ) ρ̂₁ ρ̂₂ =
      ▻⁺-cong (/̂⁺-∘̂ Γ⁺ ρ̂₁ ρ̂₂) (/̂-cong (P.refl {x = [ σ ]}) (∘̂-↑̂⁺ ρ̂₁ ρ̂₂ Γ⁺))

    -- _↑̂⁺_ distributes over _∘̂_.

    ∘̂-↑̂⁺ : ∀ {Γ Δ Ε} (ρ̂₁ : Γ ⇨̂ Δ) (ρ̂₂ : Δ ⇨̂ Ε) Γ⁺ →
           (ρ̂₁ ∘̂ ρ̂₂) ↑̂⁺ Γ⁺ ≅-⇨̂ ρ̂₁ ↑̂⁺ Γ⁺ ∘̂ ρ̂₂ ↑̂⁺ (Γ⁺ /̂⁺ ρ̂₁)
    ∘̂-↑̂⁺ ρ̂₁ ρ̂₂ ε        = P.refl
    ∘̂-↑̂⁺ ρ̂₁ ρ̂₂ (Γ⁺ ▻ σ) = begin
      [ ((ρ̂₁ ∘̂ ρ̂₂) ↑̂⁺ Γ⁺) ↑̂                   ]  ≡⟨ ↑̂-cong (∘̂-↑̂⁺ ρ̂₁ ρ̂₂ Γ⁺) P.refl ⟩
      [ (ρ̂₁ ↑̂⁺ Γ⁺ ∘̂ ρ̂₂ ↑̂⁺ (Γ⁺ /̂⁺ ρ̂₁)) ↑̂       ]  ≡⟨ P.refl ⟩
      [ (ρ̂₁ ↑̂⁺ Γ⁺) ↑̂ σ ∘̂ (ρ̂₂ ↑̂⁺ (Γ⁺ /̂⁺ ρ̂₁)) ↑̂ ]  ∎

  -- A corollary.

  /̂-↑̂⁺-/̂-ŵk-↑̂⁺ : ∀ {Γ Δ} σ (ρ̂ : Γ ⇨̂ Δ) (Γ⁺ : Ctxt⁺ Γ) τ →
                 τ /̂ ρ̂ ↑̂⁺ Γ⁺ /̂ ŵk[ σ /̂ ρ̂ ] ↑̂⁺ (Γ⁺ /̂⁺ ρ̂) ≅-Type
                 τ /̂ ŵk[ σ ] ↑̂⁺ Γ⁺ /̂ ρ̂ ↑̂ ↑̂⁺ (Γ⁺ /̂⁺ ŵk)
  /̂-↑̂⁺-/̂-ŵk-↑̂⁺ σ ρ̂ Γ⁺ τ = /̂-cong (P.refl {x = [ τ ]}) (begin
    [ ρ̂ ↑̂⁺ Γ⁺ ∘̂ ŵk ↑̂⁺ (Γ⁺ /̂⁺ ρ̂)         ]  ≡⟨ P.sym $ ∘̂-↑̂⁺ ρ̂ ŵk Γ⁺ ⟩
    [ (ρ̂ ∘̂ ŵk) ↑̂⁺ Γ⁺                    ]  ≡⟨ P.refl ⟩
    [ (ŵk[ σ ] ∘̂ ρ̂ ↑̂) ↑̂⁺ Γ⁺             ]  ≡⟨ ∘̂-↑̂⁺ ŵk[ σ ] (ρ̂ ↑̂) Γ⁺ ⟩
    [ ŵk[ σ ] ↑̂⁺ Γ⁺ ∘̂ ρ̂ ↑̂ ↑̂⁺ (Γ⁺ /̂⁺ ŵk) ]  ∎)

  -- ŵk⁺ commutes (modulo lifting) with arbitrary context morphisms.

  ∘̂-ŵk⁺ : ∀ {Γ Δ} (ρ̂ : Γ ⇨̂ Δ) Γ⁺ →
          ρ̂ ∘̂ ŵk⁺ (Γ⁺ /̂⁺ ρ̂) ≅-⇨̂ ŵk⁺ Γ⁺ ∘̂ ρ̂ ↑̂⁺ Γ⁺
  ∘̂-ŵk⁺ ρ̂ ε        = P.refl
  ∘̂-ŵk⁺ ρ̂ (Γ⁺ ▻ σ) = begin
    [ ρ̂ ∘̂ ŵk⁺ (Γ⁺ /̂⁺ ρ̂) ∘̂ ŵk         ]  ≡⟨ ∘̂-cong (∘̂-ŵk⁺ ρ̂ Γ⁺) P.refl ⟩
    [ ŵk⁺ Γ⁺ ∘̂ ρ̂ ↑̂⁺ Γ⁺ ∘̂ ŵk          ]  ≡⟨ P.refl ⟩
    [ ŵk⁺ Γ⁺ ∘̂ ŵk[ σ ] ∘̂ (ρ̂ ↑̂⁺ Γ⁺) ↑̂ ]  ∎

  -- ŵk⁺ is homomorphic with respect to _⁺++⁺_/_∘̂_.

  ŵk⁺-⁺++⁺ : ∀ {Γ} (Γ⁺ : Ctxt⁺ Γ) (Γ⁺⁺ : Ctxt⁺ (Γ ++⁺ Γ⁺)) →
             ŵk⁺ (Γ⁺ ⁺++⁺ Γ⁺⁺) ≅-⇨̂ ŵk⁺ Γ⁺ ∘̂ ŵk⁺ Γ⁺⁺
  ŵk⁺-⁺++⁺ Γ⁺ ε         = P.refl
  ŵk⁺-⁺++⁺ Γ⁺ (Γ⁺⁺ ▻ σ) =
    ∘̂-cong (ŵk⁺-⁺++⁺ Γ⁺ Γ⁺⁺)
           (ŵk-cong (drop-subst-Type id (++⁺-++⁺ Γ⁺ Γ⁺⁺)))

  -- Two n-ary liftings can be merged into one.

  ↑̂⁺-⁺++⁺ : ∀ {Γ Δ} (ρ̂ : Γ ⇨̂ Δ) Γ⁺ Γ⁺⁺ →
            ρ̂ ↑̂⁺ (Γ⁺ ⁺++⁺ Γ⁺⁺) ≅-⇨̂ ρ̂ ↑̂⁺ Γ⁺ ↑̂⁺ Γ⁺⁺
  ↑̂⁺-⁺++⁺ ρ̂ Γ⁺ ε         = P.refl
  ↑̂⁺-⁺++⁺ ρ̂ Γ⁺ (Γ⁺⁺ ▻ σ) = begin
    [ (ρ̂ ↑̂⁺ (Γ⁺ ⁺++⁺ Γ⁺⁺)) ↑̂ ]  ≡⟨ ↑̂-cong (↑̂⁺-⁺++⁺ ρ̂ Γ⁺ Γ⁺⁺) (drop-subst-Type id (++⁺-++⁺ Γ⁺ Γ⁺⁺)) ⟩
    [ (ρ̂ ↑̂⁺ Γ⁺ ↑̂⁺ Γ⁺⁺) ↑̂     ]  ∎

  -- _/̂⁺_ distributes over _⁺++⁺_ (sort of).

  ++⁺-⁺++⁺-/̂⁺ :
    ∀ {Γ Δ} (ρ̂ : Γ ⇨̂ Δ) Γ⁺ Γ⁺⁺ →
    Δ ++⁺ (Γ⁺ ⁺++⁺ Γ⁺⁺) /̂⁺ ρ̂ ≅-Ctxt Δ ++⁺ Γ⁺ /̂⁺ ρ̂ ++⁺ Γ⁺⁺ /̂⁺ ρ̂ ↑̂⁺ Γ⁺
  ++⁺-⁺++⁺-/̂⁺         ρ̂ Γ⁺ ε         = P.refl
  ++⁺-⁺++⁺-/̂⁺ {Δ = Δ} ρ̂ Γ⁺ (Γ⁺⁺ ▻ σ) = begin
    Δ ++⁺ (Γ⁺ ⁺++⁺ Γ⁺⁺) /̂⁺ ρ̂ ▻
      P.subst Type (++⁺-++⁺ Γ⁺ Γ⁺⁺) σ /̂ ρ̂ ↑̂⁺ (Γ⁺ ⁺++⁺ Γ⁺⁺)  ≡⟨ ▻-cong (/̂-cong (drop-subst-Type id (++⁺-++⁺ Γ⁺ Γ⁺⁺))
                                                                              (↑̂⁺-⁺++⁺ ρ̂ Γ⁺ Γ⁺⁺)) ⟩
    Δ ++⁺ Γ⁺ /̂⁺ ρ̂ ++⁺ Γ⁺⁺ /̂⁺ ρ̂ ↑̂⁺ Γ⁺ ▻ σ /̂ ρ̂ ↑̂⁺ Γ⁺ ↑̂⁺ Γ⁺⁺   ∎
