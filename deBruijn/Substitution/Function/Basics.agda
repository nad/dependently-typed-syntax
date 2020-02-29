------------------------------------------------------------------------
-- Parallel substitutions (defined as functions)
------------------------------------------------------------------------

open import Data.Universe.Indexed

module deBruijn.Substitution.Function.Basics
  {i u e} {Uni : IndexedUniverse i u e} where

import Axiom.Extensionality.Propositional as E
import deBruijn.Context; open deBruijn.Context Uni
open import Function using (id; _∘_; _$_)
open import Level using (_⊔_)
open import Relation.Binary.PropositionalEquality as P using (_≡_)

open P.≡-Reasoning

-- Substitutions, represented as functions from variables to terms.

Sub : ∀ {t} (T : Term-like t) {Γ Δ : Ctxt} → Γ ⇨̂ Δ → Set _
Sub T = [ Var ⟶ T ]

private
 module Dummy {t} {T : Term-like t} where

  open Term-like T

  -- Interpretation of substitutions: context morphisms.

  ⟦_⟧⇨ : ∀ {Γ Δ} {ρ̂ : Γ ⇨̂ Δ} → Sub T ρ̂ → Γ ⇨̂ Δ
  ⟦_⟧⇨ {ρ̂ = ρ̂} _ = ρ̂

  -- Application of substitutions to types.

  infixl 8 _/I_ _/_

  _/I_ : ∀ {Γ Δ i} {ρ̂ : Γ ⇨̂ Δ} → IType Γ i → Sub T ρ̂ → IType Δ i
  σ /I ρ = σ /̂I ⟦ ρ ⟧⇨

  _/_ : ∀ {Γ Δ} {ρ̂ : Γ ⇨̂ Δ} → Type Γ → Sub T ρ̂ → Type Δ
  σ / ρ = σ /̂ ⟦ ρ ⟧⇨

  -- Application of substitutions to values.

  infixl 8 _/Val_

  _/Val_ : ∀ {Γ Δ σ} {ρ̂ : Γ ⇨̂ Δ} →
           Value Γ σ → Sub T ρ̂ → Value Δ (σ /̂ ρ̂)
  v /Val ρ = v /̂Val ⟦ ρ ⟧⇨

  -- Application of substitutions to context extensions.

  infixl 8 _/⁺_ _/₊_

  _/⁺_ : ∀ {Γ Δ} {ρ̂ : Γ ⇨̂ Δ} → Ctxt⁺ Γ → Sub T ρ̂ → Ctxt⁺ Δ
  Γ⁺ /⁺ ρ = Γ⁺ /̂⁺ ⟦ ρ ⟧⇨

  _/₊_ : ∀ {Γ Δ} {ρ̂ : Γ ⇨̂ Δ} → Ctxt₊ Γ → Sub T ρ̂ → Ctxt₊ Δ
  Γ₊ /₊ ρ = Γ₊ /̂₊ ⟦ ρ ⟧⇨

  -- Application of substitutions to variables.

  infixl 8 _/∋_ _/∋-lemma_

  _/∋_ : ∀ {Γ Δ σ} {ρ̂ : Γ ⇨̂ Δ} → Γ ∋ σ → (ρ : Sub T ρ̂) → Δ ⊢ σ / ρ
  x /∋ ρ = ρ · x

  _/∋-lemma_ : ∀ {Γ Δ σ} {ρ̂ : Γ ⇨̂ Δ} (x : Γ ∋ σ) (ρ : Sub T ρ̂) →
               x /̂∋ ⟦ ρ ⟧⇨ ≅-Value ⟦ x /∋ ρ ⟧
  x /∋-lemma ρ = corresponds ρ x

  app∋ : ∀ {Γ Δ} {ρ̂ : Γ ⇨̂ Δ} → Sub T ρ̂ → [ Var ⟶ T ] ρ̂
  app∋ ρ = record
    { function    = λ _ x → x /∋       ρ
    ; corresponds = λ _ x → x /∋-lemma ρ
    }

  -- Empty substitution.

  ε⇨ : ∀ {Δ} → Sub T ε̂[ Δ ]
  ε⇨ = record { function = λ _ (); corresponds = λ _ () }

  ε⇨[_] : ∀ Δ → Sub T ε̂[ Δ ]
  ε⇨[ _ ] = ε⇨

  -- Extends a substitution with another term.

  private

    -- This function is not local to _▻⇨[_]_ because a proof below
    -- fails to type check if the function depends on the proof
    -- component of the substitution.

    fun : ∀ {Γ Δ σ} {ρ̂ : Γ ⇨̂ Δ} →
          (∀ {τ} → Γ ∋ τ → Δ ⊢ τ /̂ ρ̂) →
          (t : Δ ⊢ σ /̂ ρ̂) →
          ∀ {τ} → Γ ▻ σ ∋ τ → Δ ⊢ τ /̂ (ρ̂ ▻̂ ⟦ t ⟧)
    fun f t zero    = t
    fun f t (suc x) = f x

  infixl 5 _▻⇨_ _▻⇨[_]_

  _▻⇨[_]_ : ∀ {Γ Δ} {ρ̂ : Γ ⇨̂ Δ}
            (ρ : Sub T ρ̂) σ (t : Δ ⊢ σ / ρ) → Sub T (ρ̂ ▻̂[ σ ] ⟦ t ⟧)
  _▻⇨[_]_ {Γ} {Δ} {ρ̂} ρ σ t =
    record { function = λ _ → fun (_·_ ρ) t; corresponds = λ _ → corr }
    where
    abstract
      corr : ∀ {τ} (x : Γ ▻ σ ∋ τ) →
             x /̂∋ (ρ̂ ▻̂ ⟦ t ⟧) ≅-Value ⟦ fun (_·_ ρ) t x ⟧
      corr zero    = P.refl
      corr (suc x) = x /∋-lemma ρ

  _▻⇨_ : ∀ {Γ Δ σ} {ρ̂ : Γ ⇨̂ Δ}
         (ρ : Sub T ρ̂) (t : Δ ⊢ σ / ρ) → Sub T (ρ̂ ▻̂[ σ ] ⟦ t ⟧)
  ρ ▻⇨ t = ρ ▻⇨[ _ ] t

  -- The tail of a nonempty substitution.

  tail : ∀ {Γ Δ σ} {ρ̂ : Γ ▻ σ ⇨̂ Δ} → Sub T ρ̂ → Sub T (t̂ail ρ̂)
  tail ρ = ρ [∘] weaken∋

  -- The head of a nonempty substitution.

  head : ∀ {Γ Δ σ} {ρ̂ : Γ ▻ σ ⇨̂ Δ} (ρ : Sub T ρ̂) → Δ ⊢ σ / tail ρ
  head ρ = zero /∋ ρ

  head-lemma : ∀ {Γ Δ σ} {ρ̂ : Γ ▻ σ ⇨̂ Δ} (ρ : Sub T ρ̂) →
               ĥead ⟦ ρ ⟧⇨ ≅-Value ⟦ head ρ ⟧
  head-lemma ρ = zero /∋-lemma ρ

  -- Equality of substitutions.

  infix 4 _≅-⇨_

  _≅-⇨_ : ∀ {Γ₁ Δ₁} {ρ̂₁ : Γ₁ ⇨̂ Δ₁} (ρ₁ : Sub T ρ̂₁)
            {Γ₂ Δ₂} {ρ̂₂ : Γ₂ ⇨̂ Δ₂} (ρ₂ : Sub T ρ̂₂) → Set _
  _≅-⇨_ = _≅-⟶_

  -- Certain uses of substitutivity can be removed.

  drop-subst-Sub :
    ∀ {a} {A : Set a} {x₁ x₂ : A} {Γ Δ}
    (f : A → Γ ⇨̂ Δ) {ρ} (eq : x₁ ≡ x₂) →
    P.subst (λ x → Sub T (f x)) eq ρ ≅-⇨ ρ
  drop-subst-Sub f P.refl = [ P.refl ]

  -- Some congruence lemmas.

  ε⇨-cong : ∀ {Δ₁ Δ₂} → Δ₁ ≅-Ctxt Δ₂ → ε⇨[ Δ₁ ] ≅-⇨ ε⇨[ Δ₂ ]
  ε⇨-cong P.refl = [ P.refl ]

  ▻⇨-cong :
    ∀ {Γ₁ Δ₁ σ₁} {ρ̂₁ : Γ₁ ⇨̂ Δ₁} {ρ₁ : Sub T ρ̂₁} {t₁ : Δ₁ ⊢ σ₁ / ρ₁}
      {Γ₂ Δ₂ σ₂} {ρ̂₂ : Γ₂ ⇨̂ Δ₂} {ρ₂ : Sub T ρ̂₂} {t₂ : Δ₂ ⊢ σ₂ / ρ₂} →
    σ₁ ≅-Type σ₂ → ρ₁ ≅-⇨ ρ₂ → t₁ ≅-⊢ t₂ →
    ρ₁ ▻⇨[ σ₁ ] t₁ ≅-⇨ ρ₂ ▻⇨[ σ₂ ] t₂
  ▻⇨-cong {ρ₁ = _ , _} {ρ₂ = ._ , _} P.refl [ P.refl ] P.refl =
    [ P.refl ]

  ⟦⟧⇨-cong : ∀ {Γ₁ Δ₁} {ρ̂₁ : Γ₁ ⇨̂ Δ₁} {ρ₁ : Sub T ρ̂₁}
               {Γ₂ Δ₂} {ρ̂₂ : Γ₂ ⇨̂ Δ₂} {ρ₂ : Sub T ρ̂₂} →
             ρ₁ ≅-⇨ ρ₂ → ⟦ ρ₁ ⟧⇨ ≅-⇨̂ ⟦ ρ₂ ⟧⇨
  ⟦⟧⇨-cong {ρ₁ = _ , _} {ρ₂ = ._ , _} [ P.refl ] = P.refl

  /I-cong :
    ∀ {i}
      {Γ₁ Δ₁} {ρ̂₁ : Γ₁ ⇨̂ Δ₁} {σ₁ : IType Γ₁ i} {ρ₁ : Sub T ρ̂₁}
      {Γ₂ Δ₂} {ρ̂₂ : Γ₂ ⇨̂ Δ₂} {σ₂ : IType Γ₂ i} {ρ₂ : Sub T ρ̂₂} →
    σ₁ ≅-IType σ₂ → ρ₁ ≅-⇨ ρ₂ → σ₁ /I ρ₁ ≅-IType σ₂ /I ρ₂
  /I-cong {ρ₁ = _ , _} {ρ₂ = ._ , _} P.refl [ P.refl ] = P.refl

  /-cong : ∀ {Γ₁ Δ₁ σ₁} {ρ̂₁ : Γ₁ ⇨̂ Δ₁} {ρ₁ : Sub T ρ̂₁}
             {Γ₂ Δ₂ σ₂} {ρ̂₂ : Γ₂ ⇨̂ Δ₂} {ρ₂ : Sub T ρ̂₂} →
           σ₁ ≅-Type σ₂ → ρ₁ ≅-⇨ ρ₂ → σ₁ / ρ₁ ≅-Type σ₂ / ρ₂
  /-cong {ρ₁ = _ , _} {ρ₂ = ._ , _} P.refl [ P.refl ] = P.refl

  /⁺-cong : ∀ {Γ₁ Δ₁ Γ⁺₁} {ρ̂₁ : Γ₁ ⇨̂ Δ₁} {ρ₁ : Sub T ρ̂₁}
              {Γ₂ Δ₂ Γ⁺₂} {ρ̂₂ : Γ₂ ⇨̂ Δ₂} {ρ₂ : Sub T ρ̂₂} →
            Γ⁺₁ ≅-Ctxt⁺ Γ⁺₂ → ρ₁ ≅-⇨ ρ₂ → Γ⁺₁ /⁺ ρ₁ ≅-Ctxt⁺ Γ⁺₂ /⁺ ρ₂
  /⁺-cong {ρ₁ = _ , _} {ρ₂ = ._ , _} P.refl [ P.refl ] = P.refl

  /₊-cong : ∀ {Γ₁ Δ₁ Γ₊₁} {ρ̂₁ : Γ₁ ⇨̂ Δ₁} {ρ₁ : Sub T ρ̂₁}
              {Γ₂ Δ₂ Γ₊₂} {ρ̂₂ : Γ₂ ⇨̂ Δ₂} {ρ₂ : Sub T ρ̂₂} →
            Γ₊₁ ≅-Ctxt₊ Γ₊₂ → ρ₁ ≅-⇨ ρ₂ → Γ₊₁ /₊ ρ₁ ≅-Ctxt₊ Γ₊₂ /₊ ρ₂
  /₊-cong {ρ₁ = _ , _} {ρ₂ = ._ , _} P.refl [ P.refl ] = P.refl

  /∋-cong : ∀ {Γ₁ Δ₁ σ₁} {x₁ : Γ₁ ∋ σ₁} {ρ̂₁ : Γ₁ ⇨̂ Δ₁} {ρ₁ : Sub T ρ̂₁}
              {Γ₂ Δ₂ σ₂} {x₂ : Γ₂ ∋ σ₂} {ρ̂₂ : Γ₂ ⇨̂ Δ₂} {ρ₂ : Sub T ρ̂₂} →
            x₁ ≅-∋ x₂ → ρ₁ ≅-⇨ ρ₂ → x₁ /∋ ρ₁ ≅-⊢ x₂ /∋ ρ₂
  /∋-cong {ρ₁ = _ , _} {ρ₂ = ._ , _} P.refl [ P.refl ] = P.refl

  tail-cong : ∀ {Γ₁ Δ₁ σ₁} {ρ̂₁ : Γ₁ ▻ σ₁ ⇨̂ Δ₁} {ρ₁ : Sub T ρ̂₁}
                {Γ₂ Δ₂ σ₂} {ρ̂₂ : Γ₂ ▻ σ₂ ⇨̂ Δ₂} {ρ₂ : Sub T ρ̂₂} →
              ρ₁ ≅-⇨ ρ₂ → tail ρ₁ ≅-⇨ tail ρ₂
  tail-cong {ρ₁ = _ , _} {ρ₂ = ._ , _} [ P.refl ] = [ P.refl ]

  head-cong : ∀ {Γ₁ Δ₁ σ₁} {ρ̂₁ : Γ₁ ▻ σ₁ ⇨̂ Δ₁} {ρ₁ : Sub T ρ̂₁}
                {Γ₂ Δ₂ σ₂} {ρ̂₂ : Γ₂ ▻ σ₂ ⇨̂ Δ₂} {ρ₂ : Sub T ρ̂₂} →
              ρ₁ ≅-⇨ ρ₂ → head ρ₁ ≅-⊢ head ρ₂
  head-cong {ρ₁ = _ , _} {ρ₂ = ._ , _} [ P.refl ] = P.refl

  abstract

    -- Some eta-laws, based on the assumption of extensionality.

    -- Eta in empty contexts.

    ηε : E.Extensionality (i ⊔ u ⊔ e) (i ⊔ u ⊔ e ⊔ t) →
         ∀ {Δ} {ρ̂ : ε ⇨̂ Δ} (ρ : Sub T ρ̂) → ρ ≅-⇨ ε⇨[ Δ ]
    ηε ext ρ = extensional-equality₁ ext P.refl (λ ())

    -- Eta in non-empty contexts.

    η▻ : E.Extensionality (i ⊔ u ⊔ e) (i ⊔ u ⊔ e ⊔ t) →
         ∀ {Γ Δ σ} {ρ̂ : Γ ▻ σ ⇨̂ Δ} (ρ : Sub T ρ̂) →
         ρ ≅-⇨ tail ρ ▻⇨[ σ ] head ρ
    η▻ ext {Γ} {σ = σ} {ρ̂} ρ = extensional-equality₂ ext lemma₁ lemma₂
      where
      open Term-like Var using () renaming (_≅-⊢_ to _≅-∋′_)

      lemma₁ : ρ̂ ≅-⇨̂ t̂ail ρ̂ ▻̂[ σ ] ⟦ head ρ ⟧
      lemma₁ = begin
        [ ρ̂                   ]  ≡⟨ P.refl ⟩
        [ t̂ail ρ̂ ▻̂ ĥead ρ̂     ]  ≡⟨ ▻̂-cong P.refl P.refl (head-lemma ρ) ⟩
        [ t̂ail ρ̂ ▻̂ ⟦ head ρ ⟧ ]  ∎

      lemma₂′ : ∀ {τ} (x : Γ ▻ σ ∋ τ) →
                x /∋ ρ ≅-⊢ x /∋ (tail ρ ▻⇨[ σ ] head ρ)
      lemma₂′ zero    = P.refl
      lemma₂′ (suc x) = P.refl

      lemma₂ : ∀ {τ₁} {x₁ : Γ ▻ σ ∋ τ₁}
                 {τ₂} {x₂ : Γ ▻ σ ∋ τ₂} →
               x₁ ≅-∋′ x₂ → x₁ /∋ ρ ≅-⊢ x₂ /∋ (tail ρ ▻⇨[ σ ] head ρ)
      lemma₂ {x₁ = x} P.refl = lemma₂′ x

    -- Two substitutions are equal if their indices are equal and
    -- their projections are pairwise equal (assuming extensionality).

    extensionality :
      E.Extensionality (i ⊔ u ⊔ e) (i ⊔ u ⊔ e ⊔ t) →
      ∀ {Γ Δ₁} {ρ̂₁ : Γ ⇨̂ Δ₁} {ρ₁ : Sub T ρ̂₁}
          {Δ₂} {ρ̂₂ : Γ ⇨̂ Δ₂} {ρ₂ : Sub T ρ̂₂} →
      Δ₁ ≅-Ctxt Δ₂ → (∀ {σ} (x : Γ ∋ σ) → x /∋ ρ₁ ≅-⊢ x /∋ ρ₂) →
      ρ₁ ≅-⇨ ρ₂
    extensionality ext {ε} {ρ₁ = ρ₁} {ρ₂ = ρ₂} P.refl hyp =
      ρ₁  ≅-⟶⟨ ηε ext ρ₁ ⟩
      ε⇨  ≅-⟶⟨ sym-⟶ $ ηε ext ρ₂ ⟩
      ρ₂  ∎-⟶
    extensionality ext {Γ ▻ σ} {ρ₁ = ρ₁} {ρ₂ = ρ₂} P.refl hyp =
      ρ₁                  ≅-⟶⟨ η▻ ext ρ₁ ⟩
      tail ρ₁ ▻⇨ head ρ₁  ≅-⟶⟨ ▻⇨-cong P.refl
                                       (extensionality ext P.refl (hyp ∘ suc))
                                       (hyp zero) ⟩
      tail ρ₂ ▻⇨ head ρ₂  ≅-⟶⟨ sym-⟶ $ η▻ ext ρ₂ ⟩
      ρ₂                  ∎-⟶

open Dummy public
