------------------------------------------------------------------------
-- A Kripke model
------------------------------------------------------------------------

import Level
open import Universe

module README.DependentlyTyped.Kripke-model
  {Uni₀ : Universe Level.zero Level.zero}
  where

open import Data.Product
  using (∃; _,_) renaming (curry to c; uncurry to uc)
open import deBruijn.Substitution.Data
import deBruijn.TermLike as TermLike
open import Function using (_$_; _ˢ_) renaming (const to k)
open import README.DependentlyTyped.NormalForm
open import README.DependentlyTyped.Substitution
import README.DependentlyTyped.Term as Term; open Term Uni₀
open import Relation.Binary.PropositionalEquality as P using (_≡_)

open P.≡-Reasoning
open TermLike Uni hiding (·-cong) renaming (_·_ to _⊙_)

-- The family of types which forms a Kripke model.

import README.DependentlyTyped.Kripke-model.Definition as Definition
open Definition {Uni₀} public

-- Values paired up with syntactic types.

⟨V̌alue⟩ : (Γ : Ctxt) → Type Γ → Set
⟨V̌alue⟩ Γ σ = ∃ λ (σ′ : Γ ⊢ σ type) → V̌alue Γ σ′

-- The semantics of a value.

⟦̌_⟧ : ∀ {Γ σ} → ⟨V̌alue⟩ Γ σ → Value Γ σ
⟦̌ (σ′ , v) ⟧ = ⟦ řeify σ′ v ⟧n

-- Values are term-like.

V̌al : Term-like _
V̌al = record
  { _⊢_ = ⟨V̌alue⟩
  ; ⟦_⟧ = ⟦̌_⟧
  }

open Term-like V̌al public
  using ([_])
  renaming ( _≅-⊢_ to _≅-V̌al_
           ; drop-subst-⊢ to drop-subst-V̌al; ⟦⟧-cong to ⟦̌⟧-cong
           )

-- Weakening.

w̌k : ∀ {Γ σ τ} → ⟨V̌alue⟩ Γ τ → ⟨V̌alue⟩ (Γ ▻ σ) (τ /̂ ŵk)
w̌k         (⋆     , t) = (⋆ , t /⊢n Renaming.wk)
w̌k {Γ} {σ} (el t′ , t) =
  P.subst (λ v → ⟨V̌alue⟩ (Γ ▻ σ) (k U.el ˢ v)) (P.sym lemma)
          ( el (t′ /⊢ wk)
          , P.subst (λ v → Γ ▻ σ ⊢ k U.el ˢ v ⟨ ne ⟩) lemma
                    (t /⊢n Renaming.wk)
          )
  where lemma = ≅-Value-⇒-≡ $ corresponds (app wk) t′
w̌k {Γ} {σ} (π τ′ υ′ , f) =
  π (τ′ /⊢t wk) (υ′ /⊢t wk ↑) , λ Γ⁺ v →
  let v₀ : V̌alue (Γ ▻ σ ++ Γ⁺) (τ′ /⊢t wk /⊢t wk⁺ Γ⁺)
      v₀ = v

      v′ : V̌alue (Γ ++ (ε ▻ σ ++⁺ Γ⁺)) (τ′ /⊢t wk⁺ (ε ▻ σ ++⁺ Γ⁺))
      v′ = {!!}

      v″ : V̌alue (Γ ++ (ε ▻ σ ++⁺ Γ⁺)) (υ′ /⊢t wk⁺ (ε ▻ σ ++⁺ Γ⁺) ↑ ∘ sub ⌊ řeify (τ′ /⊢t wk⁺ (ε ▻ σ ++⁺ Γ⁺)) v′ ⌋)
      v″ = f (ε ▻ σ ++⁺ Γ⁺) v′

      v‴ : V̌alue (Γ ▻ σ ++ Γ⁺) (υ′ /⊢t wk ↑ /⊢t wk⁺ Γ⁺ ↑ ∘ sub ⌊ řeify (τ′ /⊢t wk /⊢t wk⁺ Γ⁺) v ⌋)
      v‴ = {!!}
  in v‴

w̌k⁺ : ∀ {Γ τ} → ⟨V̌alue⟩ Γ τ → ∀ Γ⁺ → ⟨V̌alue⟩ (Γ ++ Γ⁺) (τ /̂ ŵk⁺ Γ⁺)
w̌k⁺     (⋆     , t) Γ⁺ = (⋆ , t /⊢n Renaming.wk⁺ Γ⁺)
w̌k⁺ {Γ} (el t′ , t) Γ⁺ =
  P.subst (λ v → ⟨V̌alue⟩ (Γ ++ Γ⁺) (k U.el ˢ v)) (P.sym lemma)
          ( el (t′ /⊢ wk⁺ Γ⁺)
          , P.subst (λ v → Γ ++ Γ⁺ ⊢ k U.el ˢ v ⟨ ne ⟩) lemma
                    (t /⊢n Renaming.wk⁺ Γ⁺)
          )
  where lemma = ≅-Value-⇒-≡ $ corresponds (app (wk⁺ Γ⁺)) t′
w̌k⁺ {Γ} (π τ′ υ′ , f) Γ⁺ =
  π (τ′ /⊢t wk⁺ Γ⁺) (υ′ /⊢t wk⁺ Γ⁺ ↑) , λ Γ⁺⁺ v →
  let v₀ : V̌alue (Γ ++ Γ⁺ ++ Γ⁺⁺) (τ′ /⊢t wk⁺ Γ⁺ /⊢t wk⁺ Γ⁺⁺)
      v₀ = v

      v′ : V̌alue (Γ ++ (Γ⁺ ++⁺ Γ⁺⁺)) (τ′ /⊢t wk⁺ (Γ⁺ ++⁺ Γ⁺⁺))
      v′ = {!!}

      v″ : V̌alue (Γ ++ (Γ⁺ ++⁺ Γ⁺⁺)) (υ′ /⊢t wk⁺ (Γ⁺ ++⁺ Γ⁺⁺) ↑ ∘ sub ⌊ řeify (τ′ /⊢t wk⁺ (Γ⁺ ++⁺ Γ⁺⁺)) v′ ⌋)
      v″ = f (Γ⁺ ++⁺ Γ⁺⁺) v′

      v‴ : V̌alue (Γ ++ Γ⁺ ++ Γ⁺⁺) (υ′ /⊢t wk⁺ Γ⁺ ↑ /⊢t wk⁺ Γ⁺⁺ ↑ ∘ sub ⌊ řeify (τ′ /⊢t wk⁺ Γ⁺ /⊢t wk⁺ Γ⁺⁺) v ⌋)
      v‴ = {!!}
  in v‴

-- Application.

ǎpp : ∀ {Γ Δ σ τ υ} {ρ̂ : Γ ⇨̂ Δ} →
      ⟨V̌alue⟩ Γ υ → υ ≡ k U.π ˢ σ ˢ τ → (v : ⟨V̌alue⟩ Γ σ) → Sub V̌al ρ̂ →
      ⟨V̌alue⟩ Γ (uc τ /̂ ŝub ⟦̌ v ⟧)
ǎpp (⋆       , f) eq v ρ = {!!}
ǎpp (el t    , f) eq v ρ = {!!}
ǎpp (π σ′ τ′ , f) eq v ρ = {!!}

infixl 9 _·̌_ _·̌[_]_

_·̌[_]_ : ∀ {Γ σ τ υ} →
         ⟨V̌alue⟩ Γ υ → υ ≡ k U.π ˢ σ ˢ τ → (v : ⟨V̌alue⟩ Γ σ) →
         ⟨V̌alue⟩ Γ (uc τ /̂ ŝub ⟦̌ v ⟧)
(⋆       , f) ·̌[ eq ] v = {!!}
(el t    , f) ·̌[ eq ] v = {!!}
(π σ′ τ′ , f) ·̌[ eq ] v = {!!}

_·̌_ : ∀ {Γ σ τ} →
      ⟨V̌alue⟩ Γ (k U.π ˢ σ ˢ τ) → (v : ⟨V̌alue⟩ Γ σ) →
      ⟨V̌alue⟩ Γ (uc τ /̂ ŝub ⟦̌ v ⟧)
f ·̌ v = f ·̌[ P.refl ] v

-- Abstraction.

λ̌ : ∀ {Γ σ τ} →
    Γ ⊢ σ type → ⟨V̌alue⟩ (Γ ▻ σ) τ → ⟨V̌alue⟩ Γ (k U.π ˢ σ ˢ c τ)
λ̌ σ′ v = {!!}

-- Values can be translated into terms.

V̌al⟶⁼Tm : [ V̌al ⟶⁼ Tm ]
V̌al⟶⁼Tm = record
  { function    = λ _ v → ⌊_⌋ {k = no} (uc řeify v)
  ; corresponds = λ _ _ → P.refl
  }

V̌al↦Tm : V̌al ↦ Tm
V̌al↦Tm = record
  { trans  = V̌al⟶⁼Tm
  ; simple = record
    { weaken     = λ {Γ σ} → record
                     { function    = λ τ v → {!v!}
                     ; corresponds = {!!}
                     }
    ; var        = λ {Γ} → record
                     { function    = λ σ x → {!!} , řeflect {!!} (var x)
                     ; corresponds = λ σ x → řeify∘řeflect {!!} (var x)
                     }
    ; weaken-var = {!!}
    }
  }

-- Evaluation.

mutual

  eval : ∀ {Γ Δ σ} {ρ̂ : Γ ⇨̂ Δ} →
         Γ ⊢ σ → Sub V̌al ρ̂ → ⟨V̌alue⟩ Δ (σ /̂ ρ̂)
  eval (var x)  ρ = x /∋ ρ
  eval (ƛ σ′ t) ρ =
    λ̌ (σ′ /⊢t map V̌al⟶⁼Tm ρ) (eval t (_↦_._↑ V̌al↦Tm ρ))
  eval (_·_ {τ = τ} t₁ t₂) ρ =
    P.subst (λ v → ⟨V̌alue⟩ _ (uc τ /̂ ⟦ ρ ⟧⇨ ↑̂ /̂ ŝub v))
            (≅-Value-⇒-≡ $ P.sym $ eval-lemma t₂ ρ)
            (eval t₁ ρ ·̌ eval t₂ ρ)

  abstract

    -- An unfolding lemma.

    eval-· : ∀ {Γ Δ σ τ} {ρ̂ : Γ ⇨̂ Δ}
             (t₁ : Γ ⊢ k U.π ˢ σ ˢ τ) (t₂ : Γ ⊢ σ) (ρ : Sub V̌al ρ̂) →
             eval (t₁ · t₂) ρ ≅-V̌al eval t₁ ρ ·̌ eval t₂ ρ
    eval-· {τ = τ} t₁ t₂ ρ =
      drop-subst-V̌al (λ v → uc τ /̂ ⟦ ρ ⟧⇨ ↑̂ /̂ ŝub v)
                     (≅-Value-⇒-≡ $ P.sym $ eval-lemma t₂ ρ)

    -- The evaluator is well-behaved.

    eval-lemma : ∀ {Γ Δ σ} {ρ̂ : Γ ⇨̂ Δ} (t : Γ ⊢ σ) (ρ : Sub V̌al ρ̂) →
                 ⟦ t ⟧ /Val ρ ≅-Value ⟦̌ eval t ρ ⟧
    eval-lemma (var x)  ρ = _↦_./̂∋-⟦⟧⇨ V̌al↦Tm x ρ
    eval-lemma (ƛ σ′ t) ρ = {!!}
    eval-lemma (_·_ {τ = τ} t₁ t₂) ρ = {!!}

-- -- Application.

-- infixl 9 _·̌_

-- _·̌_ : ∀ {Γ σ τ} {σ′ : Γ ⊢ σ type} {τ′ : Γ ▻ σ ⊢ τ type} →
--       V̌alue Γ (π σ′ τ′) → (v : V̌alue Γ σ′) →
--       V̌alue Γ (τ′ /⊢t sub ⌊ řeify σ′ v ⌋)
-- _·̌_ {σ′ = σ′} {τ′} f v =
--   P.subst (V̌alue _) ({!≅-type-⇒-≡ lemma₂!}) (f ε v′)
--   where
--   abstract
--     lemma₁ : σ′ ≅-type σ′ /⊢t id
--     lemma₁ = {!!}

--   v′ = P.subst (V̌alue _) (≅-type-⇒-≡ lemma₁) v
--   ρ′ = sub ⌊ řeify (σ′ /⊢t id) v′ ⌋

--   abstract
--     lemma₂ : τ′ /⊢t id ↑ ∘ ρ′ ≅-type τ′ /⊢t sub ⌊ řeify σ′ v ⌋
--     lemma₂ = /⊢t-cong (P.refl {x = [ τ′ ]}) (begin
--       [ id ↑ ∘ ρ′          ]  ≡⟨ P.refl ⟩
--       [ id ∘ ρ′            ]  ≡⟨ id-∘ ρ′ ⟩
--       [ ρ′                 ]  ≡⟨ {!!} ⟩
--       [ sub ⌊ řeify σ′ v ⌋ ]  ∎)

-- -- Weakening.

-- w̌k⁺ : ∀ {Γ σ} (σ′ : Γ ⊢ σ type) Γ⁺ →
--       V̌alue Γ σ′ → V̌alue (Γ ++ Γ⁺) (σ′ /⊢t wk⁺ Γ⁺)
-- w̌k⁺ ⋆         Γ⁺ t = t /⊢n Renaming.wk⁺ Γ⁺
-- w̌k⁺ (el t′)   Γ⁺ t = {!t /⊢n Renaming.wk⁺ Γ⁺!}
-- w̌k⁺ (π σ′ τ′) Γ⁺ f = λ Γ⁺⁺ v →
--   {!f (Γ⁺ ++⁺ Γ⁺⁺) v!}

-- abstract

--   -- Properties required of a Kripke model (taken from Mitchell and
--   -- Moggi's "Kripke-style models for typed lambda calculus" and
--   -- adapted to the present setting).

--   -- No weakening amounts to nothing.

--   w̌k⁺-ε : ∀ {Γ σ} (σ′ : Γ ⊢ σ type) (v : V̌alue Γ σ′) →
--           w̌k⁺ σ′ ε v ≅-V̌alue v
--   w̌k⁺-ε σ′ v = ?

--   -- Repeated weakening can be consolidated into one.
--   --
--   -- TODO: State in a pointfree way?

--   w̌k⁺-w̌k⁺ : ∀ {Γ σ} (σ′ : Γ ⊢ σ type) (v : V̌alue Γ σ′) Γ⁺ Γ⁺⁺ →
--             w̌k⁺ (σ′ /⊢t wk⁺ Γ⁺) Γ⁺⁺ (w̌k⁺ σ′ Γ⁺ v) ≅-V̌alue
--             w̌k⁺ σ′ (Γ⁺ ++⁺ Γ⁺⁺) v
--   w̌k⁺-w̌k⁺ σ′ v Γ⁺ Γ⁺⁺ = ?

--   -- Naturality.

--   w̌k⁺-·̌ : ∀ {Γ σ τ} {σ′ : Γ ⊢ σ type} {τ′ : Γ ▻ σ ⊢ τ type} →
--           (f : V̌alue Γ (π σ′ τ′)) (v : V̌alue Γ σ′) Γ⁺ →
--           w̌k⁺ (τ′ /⊢t sub ⌊ řeify σ′ v ⌋) Γ⁺ (f ·̌ v) ≅-V̌alue
--           w̌k⁺ (π σ′ τ′) Γ⁺ f ·̌ w̌k⁺ σ′ Γ⁺ v
--   w̌k⁺-·̌ f v Γ⁺ = ?

--   -- Extensionality.

--   -- Enough elements.
