------------------------------------------------------------------------
-- A Kripke model
------------------------------------------------------------------------

import Level
open import Universe

module README.DependentlyTyped.Kripke-model
  {Uni₀ : Universe Level.zero Level.zero}
  where

open import Data.Product as Prod renaming (curry to c; uncurry to uc)
open import deBruijn.Substitution.Data
import deBruijn.TermLike as TermLike
open import Function renaming (const to k)
open import README.DependentlyTyped.NormalForm
open import README.DependentlyTyped.NormalForm.Substitution
import README.DependentlyTyped.Term as Term; open Term Uni₀
import Relation.Binary.PropositionalEquality as P

open P.≡-Reasoning
open TermLike Uni hiding (·-cong) renaming (_·_ to _⊙_)

-- The family of types which forms a Kripke model.

import README.DependentlyTyped.Kripke-model.Definition as Definition
open Definition {Uni₀} public

-- The semantics of a value.

⟦̌_⟧ : ∀ {Γ σ} → V̌alue Γ σ → Value Γ σ
⟦̌ v ⟧ = ⟦ řeify _ v ⟧n

-- Values are term-like.

V̌al : Term-like _
V̌al = record
  { _⊢_ = V̌alue
  ; ⟦_⟧ = ⟦̌_⟧
  }

open Term-like V̌al public
  using ([_])
  renaming ( _≅-⊢_ to _≅-V̌alue_
           ; drop-subst-⊢ to drop-subst-V̌alue; ⟦⟧-cong to ⟦̌⟧-cong
           )

-- Some congruence lemmas.

ňeutral-to-normal-cong :
  ∀ {Γ₁ σ₁} {t₁ : Γ₁ ⊢ σ₁ ⟨ ne ⟩}
    {Γ₂ σ₂} {t₂ : Γ₂ ⊢ σ₂ ⟨ ne ⟩} →
  t₁ ≅-⊢n t₂ → ňeutral-to-normal _ t₁ ≅-⊢n ňeutral-to-normal _ t₂
ňeutral-to-normal-cong P.refl = P.refl

žero-cong : ∀ {Γ₁} {σ₁ : Type Γ₁}
              {Γ₂} {σ₂ : Type Γ₂} →
            σ₁ ≅-Type σ₂ → žero _ (proj₂ σ₁) ≅-⊢n žero _ (proj₂ σ₂)
žero-cong P.refl = P.refl

řeify-cong : ∀ {Γ₁ σ₁} {v₁ : V̌alue Γ₁ σ₁}
               {Γ₂ σ₂} {v₂ : V̌alue Γ₂ σ₂} →
             v₁ ≅-V̌alue v₂ → řeify _ v₁ ≅-⊢n řeify _ v₂
řeify-cong P.refl = P.refl

řeflect-cong : ∀ {Γ₁ σ₁} {t₁ : Γ₁ ⊢ σ₁ ⟨ ne ⟩}
                 {Γ₂ σ₂} {t₂ : Γ₂ ⊢ σ₂ ⟨ ne ⟩} →
               t₁ ≅-⊢n t₂ → řeflect _ t₁ ≅-V̌alue řeflect _ t₂
řeflect-cong P.refl = P.refl

-- TODO: Add more congruence lemmas below.

-- Application.

infixl 9 _·̌_

_·̌_ : ∀ {Γ σ τ} →
      V̌alue Γ (, k U-π ˢ indexed-type σ ˢ proj₂ τ) → (v : V̌alue Γ σ) →
      V̌alue Γ (Prod.map id uc τ /̂ ŝub {σ = σ} ⟦̌ v ⟧)
f ·̌ v = f ε v

-- Variables can be turned into values.

v̌ar : [ Var ⟶⁼ V̌al ]
v̌ar = record
  { function    = λ σ x → řeflect _ (var x)
  ; corresponds = λ σ x → P.sym $ ňeutral-to-normal-identity _ (var x)
  }

-- Weakening.

postulate
  w̌k : ∀ {Γ σ} τ → V̌alue Γ τ → V̌alue (Γ ▻ σ) (τ /̂ ŵk)

-- w̌k⁺ : ∀ {Γ} σ → V̌alue Γ σ → ∀ Γ⁺ → V̌alue (Γ ++ Γ⁺) (σ /̂ ŵk⁺ Γ⁺)
-- w̌k⁺     (⋆         , σ) t     Γ⁺ =   t /⊢n Renaming.wk⁺ Γ⁺
-- w̌k⁺     (el        , σ) [ t ] Γ⁺ = [ t /⊢n Renaming.wk⁺ Γ⁺ ]
-- w̌k⁺ {Γ} (π sp₁ sp₂ , σ) f     Γ⁺ = λ Γ⁺⁺ v →
--   let cast₁ : V̌alue (Γ ++ Γ⁺ ++ Γ⁺⁺) (sp₁ , ifst (σ /̂I ŵk⁺ Γ⁺) /̂I ŵk⁺ Γ⁺⁺) →
--               V̌alue (Γ ++ (Γ⁺ ++⁺ Γ⁺⁺)) (sp₁ , ifst σ /̂I ŵk⁺ (Γ⁺ ++⁺ Γ⁺⁺))
--       cast₁ = {!!}

--       cast₂ : V̌alue (Γ ++ (Γ⁺ ++⁺ Γ⁺⁺)) (sp₂ , isnd σ /̂I ŵk⁺ (Γ⁺ ++⁺ Γ⁺⁺) ↑̂ ∘̂ ŝub ⟦̌ cast₁ v ⟧n) →
--               V̌alue (Γ ++ Γ⁺ ++ Γ⁺⁺) (sp₂ , isnd (σ /̂I ŵk⁺ Γ⁺) /̂I ŵk⁺ Γ⁺⁺ ↑̂ ∘̂ ŝub ⟦̌ v ⟧n)
--       cast₂ = {!!}
--   in cast₂ $ f (Γ⁺ ++⁺ Γ⁺⁺) $ cast₁ v

-- w̌k : ∀ {Γ σ} τ → V̌alue Γ τ → V̌alue (Γ ▻ σ) (τ /̂ ŵk)
-- w̌k         (⋆         , τ) t     =   t /⊢n Renaming.wk
-- w̌k         (el        , τ) [ t ] = [ t /⊢n Renaming.wk ]
-- w̌k {Γ} {σ} (π sp₁ sp₂ , τ) f     = λ Γ⁺ v →
--   let cast₁ : V̌alue (Γ ▻ σ ++ Γ⁺) (sp₁ , ifst (τ /̂I ŵk) /̂I ŵk⁺ Γ⁺) →
--               V̌alue (Γ ++ (ε ▻ σ ++⁺ Γ⁺)) (sp₁ , ifst τ /̂I ŵk⁺ (ε ▻ σ ++⁺ Γ⁺))
--       cast₁ = {!!}

--       cast₂ : V̌alue (Γ ++ (ε ▻ σ ++⁺ Γ⁺)) (sp₂ , isnd τ /̂I ŵk⁺ (ε ▻ σ ++⁺ Γ⁺) ↑̂ ∘̂ ŝub ⟦̌ cast₁ v ⟧n) →
--               V̌alue (Γ ▻ σ ++ Γ⁺) (sp₂ , isnd (τ /̂I ŵk) /̂I ŵk⁺ Γ⁺ ↑̂ ∘̂ ŝub ⟦̌ v ⟧n)
--       cast₂ = {!!}
--   in cast₂ $ f (ε ▻ σ ++⁺ Γ⁺) $ cast₁ v

w̌k[_] : ∀ {Γ} σ τ → V̌alue Γ τ → V̌alue (Γ ▻ σ) (τ /̂ ŵk)
w̌k[ σ ] τ v = w̌k {σ = σ} τ v

w̌eaken : ∀ {Γ} {σ : Type Γ} → [ V̌al ⟶ V̌al ] ŵk[ σ ]
w̌eaken = record
  { function    = w̌k
  ; corresponds = corr
  }
  where
  abstract
   postulate
    corr : ∀ {Γ σ} τ (v : V̌alue Γ τ) →
           ⟦̌ v ⟧ /̂Val ŵk[ σ ] ≅-Value ⟦̌ w̌k[ σ ] τ v ⟧
    -- corr = {!!}

-- Values can be translated into terms.

V̌al⟶⁼Tm : [ V̌al ⟶⁼ Tm ]
V̌al⟶⁼Tm = record
  { function    = λ _ v → ⌊ řeify _ v ⌋
  ; corresponds = λ _ _ → P.refl
  }

V̌al↦Tm : V̌al ↦ Tm
V̌al↦Tm = record
  { trans  = V̌al⟶⁼Tm
  ; simple = record
    { weaken     = w̌eaken
    ; var        = v̌ar
    ; weaken-var = w̌eaken-v̌ar
    }
  }
  where
  abstract
   postulate
    w̌eaken-v̌ar : ∀ {Γ σ τ} (x : Γ ∋ τ) →
                 w̌k[ σ ] τ (v̌ar ⊙ x) ≅-V̌alue v̌ar ⊙ suc[ σ ] x
    -- w̌eaken-v̌ar x = {!!}

module V̌al-subst = _↦_ V̌al↦Tm

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
  eval (ƛ t)               ρ = λ Γ⁺ v →
                               eval t (V̌al-subst.wk-subst⁺ Γ⁺ ρ ▻ v)
  eval (_·_ {τ = τ} t₁ t₂) ρ = cast (eval t₁ ρ ε (eval t₂ ρ))
    -- (_·̌_ {τ = Prod.map id c (Prod.map id uc τ /̂ ⟦ ρ ⟧⇨ ↑̂)}
    --      (eval t₁ ρ) (eval t₂ ρ))
    where
    cast = P.subst (λ v → V̌alue _ (Prod.map id uc τ /̂ ⟦ ρ ⟧⇨ ↑̂ /̂ ŝub v))
                   (≅-Value-⇒-≡ $ P.sym $ eval-lemma t₂ ρ)

  abstract

    -- An unfolding lemma.

    eval-· : ∀ {Γ Δ σ} {ρ̂ : Γ ⇨̂ Δ}
               {τ : ∃ λ sp → (γ : Env Γ) → El (indexed-type σ γ) → U sp}
             (t₁ : Γ ⊢ π (proj₁ σ) (proj₁ τ) ,
                       k U-π ˢ indexed-type σ ˢ proj₂ τ)
             (t₂ : Γ ⊢ σ) (ρ : Sub V̌al ρ̂) →
             eval (t₁ · t₂) ρ ≅-V̌alue eval t₁ ρ ε (eval t₂ ρ)
    eval-· {τ = τ} t₁ t₂ ρ =
      drop-subst-V̌alue (λ v → Prod.map id uc τ /̂ ⟦ ρ ⟧⇨ ↑̂ /̂ ŝub v)
                       (≅-Value-⇒-≡ $ P.sym $ eval-lemma t₂ ρ)

  -- The evaluator is well-behaved.

  eval-lemma : ∀ {Γ Δ σ} {ρ̂ : Γ ⇨̂ Δ} (t : Γ ⊢ σ) (ρ : Sub V̌al ρ̂) →
               ⟦ t ⟧ /Val ρ ≅-Value ⟦̌ eval t ρ ⟧
  eval-lemma (var x)               ρ = V̌al-subst./̂∋-⟦⟧⇨ x ρ

  eval-lemma (ƛ {σ = σ} {τ = τ} t) ρ =
    let ρ↑ = V̌al-subst.wk-subst⁺ (ε ▻ σ / ρ) ρ ▻ v̌ar ⊙ zero

    in begin
    [ c (⟦ t ⟧ /̂Val ⟦ ρ ⟧⇨ ↑̂)      ]  ≡⟨ curry-cong (/̂Val-cong (P.refl {x = [ ⟦ t ⟧ ]}) (P.sym $ ∘̂-ŵk-▻̂-žero ⟦ ρ ⟧⇨ _)) ⟩
    [ c (⟦ t ⟧ /Val ρ↑)            ]  ≡⟨ curry-cong (eval-lemma t ρ↑) ⟩
    [ c ⟦̌ eval t ρ↑ ⟧              ]  ≡⟨ P.refl ⟩
    [ ⟦ ƛ (řeify _ (eval t ρ↑)) ⟧n ]  ≡⟨ ⟦⟧n-cong $ P.sym $ drop-subst-⊢n (λ υ → _ , υ)
                                                                          (ifst-isnd-ŵk-ŝub-žero (proj₁ σ) {sp₂ = proj₁ τ} _) ⟩
    [ ⟦̌ eval (ƛ t) ρ ⟧             ]  ∎

  eval-lemma (_·_ {σ = σ} {τ = τ} t₁ t₂) ρ =
    let υ = (k U-π ˢ proj₂ σ ˢ proj₂ τ) /̂I ⟦ ρ ⟧⇨

    in begin
    [ ⟦ t₁ · t₂ ⟧ /Val ρ                                       ]  ≡⟨ P.refl ⟩
    [ (⟦ t₁ ⟧ /Val ρ) ˢ (⟦ t₂ ⟧ /Val ρ)                        ]  ≡⟨ ˢ-cong (P.refl {x = [ Prod.map id uc τ /̂ ⟦ ρ ⟧⇨ ↑̂ ]})
                                                                            (eval-lemma t₁ ρ) (eval-lemma t₂ ρ) ⟩
    [ ⟦̌_⟧ {σ = , υ} (eval t₁ ρ) ˢ ⟦̌ eval t₂ ρ ⟧                ]  ≡⟨ ˢ-cong
                                                                       (/̂-cong (P.refl {x = [ Prod.map id uc τ ]})
                                                                               (P.sym $ ∘̂-ŵk-▻̂-žero ⟦ ρ ⟧⇨ _))
                                                                       (⟦⟧n-cong $
                                                                          drop-subst-⊢n (λ σ → , σ)
                                                                            (ifst-isnd-ŵk-ŝub-žero (proj₁ σ) {sp₂ = proj₁ τ} _))
                                                                       (P.refl {x = [ ⟦̌ eval t₂ ρ ⟧ ]}) ⟩
    [ c ⟦̌ eval t₁ ρ (ε ▻ fst υ) (v̌ar ⊙ zero) ⟧ ˢ ⟦̌ eval t₂ ρ ⟧ ]  ≡⟨ {!!} ⟩
    [ ⟦̌ eval t₁ ρ ε (eval t₂ ρ) ⟧                              ]  ≡⟨ ⟦̌⟧-cong (P.sym $ eval-· t₁ t₂ ρ) ⟩
    [ ⟦̌ eval (t₁ · t₂) ρ ⟧                                     ]  ∎

-- Goal: (λ γ → ⟦ řeify (proj₁ τ) (eval t₁ ρ (ε ▻ fst υ) (řeflect (proj₁ σ) (var zero))) ⟧n (γ , ⟦ řeify (proj₁ σ) (eval t₂ ρ) ⟧n γ))
--         ≅-Value
--       ⟦ řeify (proj₁ τ) (eval t₁ ρ ε (eval t₂ ρ)) ⟧n

-- -- Normalisation.

-- normalise : ∀ {Γ σ} → Γ ⊢ σ → Γ ⊢ σ ⟨ no ⟩
-- normalise t = řeify _ (eval t V̌al-subst.id)

-- -- Normalisation is semantics-preserving.

-- normalise-lemma : ∀ {Γ σ} (t : Γ ⊢ σ) → ⟦ t ⟧ ≅-Value ⟦ normalise t ⟧n
-- normalise-lemma t = eval-lemma t V̌al-subst.id

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
