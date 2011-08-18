------------------------------------------------------------------------
-- Some simple substitution combinators
------------------------------------------------------------------------

-- Given a term type which supports weakening and transformation of
-- variables to terms various substitutions are defined and various
-- lemmas proved.

{-# OPTIONS --universe-polymorphism #-}

open import Universe

module deBruijn.Substitution.Function.Simple
  {i u e} {Uni : Indexed-universe i u e} where

import deBruijn.Context as Context
open import deBruijn.Substitution.Function.Basics
open import deBruijn.Substitution.Function.Map
import deBruijn.TermLike as TermLike
open import Function as F using (_$_)
open import Level using (_⊔_)
import Relation.Binary.PropositionalEquality as P

open Context Uni
open P.≡-Reasoning
open TermLike Uni

-- Simple substitutions.

record Simple {t} (T : Term-like t) : Set (u ⊔ e ⊔ t) where

  open Term-like T

  field

    -- Weakens terms.
    weaken : ∀ {Γ} {σ : Type Γ} → [ T ⟶ T ] ŵk[ σ ]

  -- A synonym.

  weaken[_] : ∀ {Γ} (σ : Type Γ) → [ T ⟶ T ] ŵk[ σ ]
  weaken[_] _ = weaken

  field

    -- Takes variables to terms.
    var : [ Var ⟶⁼ T ]

    -- A property relating weaken and var.
    weaken-var : ∀ {Γ σ τ} (x : Γ ∋ τ) →
                 weaken[ σ ] · (var · x) ≅-⊢ var · suc[ σ ] x

  -- Weakens substitutions.

  wk-subst : ∀ {Γ Δ σ} {ρ̂ : Γ ⇨̂ Δ} → Sub T ρ̂ → Sub T (ρ̂ ∘̂ ŵk[ σ ])
  wk-subst ρ = map weaken ρ

  wk-subst[_] : ∀ {Γ Δ} σ {ρ̂ : Γ ⇨̂ Δ} → Sub T ρ̂ → Sub T (ρ̂ ∘̂ ŵk[ σ ])
  wk-subst[ _ ] = wk-subst

  -- Lifting.

  infixl 10 _↑_
  infix  10 _↑

  _↑_ : ∀ {Γ Δ} {ρ̂ : Γ ⇨̂ Δ} → Sub T ρ̂ → ∀ σ → Sub T (ρ̂ ↑̂ σ)
  ρ ↑ _ =
    P.subst (Sub T)
            (≅-⇨̂-⇒-≡ $ ▻̂-cong P.refl P.refl
                         (P.sym $ corresponds var zero))
            (wk-subst ρ ▻⇨ var · zero)

  _↑ : ∀ {Γ Δ σ} {ρ̂ : Γ ⇨̂ Δ} → Sub T ρ̂ → Sub T (ρ̂ ↑̂ σ)
  ρ ↑ = ρ ↑ _

  -- N-ary lifting.

  infixl 10 _↑⁺_

  _↑⁺_ : ∀ {Γ Δ} {ρ̂ : Γ ⇨̂ Δ} → Sub T ρ̂ → ∀ Γ⁺ → Sub T (ρ̂ ↑̂⁺ Γ⁺)
  ρ ↑⁺ ε        = ρ
  ρ ↑⁺ (Γ⁺ ▻ σ) = (ρ ↑⁺ Γ⁺) ↑

  -- The identity substitution.

  id[_] : ∀ Γ → Sub T îd[ Γ ]
  id[ ε     ] = ε⇨
  id[ Γ ▻ σ ] = id[ Γ ] ↑

  id : ∀ {Γ} → Sub T îd[ Γ ]
  id = id[ _ ]

  -- N-ary weakening.

  wk⁺ : ∀ {Γ} (Γ⁺ : Ctxt⁺ Γ) → Sub T (ŵk⁺ Γ⁺)
  wk⁺ ε        = id
  wk⁺ (Γ⁺ ▻ σ) = wk-subst (wk⁺ Γ⁺)

  -- Weakening.

  wk[_] : ∀ {Γ} (σ : Type Γ) → Sub T ŵk[ σ ]
  wk[ σ ] = wk⁺ (ε ▻ σ)

  wk : ∀ {Γ} {σ : Type Γ} → Sub T ŵk[ σ ]
  wk = wk[ _ ]

  -- A substitution which only replaces the first variable.

  sub : ∀ {Γ σ} (t : Γ ⊢ σ) → Sub T (ŝub ⟦ t ⟧)
  sub t = id ▻⇨ t

  abstract

    -- Unfolding lemma for _↑.

    unfold-↑ : ∀ {Γ Δ σ} {ρ̂ : Γ ⇨̂ Δ} (ρ : Sub T ρ̂) →
               ρ ↑ σ ≅-⇨ wk-subst[ σ / ρ ] ρ ▻⇨[ σ ] var · zero
    unfold-↑ _ =
      drop-subst-Sub F.id
        (≅-⇨̂-⇒-≡ $ ▻̂-cong P.refl P.refl (P.sym $ corresponds var zero))

  -- Some congruence lemmas.

  weaken-cong : ∀ {Γ₁ σ₁ τ₁} {t₁ : Γ₁ ⊢ τ₁}
                  {Γ₂ σ₂ τ₂} {t₂ : Γ₂ ⊢ τ₂} →
                σ₁ ≅-Type σ₂ → t₁ ≅-⊢ t₂ →
                weaken[ σ₁ ] · t₁ ≅-⊢ weaken[ σ₂ ] · t₂
  weaken-cong P.refl P.refl = P.refl

  var-cong : ∀ {Γ₁ σ₁} {x₁ : Γ₁ ∋ σ₁}
               {Γ₂ σ₂} {x₂ : Γ₂ ∋ σ₂} →
               x₁ ≅-∋ x₂ → var · x₁ ≅-⊢ var · x₂
  var-cong P.refl = P.refl

  wk-subst-cong : ∀ {Γ₁ Δ₁ σ₁} {ρ̂₁ : Γ₁ ⇨̂ Δ₁} {ρ₁ : Sub T ρ̂₁}
                    {Γ₂ Δ₂ σ₂} {ρ̂₂ : Γ₂ ⇨̂ Δ₂} {ρ₂ : Sub T ρ̂₂} →
                  σ₁ ≅-Type σ₂ → ρ₁ ≅-⇨ ρ₂ →
                  wk-subst[ σ₁ ] ρ₁ ≅-⇨ wk-subst[ σ₂ ] ρ₂
  wk-subst-cong {ρ₁ = _ , _} {ρ₂ = ._ , _} P.refl [ P.refl ] =
    [ P.refl ]

  abstract

    ↑-cong : ∀ {Γ₁ Δ₁} {ρ̂₁ : Γ₁ ⇨̂ Δ₁} {ρ₁ : Sub T ρ̂₁} {σ₁}
               {Γ₂ Δ₂} {ρ̂₂ : Γ₂ ⇨̂ Δ₂} {ρ₂ : Sub T ρ̂₂} {σ₂} →
             ρ₁ ≅-⇨ ρ₂ → σ₁ ≅-Type σ₂ → ρ₁ ↑ σ₁ ≅-⇨ ρ₂ ↑ σ₂
    ↑-cong {ρ₁ = ρ₁} {σ₁} {ρ₂ = ρ₂} {σ₂} ρ₁≅ρ₂ σ₁≅σ₂ =
      let lemma = /-cong σ₁≅σ₂ ρ₁≅ρ₂ in
      ρ₁ ↑ σ₁                               ≅-⟶⟨ unfold-↑ ρ₁ ⟩
      wk-subst ρ₁ ▻⇨ var · zero[ σ₁ / ρ₁ ]  ≅-⟶⟨ ▻⇨-cong σ₁≅σ₂ (wk-subst-cong lemma ρ₁≅ρ₂) (var-cong (zero-cong lemma)) ⟩
      wk-subst ρ₂ ▻⇨ var · zero[ σ₂ / ρ₂ ]  ≅-⟶⟨ sym-⟶ $ unfold-↑ ρ₂ ⟩
      ρ₂ ↑ σ₂                               ∎-⟶

    ↑⁺-cong : ∀ {Γ₁ Δ₁} {ρ̂₁ : Γ₁ ⇨̂ Δ₁} {ρ₁ : Sub T ρ̂₁} {Γ⁺₁}
                {Γ₂ Δ₂} {ρ̂₂ : Γ₂ ⇨̂ Δ₂} {ρ₂ : Sub T ρ̂₂} {Γ⁺₂} →
              ρ₁ ≅-⇨ ρ₂ → Γ⁺₁ ≅-Ctxt⁺ Γ⁺₂ → ρ₁ ↑⁺ Γ⁺₁ ≅-⇨ ρ₂ ↑⁺ Γ⁺₂
    ↑⁺-cong {ρ₁ = _ , _} {Γ⁺₁ = ε} {ρ₂ = ._ , _} [ P.refl ] P.refl =
      [ P.refl ]
    ↑⁺-cong {Γ⁺₁ = Γ⁺ ▻ σ} ρ₁≅ρ₂ P.refl =
      ↑-cong (↑⁺-cong ρ₁≅ρ₂ (P.refl {x = [ Γ⁺ ]})) P.refl

  id-cong : ∀ {Γ₁ Γ₂} → Γ₁ ≅-Ctxt Γ₂ → id[ Γ₁ ] ≅-⇨ id[ Γ₂ ]
  id-cong P.refl = [ P.refl ]

  wk⁺-cong : ∀ {Γ₁} {Γ⁺₁ : Ctxt⁺ Γ₁} {Γ₂} {Γ⁺₂ : Ctxt⁺ Γ₂} →
             Γ⁺₁ ≅-Ctxt⁺ Γ⁺₂ → wk⁺ Γ⁺₁ ≅-⇨ wk⁺ Γ⁺₂
  wk⁺-cong P.refl = [ P.refl ]

  wk-cong : ∀ {Γ₁} {σ₁ : Type Γ₁} {Γ₂} {σ₂ : Type Γ₂} →
            σ₁ ≅-Type σ₂ → wk[ σ₁ ] ≅-⇨ wk[ σ₂ ]
  wk-cong P.refl = [ P.refl ]

  sub-cong : ∀ {Γ₁ σ₁} {t₁ : Γ₁ ⊢ σ₁} {Γ₂ σ₂} {t₂ : Γ₂ ⊢ σ₂} →
             t₁ ≅-⊢ t₂ → sub t₁ ≅-⇨ sub t₂
  sub-cong P.refl = [ P.refl ]

  abstract

    -- Some lemmas relating variables to lifting.

    /∋-↑ : ∀ {Γ Δ σ τ} {ρ̂ : Γ ⇨̂ Δ} (x : Γ ▻ σ ∋ τ) (ρ : Sub T ρ̂) →
           x /∋ ρ ↑ ≅-⊢ x /∋ (wk-subst[ σ / ρ ] ρ ▻⇨ var · zero)
    /∋-↑ x ρ = /∋-cong (P.refl {x = [ x ]}) (unfold-↑ ρ)

    zero-/∋-↑ : ∀ {Γ Δ} σ {ρ̂ : Γ ⇨̂ Δ} (ρ : Sub T ρ̂) →
                zero[ σ ] /∋ ρ ↑ ≅-⊢ var · zero[ σ / ρ ]
    zero-/∋-↑ σ ρ = begin
      [ zero[ σ ] /∋ ρ ↑                        ]  ≡⟨ /∋-↑ zero[ σ ] ρ ⟩
      [ zero[ σ ] /∋ (wk-subst ρ ▻⇨ var · zero) ]  ≡⟨ P.refl ⟩
      [ var · zero                              ]  ∎

    suc-/∋-↑ : ∀ {Γ Δ τ} σ {ρ̂ : Γ ⇨̂ Δ} (x : Γ ∋ τ) (ρ : Sub T ρ̂) →
               suc[ σ ] x /∋ ρ ↑ ≅-⊢ x /∋ wk-subst[ σ / ρ ] ρ
    suc-/∋-↑ σ x ρ = begin
      [ suc[ σ ] x /∋ ρ ↑                        ]  ≡⟨ /∋-↑ (suc[ σ ] x) ρ ⟩
      [ suc[ σ ] x /∋ (wk-subst ρ ▻⇨ var · zero) ]  ≡⟨ P.refl ⟩
      [ x /∋ wk-subst ρ                          ]  ∎

  -- One can weaken either before or after looking up a variable.
  -- (Note that this lemma holds definitionally, unlike the
  -- corresponding lemma in deBruijn.Substitution.Data.Simple.)

  /∋-wk-subst : ∀ {Γ Δ σ τ} {ρ̂ : Γ ⇨̂ Δ} (x : Γ ∋ τ) (ρ : Sub T ρ̂) →
                x /∋ wk-subst[ σ ] ρ ≅-⊢ weaken[ σ ] · (x /∋ ρ)
  /∋-wk-subst x ρ = P.refl

  abstract

    -- A corollary.

    /∋-wk-subst-var :
      ∀ {Γ Δ σ τ} {ρ̂ : Γ ⇨̂ Δ}
      (ρ : Sub T ρ̂) (x : Γ ∋ τ) (y : Δ ∋ τ / ρ) →
      x /∋               ρ ≅-⊢ var ·          y →
      x /∋ wk-subst[ σ ] ρ ≅-⊢ var · suc[ σ ] y
    /∋-wk-subst-var ρ x y hyp = begin
      [ x /∋ wk-subst ρ    ]  ≡⟨ P.refl ⟩
      [ weaken · (x /∋ ρ)  ]  ≡⟨ weaken-cong P.refl hyp ⟩
      [ weaken · (var · y) ]  ≡⟨ weaken-var y ⟩
      [ var · suc y        ]  ∎

    -- The identity substitution has no effect.

    /-id : ∀ {Γ} (σ : Type Γ) → σ / id ≅-Type σ
    /-id σ = P.refl

    /⁺-id : ∀ {Γ} (Γ⁺ : Ctxt⁺ Γ) → Γ⁺ /⁺ id ≅-Ctxt⁺ Γ⁺
    /⁺-id Γ⁺ = begin
      [ Γ⁺ /⁺ id ]  ≡⟨ P.refl ⟩
      [ Γ⁺ /̂⁺ îd ]  ≡⟨ /̂⁺-îd Γ⁺ ⟩
      [ Γ⁺       ]  ∎

    mutual

      /∋-id : ∀ {Γ σ} (x : Γ ∋ σ) → x /∋ id ≅-⊢ var · x
      /∋-id {Γ = ε}     ()
      /∋-id {Γ = Γ ▻ σ} x = begin
        [ x /∋ id ↑               ]  ≡⟨ /∋-↑ x id ⟩
        [ x /∋ (wk ▻⇨ var · zero) ]  ≡⟨ lemma x ⟩
        [ var · x                 ]  ∎
        where
        lemma : ∀ {τ} (x : Γ ▻ σ ∋ τ) →
                x /∋ (wk[ σ ] ▻⇨ var · zero) ≅-⊢ var · x
        lemma zero    = P.refl
        lemma (suc x) = /∋-wk x

      -- Weakening a variable is equivalent to incrementing it.

      /∋-wk : ∀ {Γ σ τ} (x : Γ ∋ τ) →
              x /∋ wk[ σ ] ≅-⊢ var · suc[ σ ] x
      /∋-wk x = /∋-wk-subst-var id x x (/∋-id x)

    -- The n-ary lifting of the identity substitution is the identity
    -- substitution.

    id-↑⁺ : ∀ {Γ} (Γ⁺ : Ctxt⁺ Γ) → id ↑⁺ Γ⁺ ≅-⇨ id[ Γ ++ Γ⁺ ]
    id-↑⁺ ε        = id ∎-⟶
    id-↑⁺ (Γ⁺ ▻ σ) =
      (id ↑⁺ Γ⁺) ↑  ≅-⟶⟨ ↑-cong (id-↑⁺ Γ⁺) P.refl ⟩
      id ↑          ∎-⟶

    -- The identity substitution has no effect even if lifted.

    /∋-id-↑⁺ : ∀ {Γ} Γ⁺ {σ} (x : Γ ++ Γ⁺ ∋ σ) →
               x /∋ id ↑⁺ Γ⁺ ≅-⊢ var · x
    /∋-id-↑⁺ Γ⁺ x = begin
      [ x /∋ id ↑⁺ Γ⁺ ]  ≡⟨ /∋-cong (P.refl {x = [ x ]}) (id-↑⁺ Γ⁺) ⟩
      [ x /∋ id       ]  ≡⟨ /∋-id x ⟩
      [ var · x       ]  ∎

    -- If ρ is morally a renaming, then "deep application" of ρ to a
    -- variable is still a variable.

    /∋-↑⁺ : ∀ {Γ Δ} {ρ̂ : Γ ⇨̂ Δ}
            (ρ : Sub T ρ̂) (f : [ Var ⟶ Var ] ρ̂) →
            (∀ {σ} (x : Γ ∋ σ) → x /∋ ρ ≅-⊢ var · (f · x)) →
            ∀ Γ⁺ {σ} (x : Γ ++ Γ⁺ ∋ σ) →
            x /∋ ρ ↑⁺ Γ⁺ ≅-⊢ var · (lift f Γ⁺ · x)
    /∋-↑⁺ ρ f hyp ε        x    = hyp x
    /∋-↑⁺ ρ f hyp (Γ⁺ ▻ σ) zero = begin
      [ zero[ σ ] /∋ (ρ ↑⁺ Γ⁺) ↑ ]  ≡⟨ zero-/∋-↑ σ (ρ ↑⁺ Γ⁺) ⟩
      [ var · zero               ]  ∎
    /∋-↑⁺ ρ f hyp (Γ⁺ ▻ σ) (suc x) = begin
      [ suc[ σ ] x /∋ (ρ ↑⁺ Γ⁺) ↑        ]  ≡⟨ suc-/∋-↑ σ x (ρ ↑⁺ Γ⁺) ⟩
      [ x /∋ wk-subst (ρ ↑⁺ Γ⁺)          ]  ≡⟨ P.refl ⟩
      [ weaken · (x /∋ ρ ↑⁺ Γ⁺)          ]  ≡⟨ weaken-cong P.refl (/∋-↑⁺ ρ f hyp Γ⁺ x) ⟩
      [ weaken · (var · (lift f Γ⁺ · x)) ]  ≡⟨ weaken-var (lift f Γ⁺ · x) ⟩
      [ var · suc (lift f Γ⁺ · x)        ]  ∎

    -- "Deep weakening" of a variable can be expressed without
    -- reference to the weaken function.

    /∋-wk-↑⁺ : ∀ {Γ σ} Γ⁺ {τ} (x : Γ ++ Γ⁺ ∋ τ) →
               x /∋ wk[ σ ] ↑⁺ Γ⁺ ≅-⊢
               var · (lift weaken∋[ σ ] Γ⁺ · x)
    /∋-wk-↑⁺ = /∋-↑⁺ wk weaken∋ /∋-wk

    /∋-wk-↑⁺-↑⁺ : ∀ {Γ σ} Γ⁺ Γ⁺⁺ {τ} (x : Γ ++ Γ⁺ ++ Γ⁺⁺ ∋ τ) →
                  x /∋ wk[ σ ] ↑⁺ Γ⁺ ↑⁺ Γ⁺⁺ ≅-⊢
                  var · (lift (lift weaken∋[ σ ] Γ⁺) Γ⁺⁺ · x)
    /∋-wk-↑⁺-↑⁺ Γ⁺ = /∋-↑⁺ (wk ↑⁺ Γ⁺) (lift weaken∋ Γ⁺) (/∋-wk-↑⁺ Γ⁺)

    -- Two n-ary liftings can be merged into one.

    ↑⁺-++⁺ : ∀ {Γ Δ} {ρ̂ : Γ ⇨̂ Δ} (ρ : Sub T ρ̂) Γ⁺ Γ⁺⁺ →
             ρ ↑⁺ (Γ⁺ ++⁺ Γ⁺⁺) ≅-⇨ ρ ↑⁺ Γ⁺ ↑⁺ Γ⁺⁺
    ↑⁺-++⁺ ρ Γ⁺ ε         = ρ ↑⁺ Γ⁺ ∎-⟶
    ↑⁺-++⁺ ρ Γ⁺ (Γ⁺⁺ ▻ σ) =
      (ρ ↑⁺ (Γ⁺ ++⁺ Γ⁺⁺)) ↑  ≅-⟶⟨ ↑-cong (↑⁺-++⁺ ρ Γ⁺ Γ⁺⁺)
                                         (drop-subst-Type F.id (++-++ Γ⁺ Γ⁺⁺)) ⟩
      (ρ ↑⁺ Γ⁺ ↑⁺ Γ⁺⁺) ↑     ∎-⟶
