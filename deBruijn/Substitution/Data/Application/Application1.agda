------------------------------------------------------------------------
-- Operations and lemmas related to application of substitutions
------------------------------------------------------------------------

open import Data.Universe.Indexed

module deBruijn.Substitution.Data.Application.Application1
  {i u e} {Uni : IndexedUniverse i u e} where

import deBruijn.Context; open deBruijn.Context Uni
open import deBruijn.Substitution.Data.Application.Application22
open import deBruijn.Substitution.Data.Basics
open import deBruijn.Substitution.Data.Map
open import deBruijn.Substitution.Data.Simple
open import Function using (_$_)
open import Level using (_⊔_)
open import Relation.Binary.PropositionalEquality as P using (_≡_)

open P.≡-Reasoning

-- More operations and lemmas related to application. In this module
-- the application operator is assumed to be homogeneous, so some
-- previously proved lemmas can be stated in a less complicated way.

record Application₁ {t} (T : Term-like t) : Set (i ⊔ u ⊔ e ⊔ t) where

  open Term-like T

  field
    -- Simple substitutions.
    simple : Simple T

    -- The homogeneous variant is defined in terms of the
    -- heterogeneous one.
    application₂₂ : Application₂₂ simple simple ([id] {T = T})

  open Simple simple public
  open Application₂₂ application₂₂ public
    hiding ( ∘⋆; ∘⋆-cong; /∋-∘⋆
           ; trans-cong; id-∘; map-trans-wk-subst; map-trans-↑; wk-∘-↑
           )

  -- Composition of multiple substitutions.
  --
  -- Note that singleton sequences are handled specially, to avoid the
  -- introduction of unnecessary identity substitutions.

  ∘⋆ : ∀ {Γ Δ} {ρ̂ : Γ ⇨̂ Δ} → Subs T ρ̂ → Sub T ρ̂
  ∘⋆ ε        = id
  ∘⋆ (ε  ▻ ρ) = ρ
  ∘⋆ (ρs ▻ ρ) = ∘⋆ ρs ∘ ρ

  -- A congruence lemma.

  ∘⋆-cong : ∀ {Γ₁ Δ₁} {ρ̂₁ : Γ₁ ⇨̂ Δ₁} {ρs₁ : Subs T ρ̂₁}
              {Γ₂ Δ₂} {ρ̂₂ : Γ₂ ⇨̂ Δ₂} {ρs₂ : Subs T ρ̂₂} →
            ρs₁ ≅-⇨⋆ ρs₂ → ∘⋆ ρs₁ ≅-⇨ ∘⋆ ρs₂
  ∘⋆-cong P.refl = P.refl

  abstract

    -- Applying a composed substitution to a variable is equivalent to
    -- applying all the substitutions one after another.

    /∋-∘⋆ : ∀ {Γ Δ σ} {ρ̂ : Γ ⇨̂ Δ} (x : Γ ∋ σ) (ρs : Subs T ρ̂) →
            x /∋ ∘⋆ ρs ≅-⊢ var · x /⊢⋆ ρs
    /∋-∘⋆ x ε = begin
      [ x /∋ id ]  ≡⟨ /∋-id x ⟩
      [ var · x ]  ∎
    /∋-∘⋆ x (ε ▻ ρ) = begin
      [ x /∋ ρ       ]  ≡⟨ P.sym $ var-/⊢ x ρ ⟩
      [ var · x /⊢ ρ ]  ∎
    /∋-∘⋆ x (ρs ▻ ρ₁ ▻ ρ₂) = begin
      [ x /∋ ∘⋆ (ρs ▻ ρ₁) ∘ ρ₂      ]  ≡⟨ /∋-∘ x (∘⋆ (ρs ▻ ρ₁)) ρ₂ ⟩
      [ x /∋ ∘⋆ (ρs ▻ ρ₁) /⊢ ρ₂     ]  ≡⟨ /⊢-cong (/∋-∘⋆ x (ρs ▻ ρ₁)) P.refl ⟩
      [ var · x /⊢⋆ (ρs ▻ ρ₁) /⊢ ρ₂ ]  ∎

    -- Yet another variant of var-/⊢⋆-↑⁺⋆-⇒-/⊢⋆-↑⁺⋆.

    ∘⋆-⇒-/⊢⋆ :
      ∀ {Γ Δ} {ρ̂ : Γ ⇨̂ Δ} (ρs₁ : Subs T ρ̂) (ρs₂ : Subs T ρ̂) →
      ∘⋆ ρs₁ ≅-⇨ ∘⋆ ρs₂ → ∀ {σ} (t : Γ ⊢ σ) → t /⊢⋆ ρs₁ ≅-⊢ t /⊢⋆ ρs₂
    ∘⋆-⇒-/⊢⋆ ρs₁ ρs₂ hyp = var-/⊢⋆-⇒-/⊢⋆ ρs₁ ρs₂ (λ x → begin
      [ var · x /⊢⋆ ρs₁ ]  ≡⟨ P.sym $ /∋-∘⋆ x ρs₁ ⟩
      [ x /∋ ∘⋆ ρs₁     ]  ≡⟨ /∋-cong (P.refl {x = [ x ]}) hyp ⟩
      [ x /∋ ∘⋆ ρs₂     ]  ≡⟨ /∋-∘⋆ x ρs₂ ⟩
      [ var · x /⊢⋆ ρs₂ ]  ∎)

    -- id is a left identity of _∘_.

    id-∘ : ∀ {Γ Δ} {ρ̂ : Γ ⇨̂ Δ} (ρ : Sub T ρ̂) → id ∘ ρ ≅-⇨ ρ
    id-∘ ρ = begin
      [ id ∘ ρ     ]  ≡⟨ Application₂₂.id-∘ application₂₂ ρ ⟩
      [ map [id] ρ ]  ≡⟨ map-[id] ρ ⟩
      [ ρ          ]  ∎

    -- The wk substitution commutes with any other (modulo lifting
    -- etc.).

    wk-∘-↑ : ∀ {Γ Δ} σ {ρ̂ : Γ ⇨̂ Δ} (ρ : Sub T ρ̂) →
             ρ ∘ wk {σ = σ / ρ} ≅-⇨ wk {σ = σ} ∘ ρ ↑
    wk-∘-↑ σ ρ = begin
      [ ρ ∘ wk           ]  ≡⟨ ∘-cong (P.sym $ map-[id] ρ) P.refl ⟩
      [ map [id] ρ ∘ wk  ]  ≡⟨ Application₂₂.wk-∘-↑ application₂₂ σ ρ ⟩
      [ wk {σ = σ} ∘ ρ ↑ ]  ∎

    -- Applying a composed substitution is equivalent to applying one
    -- substitution and then the other.

    /⊢-∘ : ∀ {Γ Δ Ε σ} {ρ̂₁ : Γ ⇨̂ Δ} {ρ̂₂ : Δ ⇨̂ Ε}
           (t : Γ ⊢ σ) (ρ₁ : Sub T ρ̂₁) (ρ₂ : Sub T ρ̂₂) →
           t /⊢ ρ₁ ∘ ρ₂ ≅-⊢ t /⊢ ρ₁ /⊢ ρ₂
    /⊢-∘ t ρ₁ ρ₂ = ∘⋆-⇒-/⊢⋆ (ε ▻ ρ₁ ∘ ρ₂) (ε ▻ ρ₁ ▻ ρ₂) P.refl t

    -- _∘_ is associative.

    ∘-∘ : ∀ {Γ Δ Ε Ζ} {ρ̂₁ : Γ ⇨̂ Δ} {ρ̂₂ : Δ ⇨̂ Ε} {ρ̂₃ : Ε ⇨̂ Ζ}
          (ρ₁ : Sub T ρ̂₁) (ρ₂ : Sub T ρ̂₂) (ρ₃ : Sub T ρ̂₃) →
          ρ₁ ∘ (ρ₂ ∘ ρ₃) ≅-⇨ (ρ₁ ∘ ρ₂) ∘ ρ₃
    ∘-∘ ρ₁ ρ₂ ρ₃ = extensionality P.refl λ x → begin
      [ x /∋ ρ₁ ∘ (ρ₂ ∘ ρ₃) ]  ≡⟨ /∋-∘ x ρ₁ (ρ₂ ∘ ρ₃) ⟩
      [ x /∋ ρ₁ /⊢ ρ₂ ∘ ρ₃  ]  ≡⟨ /⊢-∘ (x /∋ ρ₁) ρ₂ ρ₃ ⟩
      [ x /∋ ρ₁ /⊢ ρ₂ /⊢ ρ₃ ]  ≡⟨ /⊢-cong (P.sym $ /∋-∘ x ρ₁ ρ₂) (P.refl {x = [ ρ₃ ]}) ⟩
      [ x /∋ ρ₁ ∘ ρ₂ /⊢ ρ₃  ]  ≡⟨ P.sym $ /∋-∘ x (ρ₁ ∘ ρ₂) ρ₃ ⟩
      [ x /∋ (ρ₁ ∘ ρ₂) ∘ ρ₃ ]  ∎

    -- If sub t is applied to variable zero then t is returned.

    zero-/⊢-sub : ∀ {Γ σ} (t : Γ ⊢ σ) → var · zero /⊢ sub t ≅-⊢ t
    zero-/⊢-sub t = begin
      [ var · zero /⊢ sub t ]  ≡⟨ var-/⊢ zero (sub t) ⟩
      [ zero /∋ sub t       ]  ≡⟨ P.refl ⟩
      [ t                   ]  ∎

    -- The sub substitution commutes with any other (modulo lifting
    -- etc.).

    ↑-∘-sub : ∀ {Γ Δ σ} {ρ̂ : Γ ⇨̂ Δ} (t : Γ ⊢ σ) (ρ : Sub T ρ̂) →
              sub t ∘ ρ ≅-⇨ ρ ↑ σ ∘ sub (t /⊢ ρ)
    ↑-∘-sub t ρ =
      let lemma = begin
            [ id ∘ ρ                    ]  ≡⟨ id-∘ ρ ⟩
            [ ρ                         ]  ≡⟨ P.sym $ wk-subst-∘-sub ρ (t /⊢ ρ) ⟩
            [ wk-subst ρ ∘ sub (t /⊢ ρ) ]  ∎

      in begin
        [ sub t ∘ ρ                                              ]  ≡⟨ P.refl ⟩
        [ (id ▻ t) ∘ ρ                                           ]  ≡⟨ ▻-∘ id t ρ ⟩
        [ id ∘ ρ ▻ t /⊢ ρ                                        ]  ≡⟨ ▻⇨-cong P.refl lemma (P.sym $ zero-/⊢-sub (t /⊢ ρ)) ⟩
        [ wk-subst ρ ∘ sub (t /⊢ ρ) ▻ var · zero /⊢ sub (t /⊢ ρ) ]  ≡⟨ P.sym $ ▻-∘ (wk-subst ρ) (var · zero) (sub (t /⊢ ρ)) ⟩
        [ (wk-subst ρ ▻ var · zero) ∘ sub (t /⊢ ρ)               ]  ≡⟨ ∘-cong (P.sym $ unfold-↑ ρ) P.refl ⟩
        [ ρ ↑ ∘ sub (t /⊢ ρ)                                     ]  ∎

  -- wk-subst⁺ can be expressed using composition and wk⁺.

  ∘-wk⁺ : ∀ {Γ Δ} {ρ̂ : Γ ⇨̂ Δ} (ρ : Sub T ρ̂) (Δ⁺ : Ctxt⁺ Δ) →
          ρ ∘ wk⁺ Δ⁺ ≅-⇨ wk-subst⁺ Δ⁺ ρ
  ∘-wk⁺ ρ ε = begin
    [ ρ ∘ wk⁺ ε     ]  ≡⟨ P.refl ⟩
    [ ρ ∘ id        ]  ≡⟨ ∘-id ρ ⟩
    [ ρ             ]  ≡⟨ P.refl ⟩
    [ wk-subst⁺ ε ρ ]  ∎
  ∘-wk⁺ ρ (Δ⁺ ▻ σ) = begin
    [ ρ ∘ wk⁺ (Δ⁺ ▻ σ)          ]  ≡⟨ ∘-cong (P.refl {x = [ ρ ]}) (wk⁺-▻ Δ⁺) ⟩
    [ ρ ∘ (wk⁺ Δ⁺ ∘ wk)         ]  ≡⟨ ∘-∘ ρ (wk⁺ Δ⁺) wk ⟩
    [ (ρ ∘ wk⁺ Δ⁺) ∘ wk         ]  ≡⟨ ∘-cong (∘-wk⁺ ρ Δ⁺) P.refl ⟩
    [ wk-subst⁺ Δ⁺ ρ ∘ wk       ]  ≡⟨ ∘-wk (wk-subst⁺ Δ⁺ ρ) ⟩
    [ wk-subst (wk-subst⁺ Δ⁺ ρ) ]  ≡⟨ P.refl ⟩
    [ wk-subst⁺ (Δ⁺ ▻ σ) ρ      ]  ∎

  mutual

    -- wk-subst₊ can be expressed using composition and wk₊.

    ∘-wk₊ : ∀ {Γ Δ} {ρ̂ : Γ ⇨̂ Δ} (ρ : Sub T ρ̂) (Δ₊ : Ctxt₊ Δ) →
            ρ ∘ wk₊ Δ₊ ≅-⇨ wk-subst₊ Δ₊ ρ
    ∘-wk₊ ρ ε = begin
      [ ρ ∘ wk₊ ε     ]  ≡⟨ P.refl ⟩
      [ ρ ∘ id        ]  ≡⟨ ∘-id ρ ⟩
      [ ρ             ]  ≡⟨ P.refl ⟩
      [ wk-subst₊ ε ρ ]  ∎
    ∘-wk₊ ρ (σ ◅ Δ₊) = begin
      [ ρ ∘ wk₊ (σ ◅ Δ₊)          ]  ≡⟨ ∘-cong (P.refl {x = [ ρ ]}) (wk₊-◅ Δ₊) ⟩
      [ ρ ∘ (wk ∘ wk₊ Δ₊)         ]  ≡⟨ ∘-∘ ρ wk (wk₊ Δ₊) ⟩
      [ (ρ ∘ wk) ∘ wk₊ Δ₊         ]  ≡⟨ ∘-cong (∘-wk ρ) P.refl ⟩
      [ wk-subst ρ ∘ wk₊ Δ₊       ]  ≡⟨ ∘-wk₊ (wk-subst ρ) Δ₊ ⟩
      [ wk-subst₊ Δ₊ (wk-subst ρ) ]  ≡⟨ P.refl ⟩
      [ wk-subst₊ (σ ◅ Δ₊) ρ      ]  ∎

    -- Unfolding lemma for wk₊.

    wk₊-◅ : ∀ {Γ σ} (Γ₊ : Ctxt₊ (Γ ▻ σ)) →
            wk₊ (σ ◅ Γ₊) ≅-⇨ wk ∘ wk₊ Γ₊
    wk₊-◅ {σ = σ} Γ₊ = begin
      [ wk₊ (σ ◅ Γ₊)    ]  ≡⟨ P.refl ⟩
      [ wk-subst₊ Γ₊ wk ]  ≡⟨ P.sym $ ∘-wk₊ wk Γ₊ ⟩
      [ wk ∘ wk₊ Γ₊     ]  ∎

  -- A consequence of wk₊-◅.

  /∋-wk₊-◅ : ∀ {Γ τ σ} (x : Γ ∋ τ) (Γ₊ : Ctxt₊ (Γ ▻ σ)) →
             x /∋ wk₊ (σ ◅ Γ₊) ≅-⊢ suc x /∋ wk₊ Γ₊
  /∋-wk₊-◅ {σ = σ} x Γ₊ = begin
    [ x /∋ wk₊ (σ ◅ Γ₊)     ]  ≡⟨ /∋-cong (P.refl {x = [ x ]}) (wk₊-◅ Γ₊) ⟩
    [ x /∋ wk ∘ wk₊ Γ₊      ]  ≡⟨ /∋-∘ x wk (wk₊ Γ₊) ⟩
    [ x /∋ wk /⊢ wk₊ Γ₊     ]  ≡⟨ /⊢-cong (/∋-wk x) P.refl ⟩
    [ var · suc x /⊢ wk₊ Γ₊ ]  ≡⟨ var-/⊢ (suc x) (wk₊ Γ₊) ⟩
    [ suc x /∋ wk₊ Γ₊       ]  ∎
