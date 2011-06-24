------------------------------------------------------------------------
-- Operations and lemmas related to application of substitutions
------------------------------------------------------------------------

{-# OPTIONS --universe-polymorphism #-}

open import Universe

module deBruijn.Substitution.Data.Application.Application1
  {u e} {Uni : Universe u e} where

import deBruijn.Context as Context
open import deBruijn.Substitution.Data.Application.Application22
open import deBruijn.Substitution.Data.Basics
open import deBruijn.Substitution.Data.Map
open import deBruijn.Substitution.Data.Simple
import deBruijn.TermLike as TermLike
open import Function using (_$_)
open import Level using (_⊔_)
open import Relation.Binary.HeterogeneousEquality as H using (_≅_)
open import Relation.Binary.PropositionalEquality as P using (_≡_)

open Context Uni
open TermLike Uni

-- More operations and lemmas related to application. In this module
-- the application operator is assumed to be homogeneous, so some
-- previously proved lemmas can be stated in a less complicated way.

record Application₁ {t} (T : Term-like t) : Set (u ⊔ e ⊔ t) where

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
            Γ₁ ≡ Γ₂ → Δ₁ ≡ Δ₂ → ρ̂₁ ≅ ρ̂₂ → ρs₁ ≅ ρs₂ → ∘⋆ ρs₁ ≅ ∘⋆ ρs₂
  ∘⋆-cong P.refl P.refl H.refl H.refl = H.refl

  abstract

    -- Applying a composed substitution to a variable is equivalent to
    -- applying all the substitutions one after another.

    /∋-∘⋆ : ∀ {Γ Δ σ} {ρ̂ : Γ ⇨̂ Δ} (x : Γ ∋ σ) (ρs : Subs T ρ̂) →
            x /∋ ∘⋆ ρs ≡ var · x /⊢⋆ ρs
    /∋-∘⋆ x ε = begin
      x /∋ id  ≡⟨ /∋-id x ⟩
      var · x  ∎
      where open P.≡-Reasoning
    /∋-∘⋆ x (ε ▻ ρ) = begin
      x /∋ ρ        ≡⟨ P.sym $ var-/⊢ x ρ ⟩
      var · x /⊢ ρ  ∎
      where open P.≡-Reasoning
    /∋-∘⋆ x (ρs ▻ ρ₁ ▻ ρ₂) = begin
      x /∋ ∘⋆ (ρs ▻ ρ₁) ∘ ρ₂       ≡⟨ /∋-∘ x (∘⋆ (ρs ▻ ρ₁)) ρ₂ ⟩
      x /∋ ∘⋆ (ρs ▻ ρ₁) /⊢ ρ₂      ≅⟨ /⊢-cong P.refl P.refl H.refl
                                              (H.≡-to-≅ $ /∋-∘⋆ x (ρs ▻ ρ₁))
                                              H.refl H.refl ⟩
      var · x /⊢⋆ (ρs ▻ ρ₁) /⊢ ρ₂  ∎
      where open P.≡-Reasoning

    -- Yet another variant of var-/⊢⋆-↑⁺⋆-⇒-/⊢⋆-↑⁺⋆.

    ∘⋆-⇒-/⊢⋆ :
      ∀ {Γ Δ} {ρ̂ : Γ ⇨̂ Δ} (ρs₁ : Subs T ρ̂) (ρs₂ : Subs T ρ̂) →
      ∘⋆ ρs₁ ≡ ∘⋆ ρs₂ → ∀ {σ} (t : Γ ⊢ σ) → t /⊢⋆ ρs₁ ≡ t /⊢⋆ ρs₂
    ∘⋆-⇒-/⊢⋆ ρs₁ ρs₂ hyp = var-/⊢⋆-⇒-/⊢⋆ ρs₁ ρs₂ (λ x → begin
      var · x /⊢⋆ ρs₁  ≡⟨ P.sym $ /∋-∘⋆ x ρs₁ ⟩
      x /∋ ∘⋆ ρs₁      ≅⟨ /∋-cong P.refl P.refl H.refl (H.refl {x = x}) H.refl
                                  (H.≡-to-≅ hyp) ⟩
      x /∋ ∘⋆ ρs₂      ≡⟨ /∋-∘⋆ x ρs₂ ⟩
      var · x /⊢⋆ ρs₂  ∎)
      where open P.≡-Reasoning

    -- id is a left identity of _∘_.

    id-∘ : ∀ {Γ Δ} {ρ̂ : Γ ⇨̂ Δ} (ρ : Sub T ρ̂) → id ∘ ρ ≡ ρ
    id-∘ ρ = begin
      id ∘ ρ      ≡⟨ Application₂₂.id-∘ application₂₂ ρ ⟩
      map [id] ρ  ≡⟨ map-[id] ρ ⟩
      ρ           ∎
      where open P.≡-Reasoning

    -- The wk substitution commutes with any other (more or less).

    wk-∘-↑ : ∀ {Γ Δ} σ {ρ̂ : Γ ⇨̂ Δ} (ρ : Sub T ρ̂) →
             ρ ∘ wk ≡ wk {σ = σ} ∘ ρ ↑
    wk-∘-↑ σ ρ = begin
      ρ ∘ wk            ≅⟨ ∘-cong P.refl P.refl P.refl H.refl H.refl
                                  (H.≡-to-≅ $ P.sym $ map-[id] ρ) H.refl ⟩
      map [id] ρ ∘ wk   ≡⟨ Application₂₂.wk-∘-↑ application₂₂ σ ρ ⟩
      wk {σ = σ} ∘ ρ ↑  ∎
      where open P.≡-Reasoning

    -- Applying a composed substitution is equivalent to applying one
    -- substitution and then the other.

    /⊢-∘ : ∀ {Γ Δ Ε σ} {ρ̂₁ : Γ ⇨̂ Δ} {ρ̂₂ : Δ ⇨̂ Ε}
           (t : Γ ⊢ σ) (ρ₁ : Sub T ρ̂₁) (ρ₂ : Sub T ρ̂₂) →
           t /⊢ ρ₁ ∘ ρ₂ ≡ t /⊢ ρ₁ /⊢ ρ₂
    /⊢-∘ t ρ₁ ρ₂ = ∘⋆-⇒-/⊢⋆ (ε ▻ ρ₁ ∘ ρ₂) (ε ▻ ρ₁ ▻ ρ₂) P.refl t

    -- _∘_ is associative.

    ∘-∘ : ∀ {Γ Δ Ε Ζ} {ρ̂₁ : Γ ⇨̂ Δ} {ρ̂₂ : Δ ⇨̂ Ε} {ρ̂₃ : Ε ⇨̂ Ζ}
          (ρ₁ : Sub T ρ̂₁) (ρ₂ : Sub T ρ̂₂) (ρ₃ : Sub T ρ̂₃) →
          ρ₁ ∘ (ρ₂ ∘ ρ₃) ≡ (ρ₁ ∘ ρ₂) ∘ ρ₃
    ∘-∘ ρ₁ ρ₂ ρ₃ = H.≅-to-≡ $
      extensionality P.refl H.refl λ x → begin
        x /∋ ρ₁ ∘ (ρ₂ ∘ ρ₃)  ≡⟨ /∋-∘ x ρ₁ (ρ₂ ∘ ρ₃) ⟩
        x /∋ ρ₁ /⊢ ρ₂ ∘ ρ₃   ≡⟨ /⊢-∘ (x /∋ ρ₁) ρ₂ ρ₃ ⟩
        x /∋ ρ₁ /⊢ ρ₂ /⊢ ρ₃  ≅⟨ /⊢-cong P.refl P.refl H.refl
                                        (H.≡-to-≅ $ P.sym $ /∋-∘ x ρ₁ ρ₂)
                                        H.refl (H.refl {x = ρ₃}) ⟩
        x /∋ ρ₁ ∘ ρ₂ /⊢ ρ₃   ≡⟨ P.sym $ /∋-∘ x (ρ₁ ∘ ρ₂) ρ₃ ⟩
        x /∋ (ρ₁ ∘ ρ₂) ∘ ρ₃  ∎
      where open H.≅-Reasoning

    -- If sub t is applied to variable zero then t is returned.

    zero-/⊢-sub : ∀ {Γ σ} (t : Γ ⊢ σ) → var · zero /⊢ sub t ≡ t
    zero-/⊢-sub t = begin
      var · zero /⊢ sub t  ≡⟨ var-/⊢ zero (sub t) ⟩
      zero /∋ sub t        ≡⟨ P.refl ⟩
      t                    ∎
      where open P.≡-Reasoning

    -- The sub substitution commutes (more or less) with any other.

    ↑-∘-sub : ∀ {Γ Δ σ} {ρ̂ : Γ ⇨̂ Δ} (t : Γ ⊢ σ) (ρ : Sub T ρ̂) →
              sub t ∘ ρ ≅ _↑ {σ = σ} ρ ∘ sub (t /⊢ ρ)
    ↑-∘-sub t ρ =
      let lemma = begin
            id ∘ ρ                     ≡⟨ id-∘ ρ ⟩
            ρ                          ≡⟨ P.sym $ wk-subst-∘-sub ρ (t /⊢ ρ) ⟩
            wk-subst ρ ∘ sub (t /⊢ ρ)  ∎

      in begin
        sub t ∘ ρ                                 ≡⟨ P.refl ⟩
        (id ▻ t) ∘ ρ                              ≅⟨ ▻-∘ id t ρ ⟩
        id ∘ ρ ▻ t /⊢ ρ                           ≅⟨ ▻⇨-cong P.refl P.refl H.refl H.refl
                                                             lemma (H.≡-to-≅ $ P.sym $ zero-/⊢-sub (t /⊢ ρ)) ⟩
        wk-subst ρ ∘ sub (t /⊢ ρ) ▻
          var · zero /⊢ sub (t /⊢ ρ)              ≅⟨ H.sym $ ▻-∘ (wk-subst ρ) (var · zero) (sub (t /⊢ ρ)) ⟩
        (wk-subst ρ ▻ var · zero) ∘ sub (t /⊢ ρ)  ≅⟨ ∘-cong P.refl P.refl P.refl
                                                            (▻̂-cong P.refl P.refl H.refl H.refl
                                                                    (H.≡-to-≅ $ P.sym $ corresponds var zero))
                                                            H.refl (H.sym $ unfold-↑ ρ) H.refl ⟩
        ρ ↑ ∘ sub (t /⊢ ρ)                        ∎
      where open H.≅-Reasoning
