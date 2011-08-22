------------------------------------------------------------------------
-- The two definitions of context extensions are isomorphic
------------------------------------------------------------------------

{-# OPTIONS --universe-polymorphism #-}

open import Universe

module deBruijn.Context.Extension.Isomorphic
  {i u e} (Uni : Indexed-universe i u e) where

import deBruijn.Context.Basics          as Basics
import deBruijn.Context.Extension.Left  as Left
import deBruijn.Context.Extension.Right as Right
open import Function
open import Function.Inverse using (_↔_)
import Relation.Binary.PropositionalEquality as P

open Basics Uni
open Left   Uni
open Right  Uni
open P.≡-Reasoning

-- Ctxt₊-s can be turned into Ctxt⁺-s.

₊-to-⁺ : ∀ {Γ} → Ctxt₊ Γ → Ctxt⁺ Γ
₊-to-⁺ ε        = ε
₊-to-⁺ (σ ◅ Γ₊) = ε ▻ σ ⁺++⁺ ₊-to-⁺ Γ₊

abstract

  -- The semantics is preserved.

  ++⁺-₊-to-⁺ : ∀ {Γ} (Γ₊ : Ctxt₊ Γ) → Γ ++₊ Γ₊ ≅-Ctxt Γ ++⁺ ₊-to-⁺ Γ₊
  ++⁺-₊-to-⁺     ε        = P.refl
  ++⁺-₊-to-⁺ {Γ} (σ ◅ Γ₊) = begin
    Γ ▻ σ ++₊ Γ₊                  ≡⟨ ++⁺-₊-to-⁺ Γ₊ ⟩
    Γ ▻ σ ++⁺ ₊-to-⁺ Γ₊           ≡⟨ ++⁺-++⁺ (ε ▻ σ) (₊-to-⁺ Γ₊) ⟩
    Γ ++⁺ (ε ▻ σ ⁺++⁺ ₊-to-⁺ Γ₊)  ∎

mutual

  -- Ctxt⁺-s can be turned into Ctxt₊-s.

  ⁺-to-₊ : ∀ {Γ} → Ctxt⁺ Γ → Ctxt₊ Γ
  ⁺-to-₊ ε        = ε
  ⁺-to-₊ (Γ⁺ ▻ σ) =
    ⁺-to-₊ Γ⁺ ₊++₊ P.subst Ctxt₊ (++₊-⁺-to-₊ Γ⁺) (σ ◅ ε)

  abstract

    -- The semantics is preserved.

    ++₊-⁺-to-₊ : ∀ {Γ} (Γ⁺ : Ctxt⁺ Γ) → Γ ++⁺ Γ⁺ ≅-Ctxt Γ ++₊ ⁺-to-₊ Γ⁺
    ++₊-⁺-to-₊     ε        = P.refl
    ++₊-⁺-to-₊ {Γ} (Γ⁺ ▻ σ) =
      let σ◅ε = P.subst Ctxt₊ (++₊-⁺-to-₊ Γ⁺) (σ ◅ ε)

      in begin
      Γ ++⁺ Γ⁺ ▻ σ                ≡⟨ P.refl ⟩
      Γ ++⁺ Γ⁺ ++₊ (σ ◅ ε)        ≡⟨ P.sym $ ++₊-cong $ drop-subst-Ctxt₊ id (++₊-⁺-to-₊ Γ⁺) ⟩
      Γ ++₊ ⁺-to-₊ Γ⁺ ++₊ σ◅ε     ≡⟨ ++₊-++₊ (⁺-to-₊ Γ⁺) σ◅ε ⟩
      Γ ++₊ (⁺-to-₊ Γ⁺ ₊++₊ σ◅ε)  ∎

-- Some congruence lemmas.

₊-to-⁺-cong : ∀ {Γ₁} {Γ₊₁ : Ctxt₊ Γ₁}
                {Γ₂} {Γ₊₂ : Ctxt₊ Γ₂} →
              Γ₊₁ ≅-Ctxt₊ Γ₊₂ → ₊-to-⁺ Γ₊₁ ≅-Ctxt⁺ ₊-to-⁺ Γ₊₂
₊-to-⁺-cong P.refl = P.refl

⁺-to-₊-cong : ∀ {Γ₁} {Γ⁺₁ : Ctxt⁺ Γ₁}
                {Γ₂} {Γ⁺₂ : Ctxt⁺ Γ₂} →
              Γ⁺₁ ≅-Ctxt⁺ Γ⁺₂ → ⁺-to-₊ Γ⁺₁ ≅-Ctxt₊ ⁺-to-₊ Γ⁺₂
⁺-to-₊-cong P.refl = P.refl

-- Ctxt⁺ and Ctxt₊ are isomorphic.

Ctxt⁺↔Ctxt₊ : ∀ Γ → Ctxt⁺ Γ ↔ Ctxt₊ Γ
Ctxt⁺↔Ctxt₊ Γ = record
  { to         = P.→-to-⟶ ⁺-to-₊
  ; from       = P.→-to-⟶ ₊-to-⁺
  ; inverse-of = record
    { left-inverse-of  = λ Γ⁺ → ≅-Ctxt⁺-⇒-≡ $ ₊-to-⁺-⁺-to-₊ Γ⁺
    ; right-inverse-of = λ Γ₊ → ≅-Ctxt₊-⇒-≡ $ ⁺-to-₊-₊-to-⁺ Γ₊
    }
  }
  where
  abstract
    ₊-to-⁺-⁺-to-₊ : (Γ⁺ : Ctxt⁺ Γ) → ₊-to-⁺ (⁺-to-₊ Γ⁺) ≅-Ctxt⁺ Γ⁺
    ₊-to-⁺-⁺-to-₊ Γ⁺ = cancel-++⁺-left _ _ (begin
      Γ ++⁺ ₊-to-⁺ (⁺-to-₊ Γ⁺)  ≡⟨ P.sym $ ++⁺-₊-to-⁺ (⁺-to-₊ Γ⁺) ⟩
      Γ ++₊ (⁺-to-₊ Γ⁺)         ≡⟨ P.sym $ ++₊-⁺-to-₊ Γ⁺ ⟩
      Γ ++⁺ Γ⁺                  ∎)

    ⁺-to-₊-₊-to-⁺ : (Γ₊ : Ctxt₊ Γ) → ⁺-to-₊ (₊-to-⁺ Γ₊) ≅-Ctxt₊ Γ₊
    ⁺-to-₊-₊-to-⁺ Γ₊ = cancel-++₊-left _ _ (begin
      Γ ++₊ ⁺-to-₊ (₊-to-⁺ Γ₊)  ≡⟨ P.sym $ ++₊-⁺-to-₊ (₊-to-⁺ Γ₊) ⟩
      Γ ++⁺ (₊-to-⁺ Γ₊)         ≡⟨ P.sym $ ++⁺-₊-to-⁺ Γ₊ ⟩
      Γ ++₊ Γ₊                  ∎)
