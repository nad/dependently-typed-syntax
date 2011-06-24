------------------------------------------------------------------------
-- The two definitions of substitutions are isomorphic (assuming
-- extensionality)
------------------------------------------------------------------------

{-# OPTIONS --universe-polymorphism #-}

import deBruijn.TermLike as TermLike
open import Universe

module deBruijn.Substitution.Isomorphic
  {u e t} {Uni : Universe u e} (T : TermLike.Term-like Uni t) where

import deBruijn.Context as Context
import deBruijn.Substitution.Data.Basics
import deBruijn.Substitution.Function.Basics
open import Function using (_$_)
open import Function.Inverse using (_↔_)
open import Level using (_⊔_)
open import Relation.Binary.HeterogeneousEquality as H using (_≅_)
open import Relation.Binary.PropositionalEquality as P using (_≡_)

open Context Uni
private
  open module DB = deBruijn.Substitution.Data.Basics T using (ε; _▻_)
  open module FB = deBruijn.Substitution.Function.Basics T
    using (ε⇨; _▻⇨_)

isomorphic :
  P.Extensionality (e ⊔ u) (Level.suc (e ⊔ u ⊔ t)) →
  ∀ {Γ Δ} {ρ̂ : Γ ⇨̂ Δ} → FB.Sub ρ̂ ↔ DB.Sub ρ̂
isomorphic ext = record
  { to         = P.→-to-⟶ (to _)
  ; from       = P.→-to-⟶ from
  ; inverse-of = record
    { left-inverse-of  = from∘to _
    ; right-inverse-of = to∘from
    }
  }
  where
  to : ∀ Γ {Δ} {ρ̂ : Γ ⇨̂ Δ} → FB.Sub ρ̂ → DB.Sub ρ̂
  to ε               ρ = ε
  to (Γ ▻ σ) {ρ̂ = ρ̂} ρ =
    P.subst (λ v → DB.Sub (t̂ail ρ̂ ▻̂ v))
            (P.sym $ FB.head-lemma ρ)
            (to Γ (FB.tail ρ) ▻ FB.head ρ)

  from : ∀ {Γ Δ} {ρ̂ : Γ ⇨̂ Δ} → DB.Sub ρ̂ → FB.Sub ρ̂
  from ε       = ε⇨
  from (ρ ▻ t) = from ρ ▻⇨ t

  from-cong : ∀ {Γ Δ} {ρ̂₁ ρ̂₂ : Γ ⇨̂ Δ}
                {ρ₁ : DB.Sub ρ̂₁} {ρ₂ : DB.Sub ρ̂₂} →
              ρ̂₁ ≡ ρ̂₂ → ρ₁ ≅ ρ₂ → from ρ₁ ≅ from ρ₂
  from-cong P.refl H.refl = H.refl

  abstract

    from∘to : ∀ Γ {Δ} {ρ̂ : Γ ⇨̂ Δ} (ρ : FB.Sub ρ̂) → from (to Γ ρ) ≡ ρ
    from∘to ε ρ = begin
      ε⇨  ≡⟨ P.sym $ FB.ηε ext ρ ⟩
      ρ   ∎
      where open P.≡-Reasoning
    from∘to (Γ ▻ σ) {ρ̂ = ρ̂} ρ = H.≅-to-≡ (begin
      from (P.subst (λ v → DB.Sub (t̂ail ρ̂ ▻̂ v))
                    (P.sym $ FB.head-lemma ρ)
                    (to Γ (FB.tail ρ) ▻ FB.head ρ))  ≅⟨ from-cong (H.≅-to-≡ $ ▻̂-cong P.refl P.refl H.refl H.refl
                                                                                     (H.≡-to-≅ $ FB.head-lemma ρ))
                                                                  (H.≡-subst-removable (λ v → DB.Sub (t̂ail ρ̂ ▻̂ v))
                                                                                       (P.sym $ FB.head-lemma ρ) _) ⟩
      from (to Γ (FB.tail ρ) ▻ FB.head ρ)            ≡⟨ P.refl ⟩
      from (to Γ (FB.tail ρ)) ▻⇨ FB.head ρ           ≅⟨ FB.▻⇨-cong P.refl P.refl H.refl H.refl
                                                                   (H.≡-to-≅ $ from∘to Γ (FB.tail ρ))
                                                                   (H.refl {x = FB.head ρ}) ⟩
      FB.tail ρ ▻⇨ FB.head ρ                         ≅⟨ H.sym $ FB.η▻ ext ρ ⟩
      ρ                                              ∎)
      where open H.≅-Reasoning

    to∘from : ∀ {Γ Δ} {ρ̂ : Γ ⇨̂ Δ} (ρ : DB.Sub ρ̂) → to Γ (from ρ) ≡ ρ
    to∘from ε       = P.refl
    to∘from (ρ ▻ t) = H.≅-to-≡ $
      DB.▻⇨-cong P.refl P.refl H.refl H.refl
        (H.≡-to-≅ (to∘from ρ)) H.refl
