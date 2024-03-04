------------------------------------------------------------------------
-- The two definitions of substitutions are isomorphic (assuming
-- extensionality)
------------------------------------------------------------------------

open import Data.Universe.Indexed

module deBruijn.Substitution.Isomorphic
  {i u e} {Uni : IndexedUniverse i u e} where

import Axiom.Extensionality.Propositional as E
open import Data.Product
import deBruijn.Context; open deBruijn.Context Uni
open import deBruijn.Substitution.Data.Basics as D using (ε; _▻_; [_])
open import deBruijn.Substitution.Function.Basics as F
  using (ε⇨; _▻⇨_) renaming (_▻⇨[_]_ to _▻⇨[_]F_)
open import Function
open import Level using (_⊔_)
import Relation.Binary.PropositionalEquality as P

open P.≡-Reasoning

isomorphic :
  ∀ {t} {T : Term-like t} →
  E.Extensionality (i ⊔ u ⊔ e) (i ⊔ u ⊔ e ⊔ t) →
  ∀ {Γ Δ} {ρ̂ : Γ ⇨̂ Δ} →
  Inverse ([ Var ⟶ T ]-setoid ρ̂) (P.setoid $ D.Sub T ρ̂)
isomorphic {T = T} ext = record
  { to        = to _
  ; from      = from
  ; to-cong   = λ ρ₁≅ρ₂ → D.≅-⇨-⇒-≡ $ to-cong ρ₁≅ρ₂
  ; from-cong = λ { P.refl → _ ∎-⟶ }
  ; inverse   =
        (λ { [ P.refl ] → D.≅-⇨-⇒-≡ $ to∘from _ })
      , (λ { P.refl → from∘to _ _ })
  }
  where
  to : ∀ Γ {Δ} {ρ̂ : Γ ⇨̂ Δ} → F.Sub T ρ̂ → D.Sub T ρ̂
  to ε               ρ = ε
  to (Γ ▻ σ) {ρ̂ = ρ̂} ρ =
    P.subst (λ v → D.Sub T (t̂ail ρ̂ ▻̂ v))
            (≅-Value-⇒-≡ $ P.sym $ F.head-lemma ρ)
            (to Γ (F.tail ρ) ▻ F.head ρ)

  from : ∀ {Γ Δ} {ρ̂ : Γ ⇨̂ Δ} → D.Sub T ρ̂ → F.Sub T ρ̂
  from ε       = ε⇨
  from (ρ ▻ t) = from ρ ▻⇨ t

  to-▻ : ∀ {Γ Δ σ} {ρ̂ : Γ ▻ σ ⇨̂ Δ} (ρ : F.Sub T ρ̂) →
         D._≅-⇨_ (to (Γ ▻ σ) ρ) (to Γ (F.tail ρ) ▻ F.head ρ)
  to-▻ {ρ̂ = ρ̂} ρ =
    D.drop-subst-Sub (λ v → t̂ail ρ̂ ▻̂ v)
                     (≅-Value-⇒-≡ $ P.sym $ F.head-lemma ρ)

  abstract

    to-cong : ∀ {Γ₁ Δ₁} {ρ̂₁ : Γ₁ ⇨̂ Δ₁} {ρ₁ : F.Sub T ρ̂₁}
                {Γ₂ Δ₂} {ρ̂₂ : Γ₂ ⇨̂ Δ₂} {ρ₂ : F.Sub T ρ̂₂} →
              F._≅-⇨_ ρ₁ ρ₂ → D._≅-⇨_ (to Γ₁ ρ₁) (to Γ₂ ρ₂)
    to-cong {Γ₁ = ε}     {ρ₁ = _ , _} {ρ₂ = ._ , _}     [ P.refl ] = P.refl
    to-cong {Γ₁ = Γ ▻ σ} {ρ₁ = ρ₁}    {ρ₂ = ._ , corr₂} [ P.refl ] =
      let ρ₂ = [_⟶_].function ρ₁ , corr₂ in begin
       [ to (Γ ▻ σ) ρ₁                ]  ≡⟨ to-▻ ρ₁ ⟩
       [ to Γ (F.tail ρ₁) ▻ F.head ρ₁ ]  ≡⟨ D.▻⇨-cong P.refl (to-cong [ P.refl ]) P.refl ⟩
       [ to Γ (F.tail ρ₂) ▻ F.head ρ₂ ]  ≡⟨ P.sym $ to-▻ ρ₂ ⟩
       [ to (Γ ▻ σ) ρ₂                ]  ∎

  from-cong : ∀ {Γ₁ Δ₁} {ρ̂₁ : Γ₁ ⇨̂ Δ₁} {ρ₁ : D.Sub T ρ̂₁}
                {Γ₂ Δ₂} {ρ̂₂ : Γ₂ ⇨̂ Δ₂} {ρ₂ : D.Sub T ρ̂₂} →
              D._≅-⇨_ ρ₁ ρ₂ → F._≅-⇨_ (from ρ₁) (from ρ₂)
  from-cong P.refl = [ P.refl ]

  abstract

    from∘to : ∀ Γ {Δ} {ρ̂ : Γ ⇨̂ Δ} (ρ : F.Sub T ρ̂) →
              F._≅-⇨_ (from (to Γ ρ)) ρ
    from∘to ε ρ =
      ε⇨  ≅-⟶⟨ sym-⟶ $ F.ηε ext ρ ⟩
      ρ   ∎-⟶
    from∘to (Γ ▻ σ) {ρ̂ = ρ̂} ρ =
      from (to (Γ ▻ σ) ρ)                 ≅-⟶⟨ from-cong $ to-▻ ρ ⟩
      from (to Γ (F.tail ρ) ▻ F.head ρ)   ≅-⟶⟨ _ ∎-⟶ ⟩
      from (to Γ (F.tail ρ)) ▻⇨ F.head ρ  ≅-⟶⟨ F.▻⇨-cong P.refl (from∘to Γ (F.tail ρ)) P.refl ⟩
      F.tail ρ ▻⇨ F.head ρ                ≅-⟶⟨ sym-⟶ $ F.η▻ ext ρ ⟩
      ρ                                   ∎-⟶

    to∘from :
      ∀ {Γ Δ} {ρ̂ : Γ ⇨̂ Δ} (ρ : D.Sub T ρ̂) {c} →
      D._≅-⇨_ (to Γ ([_⟶_].function (from ρ) , c)) ρ
    to∘from ε                         = P.refl
    to∘from (_▻_ {σ = σ} ρ t) {c = c} = begin
      [ to (_ ▻ _) ([_⟶_].function (from (_▻_ {σ = σ} ρ t)) , c) ]  ≡⟨⟩
      [ to (_ ▻ _) ([_⟶_].function (from ρ ▻⇨ t) , c)            ]  ≡⟨ to-▻ _ ⟩
      [ to _ ([_⟶_].function (from ρ) , _) ▻ t                   ]  ≡⟨ D.▻⇨-cong P.refl (to-cong [ P.refl ]) P.refl ⟩
      [ to _ (from ρ) ▻ t                                        ]  ≡⟨ D.▻⇨-cong P.refl (to∘from ρ) P.refl ⟩
      [ ρ ▻ t                                                    ]  ∎
