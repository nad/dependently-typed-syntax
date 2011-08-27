------------------------------------------------------------------------
-- The values that are used by the NBE algorithm
------------------------------------------------------------------------

import Level
open import Universe

module README.DependentlyTyped.NBE.Value
  {Uni₀ : Universe Level.zero Level.zero}
  where

open import Data.Product renaming (curry to c; uncurry to uc)
open import deBruijn.Substitution.Data
open import Function using (id; _ˢ_; _$_) renaming (const to k)
open import README.DependentlyTyped.NormalForm
open import README.DependentlyTyped.NormalForm.Substitution
import README.DependentlyTyped.Term as Term; open Term Uni₀
open import Relation.Binary.PropositionalEquality as P using (_≡_)

open P.≡-Reasoning

-- A wrapper which is used to make V̌alue "constructor-headed", which
-- in turn makes Agda infer more types for us.

infix 4 _⊢_⟨ne⟩

record _⊢_⟨ne⟩ (Γ : Ctxt) (σ : Type Γ) : Set where
  constructor [_]
  field t : Γ ⊢ σ ⟨ ne ⟩

mutual

  -- The values.

  V̌alue′ : ∀ Γ sp (σ : IType Γ sp) → Set
  V̌alue′ Γ ⋆           σ = Γ ⊢ ⋆  , σ ⟨ ne ⟩
  V̌alue′ Γ el          σ = Γ ⊢ el , σ ⟨ne⟩
  V̌alue′ Γ (π sp₁ sp₂) σ =
    Σ (V̌alue-π Γ sp₁ sp₂ σ) (W̌ell-behaved sp₁ sp₂ σ)

  V̌alue : (Γ : Ctxt) (σ : Type Γ) → Set
  V̌alue Γ (sp , σ) = V̌alue′ Γ sp σ

  V̌alue-π : ∀ Γ sp₁ sp₂ → IType Γ (π sp₁ sp₂) → Set
  V̌alue-π Γ sp₁ sp₂ σ =
    (Γ₊ : Ctxt₊ Γ)
    (v : V̌alue′ (Γ ++₊ Γ₊) sp₁ (ifst σ /̂I ŵk₊ Γ₊)) →
    V̌alue′ (Γ ++₊ Γ₊) sp₂ (isnd σ /̂I ŵk₊ Γ₊ ↑̂ ∘̂ ŝub ⟦̌ v ⟧)

    -- The use of Ctxt₊ rather than Ctxt⁺ in V̌alue-π is important: it
    -- seems to make it much easier to define weakening for V̌alue.

  W̌ell-behaved :
    ∀ {Γ} sp₁ sp₂ σ → V̌alue-π Γ sp₁ sp₂ σ → Set
  W̌ell-behaved {Γ} sp₁ sp₂ σ f =
    ∀ Γ₊ v → (⟦̌ σ ∣ f ⟧-π /̂Val ŵk₊ Γ₊) ˢ ⟦̌ v ⟧ ≅-Value ⟦̌ f Γ₊ v ⟧

  -- The semantics of a value.

  ⟦̌_⟧ : ∀ {Γ sp σ} → V̌alue Γ (sp , σ) → Value Γ (sp , σ)
  ⟦̌ v ⟧ = ⟦ řeify _ v ⟧n

  ⟦̌_∣_⟧-π : ∀ {Γ sp₁ sp₂} σ →
            V̌alue-π Γ sp₁ sp₂ σ → Value Γ (π sp₁ sp₂ , σ)
  ⟦̌ _ ∣ f ⟧-π = ⟦ řeify-π _ _ _ f ⟧n

  -- Neutral terms can be turned into normal terms using reflection
  -- followed by reification.

  ňeutral-to-normal :
    ∀ {Γ} sp {σ} → Γ ⊢ sp , σ ⟨ ne ⟩ → Γ ⊢ sp , σ ⟨ no ⟩
  ňeutral-to-normal sp t = řeify sp (řeflect sp t)

  -- A normal term corresponding to variable zero.

  žero : ∀ {Γ} sp σ → Γ ▻ (sp , σ) ⊢ sp , σ /̂I ŵk ⟨ no ⟩
  žero sp σ = ňeutral-to-normal sp (var zero[ , σ ])

  -- Reification.

  řeify : ∀ {Γ} sp {σ} → V̌alue Γ (sp , σ) → Γ ⊢ sp , σ ⟨ no ⟩
  řeify ⋆           t     = ne ⋆  t
  řeify el          [ t ] = ne el t
  řeify (π sp₁ sp₂) f     = řeify-π sp₁ sp₂ _ (proj₁ f)

  řeify-π : ∀ {Γ} sp₁ sp₂ σ →
            V̌alue-π Γ sp₁ sp₂ σ → Γ ⊢ π sp₁ sp₂ , σ ⟨ no ⟩
  řeify-π {Γ} sp₁ sp₂ σ f = čast sp₁ σ $
    ƛ (řeify sp₂ (f (fst σ ◅ ε) (řeflect sp₁ (var zero))))

  čast : ∀ {Γ} sp₁ {sp₂} (σ : IType Γ (π sp₁ sp₂)) →
         let ρ̂ = ŵk ↑̂ ∘̂ ŝub ⟦ žero sp₁ (ifst σ) ⟧n in
         Γ ⊢ Type-π (fst σ) (snd σ /̂ ρ̂) ⟨ no ⟩ →
         Γ ⊢ , σ ⟨ no ⟩
  čast {Γ} sp₁ σ =
    P.subst (λ σ → Γ ⊢ σ ⟨ no ⟩)
            (≅-Type-⇒-≡ $ π-fst-snd-ŵk-ŝub-žero sp₁ σ)

  -- Reflection.

  řeflect : ∀ {Γ} sp {σ} → Γ ⊢ sp , σ ⟨ ne ⟩ → V̌alue Γ (sp , σ)
  řeflect ⋆           t = t
  řeflect el          t = [ t ]
  řeflect (π sp₁ sp₂) t =
    (λ Γ₊ v → řeflect sp₂ ((t /⊢n Renaming.wk₊ Γ₊) · řeify sp₁ v)) ,
    řeflect-π-well-behaved sp₁ sp₂ t

  abstract

    řeflect-π-well-behaved :
      ∀ {Γ} sp₁ sp₂ {σ} (t : Γ ⊢ π sp₁ sp₂ , σ ⟨ ne ⟩) Γ₊ v →
      let t′ = ňeutral-to-normal sp₂
                 ((t /⊢n Renaming.wk) · žero sp₁ (ifst σ)) in
      (⟦ čast sp₁ σ (ƛ t′) ⟧n /̂Val ŵk₊ Γ₊) ˢ ⟦̌ v ⟧
        ≅-Value
      ⟦ ňeutral-to-normal sp₂ ((t /⊢n Renaming.wk₊ Γ₊) · řeify sp₁ v) ⟧n
    řeflect-π-well-behaved sp₁ sp₂ {σ} t Γ₊ v =
      let t′ = ňeutral-to-normal sp₂
                 ((t /⊢n Renaming.wk) · žero sp₁ (ifst σ))
          v′ = řeify sp₁ v

          lemma′ = begin
            [ ⟦ čast sp₁ σ (ƛ t′) ⟧n /̂Val ŵk₊ Γ₊ ]  ≡⟨ /̂Val-cong (ňeutral-to-normal-identity-π sp₁ sp₂ t) P.refl ⟩
            [ ⟦ t ⟧n                 /̂Val ŵk₊ Γ₊ ]  ≡⟨ t /⊢n-lemma Renaming.wk₊ Γ₊ ⟩
            [ ⟦ t /⊢n Renaming.wk₊ Γ₊ ⟧n         ]  ∎

      in begin
      [ (⟦ čast sp₁ σ (ƛ t′) ⟧n /̂Val ŵk₊ Γ₊) ˢ ⟦ v′ ⟧n            ]  ≡⟨ ˢ-cong lemma′ P.refl ⟩
      [ ⟦ t /⊢n Renaming.wk₊ Γ₊ ⟧n           ˢ ⟦ v′ ⟧n            ]  ≡⟨ P.refl ⟩
      [ ⟦ (t /⊢n Renaming.wk₊ Γ₊) · v′ ⟧n                         ]  ≡⟨ P.sym $ ňeutral-to-normal-identity sp₂ _ ⟩
      [ ⟦ ňeutral-to-normal sp₂ ((t /⊢n Renaming.wk₊ Γ₊) · v′) ⟧n ]  ∎

    -- A given context morphism is equal to the identity.

    ŵk-ŝub-žero :
      ∀ {Γ} sp₁ {sp₂} (σ : IType Γ (π sp₁ sp₂)) →
      ŵk ↑̂ fst σ ∘̂ ŝub ⟦ žero sp₁ (ifst σ) ⟧n ≅-⇨̂ îd[ Γ ▻ fst σ ]
    ŵk-ŝub-žero sp₁ σ = begin
      [ ŵk ↑̂ ∘̂ ŝub ⟦ žero sp₁ (ifst σ) ⟧n ]  ≡⟨ ∘̂-cong (P.refl {x = [ ŵk ↑̂ ]})
                                                       (ŝub-cong (ňeutral-to-normal-identity sp₁ (var zero))) ⟩
      [ ŵk ↑̂ ∘̂ ŝub ⟦ var zero          ⟧n ]  ≡⟨ P.refl ⟩
      [ îd                                ]  ∎

    -- A corollary of the lemma above.

    π-fst-snd-ŵk-ŝub-žero :
      ∀ {Γ} sp₁ {sp₂} (σ : IType Γ (π sp₁ sp₂)) →
      Type-π (fst σ) (snd σ /̂ ŵk ↑̂ ∘̂ ŝub ⟦ žero sp₁ (ifst σ) ⟧n) ≅-Type
      (, σ)
    π-fst-snd-ŵk-ŝub-žero sp₁ σ = begin
      [ Type-π (fst σ) (snd σ /̂ ŵk ↑̂ ∘̂ ŝub ⟦ žero sp₁ (ifst σ) ⟧n) ]  ≡⟨ Type-π-cong $ /̂-cong (P.refl {x = [ snd σ ]})
                                                                                              (ŵk-ŝub-žero sp₁ σ) ⟩
      [ Type-π (fst σ) (snd σ)                                     ]  ≡⟨ P.refl ⟩
      [ , σ                                                        ]  ∎

    -- In the semantics řeify is a left inverse of řeflect.

    ňeutral-to-normal-identity :
      ∀ {Γ} sp {σ} (t : Γ ⊢ sp , σ ⟨ ne ⟩) →
      ⟦ ňeutral-to-normal sp t ⟧n ≅-Value ⟦ t ⟧n
    ňeutral-to-normal-identity ⋆           t = P.refl
    ňeutral-to-normal-identity el          t = P.refl
    ňeutral-to-normal-identity (π sp₁ sp₂) t =
      ňeutral-to-normal-identity-π sp₁ sp₂ t

    ňeutral-to-normal-identity-π :
      ∀ {Γ} sp₁ sp₂ {σ} (t : Γ ⊢ π sp₁ sp₂ , σ ⟨ ne ⟩) →
      let t′ = ňeutral-to-normal sp₂
                 ((t /⊢n Renaming.wk) · žero sp₁ (ifst σ)) in
      ⟦ čast sp₁ σ (ƛ t′) ⟧n ≅-Value ⟦ t ⟧n
    ňeutral-to-normal-identity-π sp₁ sp₂ {σ} t =
      let t′ = (t /⊢n Renaming.wk) · žero sp₁ (ifst σ)

          lemma = begin
            [ ⟦ ňeutral-to-normal sp₂ t′ ⟧n                   ]  ≡⟨ ňeutral-to-normal-identity sp₂ t′ ⟩
            [ ⟦ t′ ⟧n                                         ]  ≡⟨ P.refl ⟩
            [ ⟦ t /⊢n Renaming.wk ⟧n ˢ ⟦ žero sp₁ (ifst σ) ⟧n ]  ≡⟨ ˢ-cong (P.sym $ t /⊢n-lemma Renaming.wk)
                                                                           (ňeutral-to-normal-identity sp₁ (var zero)) ⟩
            [ (⟦ t ⟧n /̂Val ŵk)       ˢ lookup zero            ]  ≡⟨ P.refl ⟩
            [ uc ⟦ t ⟧n                                       ]  ∎

      in begin
      [ ⟦ čast sp₁ σ (ƛ (ňeutral-to-normal sp₂ t′)) ⟧n ]  ≡⟨ ⟦⟧n-cong $ drop-subst-⊢n id (≅-Type-⇒-≡ $ π-fst-snd-ŵk-ŝub-žero sp₁ σ) ⟩
      [ c ⟦ ňeutral-to-normal sp₂ t′ ⟧n                ]  ≡⟨ curry-cong lemma ⟩
      [ c {C = k El ˢ isnd σ} (uc ⟦ t ⟧n)              ]  ≡⟨ P.refl ⟩
      [ ⟦ t ⟧n                                         ]  ∎

-- An immediate consequence of the somewhat roundabout definition
-- above.

w̌ell-behaved :
  ∀ {Γ sp₁ sp₂ σ} (f : V̌alue Γ (π sp₁ sp₂ , σ)) →
  ∀ Γ₊ v → (⟦̌_⟧ {σ = σ} f /̂Val ŵk₊ Γ₊) ˢ ⟦̌ v ⟧ ≅-Value ⟦̌ proj₁ f Γ₊ v ⟧
w̌ell-behaved = proj₂

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

abstract

  -- Unfolding lemma for ⟦̌_∣_⟧-π.

  unfold-⟦̌∣⟧-π :
    ∀ {Γ sp₁ sp₂} σ (f : V̌alue-π Γ sp₁ sp₂ σ) →
    ⟦̌ σ ∣ f ⟧-π ≅-Value c ⟦̌ f (fst σ ◅ ε) (řeflect sp₁ (var zero)) ⟧
  unfold-⟦̌∣⟧-π σ _ = ⟦⟧n-cong $
    drop-subst-⊢n id (≅-Type-⇒-≡ $ π-fst-snd-ŵk-ŝub-žero _ σ)

-- Some congruence/conversion lemmas.

≅-⊢n-⇒-≅-Value-⋆ : ∀ {Γ₁ σ₁} {t₁ : Γ₁ ⊢ ⋆ , σ₁ ⟨ ne ⟩}
                     {Γ₂ σ₂} {t₂ : Γ₂ ⊢ ⋆ , σ₂ ⟨ ne ⟩} →
                   t₁ ≅-⊢n t₂ → t₁ ≅-V̌alue t₂
≅-⊢n-⇒-≅-Value-⋆ P.refl = P.refl

≅-⊢n-⇒-≅-Value-el : ∀ {Γ₁ σ₁} {t₁ : Γ₁ ⊢ el , σ₁ ⟨ ne ⟩}
                      {Γ₂ σ₂} {t₂ : Γ₂ ⊢ el , σ₂ ⟨ ne ⟩} →
                    t₁ ≅-⊢n t₂ → _⊢_⟨ne⟩.[_] t₁ ≅-V̌alue _⊢_⟨ne⟩.[_] t₂
≅-⊢n-⇒-≅-Value-el P.refl = P.refl

abstract

  ,-cong : P.Extensionality Level.zero Level.zero →
           ∀ {Γ sp₁ sp₂ σ} {f₁ f₂ : V̌alue Γ (π sp₁ sp₂ , σ)} →
           (∀ Γ₊ v → proj₁ f₁ Γ₊ v ≅-V̌alue proj₁ f₂ Γ₊ v) →
           _≅-V̌alue_ {σ₁ = (π sp₁ sp₂ , σ)} f₁
                     {σ₂ = (π sp₁ sp₂ , σ)} f₂
  ,-cong ext hyp = P.cong (Term-like.[_] {_} {V̌al}) $
    ,-cong′ (ext λ Γ₊ → ext λ v → Term-like.≅-⊢-⇒-≡ V̌al $ hyp Γ₊ v)
            (ext λ _  → ext λ _ → P.proof-irrelevance _ _)
    where
    ,-cong′ : {A : Set} {B : A → Set}
              {x₁ x₂ : A} {y₁ : B x₁} {y₂ : B x₂} →
              (eq : x₁ ≡ x₂) → P.subst B eq y₁ ≡ y₂ →
              _≡_ {A = Σ A B} (x₁ , y₁) (x₂ , y₂)
    ,-cong′ P.refl P.refl = P.refl

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
