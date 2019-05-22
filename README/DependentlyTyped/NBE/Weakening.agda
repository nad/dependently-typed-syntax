------------------------------------------------------------------------
-- Weakening for the NBE values
------------------------------------------------------------------------

import Axiom.Extensionality.Propositional as E
import Level
open import Universe

-- The code makes use of the assumption that propositional equality of
-- functions is extensional.

module README.DependentlyTyped.NBE.Weakening
  (Uni₀ : Universe Level.zero Level.zero)
  (ext : E.Extensionality Level.zero Level.zero)
  where

open import Data.Product renaming (curry to c)
open import deBruijn.Substitution.Data
open import Function hiding (_∋_)
import README.DependentlyTyped.NBE.Value as Value
open Value Uni₀ renaming ([_] to [̌_])
import README.DependentlyTyped.NormalForm as NF
open NF Uni₀ renaming ([_] to [_]n)
import README.DependentlyTyped.NormalForm.Substitution as NFS
open NFS Uni₀
import README.DependentlyTyped.Term as Term; open Term Uni₀
import Relation.Binary.PropositionalEquality as P

open P.≡-Reasoning

mutual

  -- Weakening.

  w̌k[_] : ∀ {Γ} σ τ → V̌alue Γ τ → V̌alue (Γ ▻ σ) (τ /̂ ŵk)
  w̌k[ _ ] (⋆     , τ) t       =   t /⊢n Renaming.wk
  w̌k[ _ ] (el    , τ) [ t ]el = [ t /⊢n Renaming.wk ]el
  w̌k[ σ ] (π _ _ , τ) f       =
    (λ Γ₊ → proj₁ f (σ ◅ Γ₊)) , w̌k-π-well-behaved τ f

  w̌k : ∀ {Γ σ} τ → V̌alue Γ τ → V̌alue (Γ ▻ σ) (τ /̂ ŵk)
  w̌k τ v = w̌k[ _ ] τ v

  abstract

    -- The Π case of weakening is well-behaved.

    w̌k-π-well-behaved :
      ∀ {Γ σ sp₁ sp₂} τ (f : V̌alue Γ (π sp₁ sp₂ , τ)) →
      W̌ell-behaved sp₁ sp₂ (τ /̂I ŵk) (λ Γ₊ → proj₁ f (σ ◅ Γ₊))
    w̌k-π-well-behaved {σ = σ} τ f Γ₊ v =
      let lemma = begin
            [ ⟦̌ τ /̂I ŵk ∣ (λ Γ₊ → proj₁ f (σ ◅ Γ₊)) ⟧-π /̂Val ŵk₊ Γ₊ ]  ≡⟨ /̂Val-cong (P.sym $ w̌eaken-corresponds-π τ f) P.refl ⟩
            [ ⟦̌_⟧ {σ = τ} f /̂Val ŵk[ σ ] /̂Val ŵk₊ Γ₊                ]  ≡⟨ P.refl ⟩
            [ ⟦̌ τ ∣ proj₁ f ⟧-π /̂Val ŵk₊ (σ ◅ Γ₊)                   ]  ∎

      in begin
      [ (⟦̌ τ /̂I ŵk ∣ (λ Γ₊ → proj₁ f (σ ◅ Γ₊)) ⟧-π /̂Val ŵk₊      Γ₊ ) ˢ ⟦̌ v ⟧ ]  ≡⟨ ˢ-cong lemma P.refl ⟩
      [ (⟦̌ τ       ∣         proj₁ f           ⟧-π /̂Val ŵk₊ (σ ◅ Γ₊)) ˢ ⟦̌ v ⟧ ]  ≡⟨ proj₂ f (σ ◅ Γ₊) v ⟩
      [ ⟦̌ proj₁ f (σ ◅ Γ₊) v ⟧                                                ]  ∎

    -- The Π case of weakening weakens.

    w̌eaken-corresponds-π :
      ∀ {Γ σ sp₁ sp₂} τ (f : V̌alue Γ (π sp₁ sp₂ , τ)) →
        ⟦̌_⟧ {σ = τ} f /̂Val ŵk[ σ ] ≅-Value
        ⟦̌ τ /̂I ŵk ∣ (λ Γ₊ → proj₁ f (σ ◅ Γ₊)) ⟧-π
    w̌eaken-corresponds-π {σ = σ} τ f =
      let f̌ = ⟦̌_⟧ {σ = τ} f

      in begin
      [ f̌ /̂Val ŵk[ σ ]                                            ]  ≡⟨ P.refl ⟩
      [ c ((f̌ /̂Val ŵk₊ (σ ◅ fst τ /̂ ŵk ◅ ε)) ˢ lookup zero)       ]  ≡⟨ curry-cong $
                                                                          ˢ-cong (P.refl {x = [ f̌ /̂Val ŵk₊ (σ ◅ fst τ /̂ ŵk ◅ ε) ]})
                                                                                 (P.sym $ ňeutral-to-normal-identity _ _) ⟩
      [ c ((f̌ /̂Val ŵk₊ (σ ◅ fst τ /̂ ŵk ◅ ε)) ˢ ⟦ žero _ _ ⟧n)     ]  ≡⟨ curry-cong $ proj₂ f (σ ◅ fst τ /̂ ŵk ◅ ε) _ ⟩
      [ c ⟦̌ proj₁ f (σ ◅ fst τ /̂ ŵk ◅ ε) (řeflect _ (var zero)) ⟧ ]  ≡⟨ P.sym $ unfold-⟦̌∣⟧-π (τ /̂I ŵk) (λ Γ₊ → proj₁ f (σ ◅ Γ₊)) ⟩
      [ ⟦̌ τ /̂I ŵk ∣ (λ Γ₊ → proj₁ f (σ ◅ Γ₊)) ⟧-π                 ]  ∎

-- Weakening.

w̌eaken : ∀ {Γ} {σ : Type Γ} → [ V̌al ⟶ V̌al ] ŵk[ σ ]
w̌eaken = record
  { function    = w̌k
  ; corresponds = corr
  }
  where
  abstract

    -- Weakening weakens.

    corr : ∀ {Γ σ} τ (v : V̌alue Γ τ) →
           ⟦̌ v ⟧ /̂Val ŵk[ σ ] ≅-Value ⟦̌ w̌k[ σ ] τ v ⟧
    corr (⋆         , τ) t       = t /⊢n-lemma Renaming.wk
    corr (el        , τ) [ t ]el = t /⊢n-lemma Renaming.wk
    corr (π sp₁ sp₂ , τ) f       = w̌eaken-corresponds-π τ f

-- Variables can be turned into values.

v̌ar : [ Var ⟶⁼ V̌al ]
v̌ar = record
  { function    = λ _ x → řeflect _ (var x)
  ; corresponds = λ _ x → P.sym $ ňeutral-to-normal-identity _ (var x)
  }

-- Values can be turned into terms.
--
-- This definition uses the assumption that propositional equality of
-- functions is extensional. I don't know how much work is required to
-- avoid this assumption, or if it is even possible to do so.

V̌al↦Tm : V̌al ↦ Tm
V̌al↦Tm = record
  { trans = record
    { function    = λ _ v → ⌊ řeify _ v ⌋
    ; corresponds = λ _ _ → P.refl
    }
  ; simple = record
    { weaken     = w̌eaken
    ; var        = v̌ar
    ; weaken-var = w̌eaken-v̌ar _
    }
  }
  where
  open Renaming hiding (var)

  abstract
    w̌eaken-v̌ar : ∀ {Γ σ} τ (x : Γ ∋ τ) →
                 w̌k[ σ ] τ (v̌ar ⊙ x) ≅-V̌alue v̌ar ⊙ suc[ σ ] x
    w̌eaken-v̌ar (⋆ , τ) x = begin
      [̌ var (x /∋ wk) ]  ≡⟨ ≅-⊢n-⇒-≅-Value-⋆ $ var-n-cong $ ≅-⊢-⇒-≅-∋ $ /∋-wk x ⟩
      [̌ var (suc x)   ]  ∎
    w̌eaken-v̌ar (el , τ) x =  begin
      [̌ [ var (x /∋ wk) ]el ]  ≡⟨ ≅-⊢n-⇒-≅-Value-el $ var-n-cong $ ≅-⊢-⇒-≅-∋ $ /∋-wk x ⟩
      [̌ [ var (suc x)   ]el ]  ∎
    w̌eaken-v̌ar {σ = σ} (π _ _ , τ) x = ,-cong ext λ Γ₊ v → begin
      [̌ řeflect _ ((var x /⊢n wk₊ (σ ◅ Γ₊)) · řeify _ v) ]  ≡⟨ řeflect-cong $
                                                                 ·n-cong (var-n-cong $ ≅-⊢-⇒-≅-∋ $ /∋-wk₊-◅ x Γ₊)
                                                                         (P.refl {x = [ řeify _ v ]n}) ⟩
      [̌ řeflect _ ((var (suc x) /⊢n wk₊ Γ₊) · řeify _ v) ]  ∎

module V̌al-subst = _↦_ V̌al↦Tm
