------------------------------------------------------------------------
-- Substitutions
------------------------------------------------------------------------

{-# OPTIONS --universe-polymorphism #-}

-- Uses a variant of Conor McBride's technique from "Type-Preserving
-- Renaming and Substitution".

-- TODO: See MMM for an example of how this module can be used: a
-- definition of substitution for the untyped λ-calculus.

open import Universe

module deBruijn.Substitution.Data {u e} {Uni : Universe u e} where

import deBruijn.Context as Context
import deBruijn.TermLike as TermLike
open import Function as F using (_$_)
open import Level using (_⊔_)
import Relation.Binary.PropositionalEquality as P

open Context Uni
open P.≡-Reasoning
open TermLike Uni

-- This module reexports some other modules.

open import deBruijn.Substitution.Data.Application public
open import deBruijn.Substitution.Data.Basics      public
open import deBruijn.Substitution.Data.Map         public
open import deBruijn.Substitution.Data.Simple      public

------------------------------------------------------------------------
-- Instantiations and code for facilitating instantiations

-- Renamings (variable substitutions).

module Renaming where

  -- Variables support all of the operations above.

  simple : Simple Var
  simple = record
    { weaken     = weaken∋
    ; var        = [id]
    ; weaken-var = λ _ → P.refl
    }

  application : Application Var Var
  application = record { app = app∋ }

  application₁ : Application₁ Var
  application₁ = record
    { simple        = simple
    ; application₂₂ = record
      { application₂₁ = record
        { application  = application
        ; trans-weaken = λ _ → P.refl
        ; trans-var    = λ _ → P.refl
        ; var-/⊢       = λ _ _ → P.refl
        }
      ; var-/⊢⋆-↑⁺⋆-⇒-/⊢⋆-↑⁺⋆ = λ _ _ hyp → hyp
      ; /⊢-wk                 = Simple./∋-wk simple
      }
    }

  open Application₁ application₁ public hiding (simple; application)

-- A translation of T₁'s to T₂'s, plus a bit more.

record _↦_ {t₁} (T₁ : Term-like t₁)
           {t₂} (T₂ : Term-like t₂) : Set (u ⊔ e ⊔ t₁ ⊔ t₂) where
  field
    -- Translates T₁'s to T₂'s.
    trans : [ T₁ ⟶⁼ T₂ ]

    -- Simple substitutions for T₁'s.
    simple : Simple T₁

  open Simple simple public

-- "Term" substitutions.

-- For simplicity I have chosen to use the universe level (u ⊔ e)
-- here; this is the level of Var. The code could perhaps be made more
-- general.

record Substitution₁ (T : Term-like (u ⊔ e))
                     : Set (Level.suc (u ⊔ e)) where

  open Term-like T

  field
    -- Takes variables to terms.
    var : [ Var ⟶⁼ T ]

    -- Applies substitutions, which contain things which can be
    -- translated to terms, to terms.
    app : {T′ : Term-like (u ⊔ e)} → T′ ↦ T →
          ∀ {Γ Δ} {ρ̂ : Γ ⇨̂ Δ} → Sub T′ ρ̂ → [ T ⟶ T ] ρ̂

    -- A property relating app and var.
    app-var :
      ∀ {T′ : Term-like (u ⊔ e)} {Γ Δ σ} {ρ̂ : Γ ⇨̂ Δ}
      (T′↦T : T′ ↦ T) (x : Γ ∋ σ) (ρ : Sub T′ ρ̂) →
      app T′↦T ρ · (var · x) ≅-⊢ _↦_.trans T′↦T · (x /∋ ρ)

  -- Variables can be translated into terms.

  private

    Var-↦′ : Var ↦ T
    Var-↦′ = record
      { trans  = var
      ; simple = Renaming.simple
      }

  -- Renamings can be applied to terms.

  app-renaming : ∀ {Γ Δ} {ρ̂ : Γ ⇨̂ Δ} → Sub Var ρ̂ → [ T ⟶ T ] ρ̂
  app-renaming = app Var-↦′

  -- This gives us a way to define the weakening operation.

  simple : Simple T
  simple = record
    { weaken     = app-renaming Renaming.wk
    ; var        = var
    ; weaken-var = weaken-var
    }
    where
    abstract
      weaken-var : ∀ {Γ σ τ} (x : Γ ∋ τ) →
                   app-renaming (Renaming.wk[_] σ) · (var · x) ≅-⊢
                   var · suc[ σ ] x
      weaken-var x = begin
        [ app-renaming Renaming.wk · (var · x) ]  ≡⟨ app-var Var-↦′ x Renaming.wk ⟩
        [ var · (x /∋ Renaming.wk)             ]  ≡⟨ ·-cong (P.refl {x = [ var ]}) (Renaming./∋-wk x) ⟩
        [ var · suc x                          ]  ∎

  -- A translation of T′'s to T's, plus a bit more.

  record Translation-from (T′ : Term-like (u ⊔ e)) : Set (u ⊔ e) where

    field
      translation : T′ ↦ T

    open _↦_ translation
      using (trans)
      renaming (simple to simple′; var to var′; weaken[_] to weaken′[_])

    field
      trans-weaken : ∀ {Γ σ τ} (t : Term-like._⊢_ T′ Γ τ) →
                     trans · (weaken′[ σ ] · t) ≅-⊢
                     Simple.weaken[_] simple σ · (trans · t)
      trans-var    : ∀ {Γ σ} (x : Γ ∋ σ) →
                     trans · (var′ · x) ≅-⊢ var · x

    -- An Application₂₁ record.

    application₂₁ : Application₂₁ simple′ simple trans
    application₂₁ = record
      { application  = record { app = app translation }
      ; trans-weaken = trans-weaken
      ; trans-var    = trans-var
      ; var-/⊢       = app-var translation
      }

    open _↦_ translation public
    open Application₂₁ application₂₁ public
      hiding (trans-weaken; trans-var)

  -- Variables can be translated into terms.

  Var-↦ : Translation-from Var
  Var-↦ = record
    { translation  = Var-↦′
    ; trans-weaken = trans-weaken
    ; trans-var    = λ _ → P.refl
    }
    where
    abstract
      trans-weaken :
        ∀ {Γ σ τ} (x : Γ ∋ τ) →
        var · suc[ σ ] x ≅-⊢
        Simple.weaken[_] simple σ · (var · x)
      trans-weaken x = P.sym $ Simple.weaken-var simple x

record Substitution₂ (T : Term-like (u ⊔ e))
                     : Set (Level.suc (u ⊔ e)) where

  open Term-like T

  field
    substitution₁ : Substitution₁ T

  open Substitution₁ substitution₁

  field
    -- Lifts equalities valid for all variables and liftings to
    -- arbitrary terms.
    var-/⊢⋆-↑⁺⋆-⇒-/⊢⋆-↑⁺⋆ :
      {T₁ T₂ : Term-like (u ⊔ e)}
      (T₁↦T : Translation-from T₁) (T₂↦T : Translation-from T₂) →

      let open Translation-from T₁↦T
            using () renaming (_↑⁺⋆_ to _↑⁺⋆₁_; _/⊢⋆_ to _/⊢⋆₁_)
          open Translation-from T₂↦T
            using () renaming (_↑⁺⋆_ to _↑⁺⋆₂_; _/⊢⋆_ to _/⊢⋆₂_) in

      ∀ {Γ Δ} {ρ̂ : Γ ⇨̂ Δ} (ρs₁ : Subs T₁ ρ̂) (ρs₂ : Subs T₂ ρ̂) →
      (∀ Γ⁺ {σ} (x : Γ ++ Γ⁺ ∋ σ) →
         var · x /⊢⋆₁ ρs₁ ↑⁺⋆₁ Γ⁺ ≅-⊢ var · x /⊢⋆₂ ρs₂ ↑⁺⋆₂ Γ⁺) →
      ∀ Γ⁺ {σ} (t : Γ ++ Γ⁺ ⊢ σ) →
      t /⊢⋆₁ ρs₁ ↑⁺⋆₁ Γ⁺ ≅-⊢ t /⊢⋆₂ ρs₂ ↑⁺⋆₂ Γ⁺

  -- Given a well-behaved translation from something with simple
  -- substitutions one can define an Application₂₂ record.

  application₂₂ :
    {T′ : Term-like (u ⊔ e)} (T′↦T : Translation-from T′) →
    let open Translation-from T′↦T
          using (trans) renaming (simple to simple′) in
    Application₂₂ simple′ simple trans
  application₂₂ T′↦T = record
    { application₂₁         = Translation-from.application₂₁ T′↦T
    ; var-/⊢⋆-↑⁺⋆-⇒-/⊢⋆-↑⁺⋆ = var-/⊢⋆-↑⁺⋆-⇒-/⊢⋆-↑⁺⋆ T′↦T T′↦T
    ; /⊢-wk                 = /⊢-wk
    }
    where
    open Translation-from T′↦T
      using ()
      renaming ( _↑⁺_ to _↑⁺′_; _↑⁺⋆_ to _↑⁺⋆′_
               ; wk to wk′; wk[_] to wk′[_]
               ; _/⊢_ to _/⊢′_; _/⊢⋆_ to _/⊢⋆′_
               )
    open Translation-from Var-↦
      using ()
      renaming ( _↑⁺_ to _↑⁺-renaming_; _↑⁺⋆_ to _↑⁺⋆-renaming_
               ; _/⊢_ to _/⊢-renaming_; _/⊢⋆_ to _/⊢⋆-renaming_
               )

    abstract
      /⊢-wk : ∀ {Γ σ τ} (t : Γ ⊢ τ) →
              t /⊢′ wk′[ σ ] ≅-⊢ t /⊢-renaming Renaming.wk[_] σ
      /⊢-wk =
        var-/⊢⋆-↑⁺⋆-⇒-/⊢⋆-↑⁺⋆ T′↦T Var-↦ (ε ▻ wk′) (ε ▻ Renaming.wk)
          (λ Γ⁺ x → begin
             [ var · x /⊢⋆′ (ε ▻ wk′) ↑⁺⋆′ Γ⁺                         ]  ≡⟨ Translation-from./⊢⋆-ε-▻-↑⁺⋆ T′↦T Γ⁺ (var · x) wk′ ⟩
             [ var · x /⊢′ wk′ ↑⁺′ Γ⁺                                 ]  ≡⟨ Translation-from.var-/⊢-wk-↑⁺ T′↦T Γ⁺ x ⟩
             [ var · (lift weaken∋ Γ⁺ · x)                            ]  ≡⟨ P.sym $ Translation-from.var-/⊢-wk-↑⁺ Var-↦ Γ⁺ x ⟩
             [ var · x /⊢-renaming Renaming.wk ↑⁺-renaming Γ⁺         ]  ≡⟨ P.sym $ Translation-from./⊢⋆-ε-▻-↑⁺⋆
                                                                                      Var-↦ Γ⁺ (var · x) Renaming.wk ⟩
             [ var · x /⊢⋆-renaming (ε ▻ Renaming.wk) ↑⁺⋆-renaming Γ⁺ ]  ∎)
          ε

  -- An Application₂₂ record for renamings.

  application₂₂-renaming : Application₂₂ Renaming.simple simple var
  application₂₂-renaming = application₂₂ Var-↦

  -- We can apply substitutions to terms.

  application₁ : Application₁ T
  application₁ = record
    { simple        = simple
    ; application₂₂ = application₂₂ (record
        { translation  = record { trans = [id]; simple = simple }
        ; trans-weaken = λ _ → P.refl
        ; trans-var    = λ _ → P.refl
        })
    }

  open Application₁ application₁ public
    hiding (var; simple; application₂₂; app; var-/⊢⋆-↑⁺⋆-⇒-/⊢⋆-↑⁺⋆)
  open Substitution₁ substitution₁ public
