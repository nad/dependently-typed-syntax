------------------------------------------------------------------------
-- Normalisation by evaluation
------------------------------------------------------------------------

open import Level using (zero)
open import Universe

module README.DependentlyTyped.NBE5 (Uni₀ : Universe zero zero) where

import README.DependentlyTyped.Term as Term
import README.DependentlyTyped.Substitution as Substitution
import README.DependentlyTyped.NormalForm as NormalForm
open Term Uni₀
open Substitution Uni₀
open NormalForm Uni₀

open import Data.Product renaming (curry to c; uncurry to uc)
import deBruijn.Substitution; open deBruijn.Substitution Uni
open import Function hiding (id) renaming (_∘_ to _⊚_; const to k)
open import Relation.Binary.HeterogeneousEquality as H using (_≅_)
open import Relation.Binary.PropositionalEquality as P using (_≡_)

open Tm-subst

mutual

  -- Kripke-style values.

  Kripke-val : Ctxt → U → Set
  Kripke-val Γ ⋆       = Γ ⊢ k ⋆ [ ne ]
  Kripke-val Γ (el a)  = Γ ⊢ k (U.el a) [ ne ]
  Kripke-val Γ (π a b) =
    (Γ⁺ : Ctxt⁺ Γ) →
    (v : Kripke-val (Γ ++ Γ⁺) a) →
    Kripke-val (Γ ++ Γ⁺) (b (foo a v))

  foo : ∀ {Γ} a → Kripke-val Γ a → El a
  foo ⋆       t = {!⟦ ⌊ t ⌋ ⟧!}
  foo (el a)  t = {!⟦ ⌊ t ⌋ ⟧!}
  foo (π a b) f = λ v → foo (b v) {!f ε ?!}

-- mutual

--   -- Kripke-style values.

--   Kripke-val : (Γ : Ctxt) → U → Env Γ → Set
--   Kripke-val Γ ⋆       _ = Γ ⊢ k ⋆ [ ne ]
--   Kripke-val Γ (el a)  _ = Γ ⊢ k (U.el a) [ ne ]
--   Kripke-val Γ (π a b) γ =
--     (Γ⁺ : Ctxt⁺ Γ) →
--     (v : Kripke-val (Γ ++ Γ⁺) a {!!}) →
--     Kripke-val (Γ ++ Γ⁺) (b (foo a {!γ!} v)) {!!}

--   foo : ∀ {Γ} a γ → Kripke-val Γ a γ → El a
--   foo ⋆       γ t = ⟦ ⌊ t ⌋ ⟧ γ
--   foo (el a)  γ t = ⟦ ⌊ t ⌋ ⟧ γ
--   foo (π a b) γ t = λ v → {!!}
