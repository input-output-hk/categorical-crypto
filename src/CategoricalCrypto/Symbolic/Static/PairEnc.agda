{-# OPTIONS --safe --without-K --guardedness #-}

-- Static equivalence characterizes frame-emitter observations at E₀.
-- The multi-sorted converse is not established; see docs/uc-setup-symbolic.md §3.7.

module CategoricalCrypto.Symbolic.Static.PairEnc where

open import Data.List.Base using (List)
open import Data.List.Relation.Unary.All
open import Data.Unit using (⊤; tt)
open import Function.Bundles using (_⇔_; mk⇔)

open import CategoricalCrypto.Symbolic.Term
open import CategoricalCrypto.Symbolic.Term.PairEnc
open import CategoricalCrypto.Symbolic.Deduction Σ₀ E₀
open import CategoricalCrypto.Symbolic.Role Σ₀ using (Rcp)
open import CategoricalCrypto.Symbolic.Setup Σ₀ E₀ using (module Sym)
open import CategoricalCrypto.Symbolic.Static Σ₀ E₀ using (≈ₛ⇒≈ℰ)
open import CategoricalCrypto.Symbolic.Static.Distinguish using (≈ℰ⇒≈ₛ)
open import CategoricalCrypto.Symbolic.Static.Emitter Σ₀ E₀ using (Emitter; frame)

open Terms Σ₀
open EqTheory E₀

sort-blind : SortBlind
sort-blind = renˢ-cong

≈ℰ⇔≈ₛ : {Δ Ν : List ⊤} {ζs ζs′ : All (Rcp Ν) Δ}
      → (Emitter Ν ζs Sym.≈ℰ Emitter Ν ζs′) ⇔ (∀ κ → frame κ Ν ζs ≈ₛ frame κ Ν ζs′)
≈ℰ⇔≈ₛ = mk⇔ ≈ℰ⇒≈ₛ ≈ₛ⇒≈ℰ
