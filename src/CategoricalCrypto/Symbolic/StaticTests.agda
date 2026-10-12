{-# OPTIONS --safe --without-K --guardedness #-}

module CategoricalCrypto.Symbolic.StaticTests where

open import Data.List.Base using ([]; _∷_)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.Unit using (tt)
open import Function.Bundles using (Equivalence; mk⇔)

open import CategoricalCrypto.Symbolic.Term
open import CategoricalCrypto.Symbolic.Term.PairEnc
open import CategoricalCrypto.Symbolic.Deduction Σ₀ E₀
open import CategoricalCrypto.Symbolic.Role Σ₀ using (Rcp)
open import CategoricalCrypto.Symbolic.Setup Σ₀ E₀ using (module Sym)
open import CategoricalCrypto.Symbolic.Static.Emitter Σ₀ E₀
open import CategoricalCrypto.Symbolic.Static.PairEnc

import CategoricalCrypto.Symbolic.Example.SecureChannel as Channel

open Terms Σ₀

private
  empty-kernel : Emitter {Δ = []} [] [] Sym.≈ℰ Emitter [] []
  empty-kernel = Equivalence.from ≈ℰ⇔≈ₛ λ _ _ _ → mk⇔ (λ e → e) (λ e → e)

  normalized raw : All (Rcp []) (tt ∷ tt ∷ [])
  normalized = app (cst 0) [] ∷ app (cst 1) [] ∷ []
  raw = app (cst 0) [] ∷ π₁ ⟪ app (cst 1) [] , app (cst 2) [] ⟫ ∷ []

  two-port-kernel : Emitter [] raw Sym.≈ℰ Emitter [] normalized
  two-port-kernel = Equivalence.from ≈ℰ⇔≈ₛ λ _ _ _ → mk⇔ (λ e → e) (λ e → e)

  _ : ∀ κ → frame κ [] raw ≈ₛ frame κ [] normalized
  _ = Equivalence.to ≈ℰ⇔≈ₛ two-port-kernel

  _ : ∀ κ → frame κ Channel.keys (Channel.ciphertext 1) ≈ₛ frame κ Channel.keys (Channel.ciphertext 0)
  _ = Equivalence.to ≈ℰ⇔≈ₛ (Channel.real≈simulated 1)

  _ : Channel.smt 1 Sym.≤UC Channel.ideal 1
  _ = Channel.smt≤ideal 1
