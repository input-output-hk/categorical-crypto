{-# OPTIONS --safe --guardedness #-}

module CategoricalCrypto.Machine.Relational.Presentation.ClassicalObservation where

open import Axiom.ExcludedMiddle
open import Data.Bool.Base
open import Data.Empty
open import Data.Maybe.Base
open import Data.Product.Base
open import Data.Sum.Base
open import Data.Unit.Base
open import Function.Bundles
open import Level using (0ℓ)
open import Relation.Binary.PropositionalEquality

open import ProbabilisticLogic.Dp.Positive
open import ProbabilisticLogic.Dp.Positive.Composition

import CategoricalCrypto.Channel.Core as Ch
open import CategoricalCrypto.Iface
open import CategoricalCrypto.Machine.Relational
import CategoricalCrypto.Machine.Relational.Observation as Native
import CategoricalCrypto.Machine.Relational.Presentation.Classical as Classical
import CategoricalCrypto.Machines.Positive.Repack as Re
open import CategoricalCrypto.Protocol.Machine using (runᴹFrom)
open import CategoricalCrypto.Strategy
import CategoricalCrypto.UC.Machine as UC

private module R = Re.At 0ℓ

module WithLEM (lem : ExcludedMiddle 0ℓ) where
  open Classical.WithLEM lem

  opaque
    unfolding Ch._⊗₀_ compile-step Native.tick Native.verdict

    readout-to : (f : UC.Proc unitᴵ UC.Ωᴵ) {b : Bool}
      → Positive UC.⟦ f ⟧ᴼ b → Native.eval (compile (R.repack f)) b
    readout-to f path =
      let s , init , rest = bind-unpath path
          s′ , step = finish s rest
      in s , init , s′ , step
      where
      finish : ∀ s {b} → Positive (runᴹFrom f s (ask tt out)) b
        → ∃ λ s′ → Positive (R.P.step f (s , inj₂ tt)) (s′ , inj₂ b)
      finish s p with bind-unpath p
      ... | (s′ , inj₁ ()) , path , result
      ... | (s′ , inj₂ c) , path , result =
        s′ , subst (λ b → Positive (R.P.step f (s , inj₂ tt)) (s′ , inj₂ b)) (positive-return-reflect result) path

    readout-from : (f : UC.Proc unitᴵ UC.Ωᴵ) {b : Bool}
      → Native.eval (compile (R.repack f)) b → Positive UC.⟦ f ⟧ᴼ b
    readout-from f (s , init , s′ , step) = bind-path init (bind-path step (positive-return _))

  readout : (f : UC.Proc unitᴵ UC.Ωᴵ) (b : Bool)
    → Positive UC.⟦ f ⟧ᴼ b ⇔ Native.eval (compile (R.repack f)) b
  readout f b = mk⇔ (readout-to f) (readout-from f)
