{-# OPTIONS --safe --guardedness #-}

-- Every successful native preparation/test interaction has a finite scripted
-- PM preparation.  Replaying that script is only a forward simulation: the
-- target preparation need not be probabilistically representable.
module CategoricalCrypto.Machine.Relational.Presentation.ClassicalTests where

open import Axiom.ExcludedMiddle
open import Categories.Category.Monoidal.Bundle
open import Categories.Functor using (Functor)
open import Data.Bool.Base
open import Data.List.Base
open import Data.Product.Base
open import Function.Bundles
open import Level using (0ℓ)
open import Relation.Binary.Bundles using (Setoid)

open import ProbabilisticLogic.Dp.Positive
open import ProbabilisticLogic.Dp.Positive.Monad

open import CategoricalCrypto.Iface
open import CategoricalCrypto.Machine.Relational
import CategoricalCrypto.Machine.Relational.Observation as Native
import CategoricalCrypto.Machine.Relational.Wiring as W
import CategoricalCrypto.Machine.Relational.Presentation.Classical as Classical
import CategoricalCrypto.Machine.Relational.Presentation.ClassicalExtraction as Extraction
import CategoricalCrypto.Machine.Relational.Presentation.ClassicalObservation as Readout
import CategoricalCrypto.Machine.Relational.Presentation.ClassicalScript as Script
import CategoricalCrypto.Machine.Relational.Simulation as Sim
import CategoricalCrypto.Machine.Relational.Presentation.ClassicalWiring as Wiring
open import CategoricalCrypto.Machine.Relational.Presentation.Canonical
open import CategoricalCrypto.Machine.Relational.Presentation.Descent using (channel)
import CategoricalCrypto.Machine.Relational.Presentation.Positive as EP
import CategoricalCrypto.Machines.Positive.Model as Model
import CategoricalCrypto.Machines.Positive.Raw as Raw
import CategoricalCrypto.Machines.Positive.Repack as Re
import CategoricalCrypto.Machines.Positive.Setup as Source
import CategoricalCrypto.UC.Machine as UC
import CategoricalCrypto.UC.Model.Observation as Observation
import CategoricalCrypto.UC.Model.Seal as Seal

private
  module R = Re.At 0ℓ
  module G = Raw.At 0ℓ
  module Q = MonoidalCategory Model.𝔾₊
  variable A : Iface

module WithLEM (lem : ExcludedMiddle 0ℓ) where
  open Classical.WithLEM lem
  open Wiring.WithLEM lem
  open Readout.WithLEM lem

  opaque
    unfolding Seal.𝔾ᵒ Seal.procᵒ Seal.unprocᵒ Seal.ifaceᵒ

    source-square : (t : UC.Proc A UC.Ωᴵ) (m : EP.Proc Native.J (channel A))
      → UC.⟦ R.unpack (G.compose₊ (R.repack t) m) ⟧ᴼ ≈₊
          Observation.Obs (Seal.procᵒ t Q.∘ Model.pack-positive {unitᴵ} {A} m)
    source-square {A} t m = Source.observation-resp
      (Q.Equiv.trans (Model.pack-positive-resp {unitᴵ} {UC.Ωᴵ} (G.compose₊-project (R.repack t) m))
        (Model.pack-positive-compose {unitᴵ} {A} {UC.Ωᴵ} (R.repack t) m))

  tests-to : {t u : UC.Proc A UC.Ωᴵ}
    → Setoid._≈_ (Functor.F₀ Source.ℰ₊ (Seal.ifaceᵒ A)) (Seal.procᵒ t) (Seal.procᵒ u)
    → (m : Initialized Native.J (channel A)) → ∀ {b}
    → Native.eval (compile (R.repack t) W.∘ m) b
    → Native.eval (compile (R.repack u) W.∘ m) b
  tests-to {A} {t} {u} eq m {b} ((s , q) , (im , it) , (s′ , q′) , path) =
    let xs , follows , extracted = Extraction.extract lem m (compile (R.repack t)) path
        pm = S.process lem xs
        script-correct = presentation (presentₚ _ (S.step lem))
        scripted = (xs , q) , (positive-return xs , it) , ([] , q′) , extracted
        compiled = Native.eval-to (W.∘-cong ≈ᴿ-refl (≈ᴿ-sym script-correct)) scripted
        closed = Native.eval-to (≈ᴿ-sym (compose (R.repack t) pm)) compiled
        pos = readout-from (R.unpack (G.compose₊ (R.repack t) pm)) closed
        observed = positive-support (source-square t pm) pos
        transferred = positive-support (eq (Model.pack-positive {unitᴵ} {A} pm)) observed
        pos′ = positive-support (≈₊-sym (source-square u pm)) transferred
        closed′ = readout-to (R.unpack (G.compose₊ (R.repack u) pm)) pos′
        compiled′ = Native.eval-to (compose (R.repack u) pm) closed′
        scripted′ = Native.eval-to (W.∘-cong ≈ᴿ-refl script-correct) compiled′
    in Sim.forward (Sim.compose Sim.reflexive (S.replay lem im follows)) scripted′
    where module S = Script.At {Native.J} {channel A}

  tests-cong : {t u : UC.Proc A UC.Ωᴵ}
    → Setoid._≈_ (Functor.F₀ Source.ℰ₊ (Seal.ifaceᵒ A)) (Seal.procᵒ t) (Seal.procᵒ u)
    → (m : Initialized Native.J (channel A)) → ∀ b
    → Native.eval (compile (R.repack t) W.∘ m) b ⇔ Native.eval (compile (R.repack u) W.∘ m) b
  tests-cong {A} eq m b = mk⇔ (tests-to eq m)
    (tests-to (Setoid.sym (Functor.F₀ Source.ℰ₊ (Seal.ifaceᵒ A)) eq) m)
