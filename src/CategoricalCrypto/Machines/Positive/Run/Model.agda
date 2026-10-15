{-# OPTIONS --safe --without-K --guardedness #-}

-- Adaptive finite experiments on actual public target arrows.  The returned
-- computation is observed in the positive setoid, not by its probability
-- magnitudes or the private representative's state predicates.
module CategoricalCrypto.Machines.Positive.Run.Model where

open import Categories.Category.Monoidal.Bundle
open import Data.Sum.Base
open import Level
open import ProbabilisticLogic.Dp
open import ProbabilisticLogic.Dp.Positive.Monad
open import CategoricalCrypto.Iface
open import CategoricalCrypto.Strategy
import CategoricalCrypto.UC.Model.Seal as Seal
import CategoricalCrypto.Machines.Positive.Model as Model
import CategoricalCrypto.Machines.Positive.Run as Run
import CategoricalCrypto.Machines.Positive.Repack as Re
open import Data.Bool.Base using (Bool)

private
  module T = MonoidalCategory Model.𝔾₊
  module R = Re.At 0ℓ

run : {A B : Iface} → Seal.ifaceᵒ A T.⇒ Seal.ifaceᵒ B
    → Strat (Pos A ⊎ Neg B) (Neg A ⊎ Pos B) → Dₚ Bool
run f d = Run.run (R.repack (Seal.unprocᵒ f)) d

opaque
  unfolding Seal.𝔾ᵒ Seal.ifaceᵒ Seal.procᵒ Seal.unprocᵒ Model.positive-congruence Model._≈⁺_

  run-resp : {A B : Iface} {f g : Seal.ifaceᵒ A T.⇒ Seal.ifaceᵒ B}
    → f T.≈ g → (d : Strat (Pos A ⊎ Neg B) (Neg A ⊎ Pos B)) → run f d ≈₊ run g d
  run-resp eq d = Run.run-resp eq d

  pack-run : {A B : Iface} (f : R.Q.Machine (Pos A ⊎ Neg B) (Neg A ⊎ Pos B))
    (d : Strat (Pos A ⊎ Neg B) (Neg A ⊎ Pos B))
    → run (Model.pack-positive {A} {B} f) d ≈₊ Run.run f d
  pack-run f d = Run.run-resp (R.repack-unpack f) d
