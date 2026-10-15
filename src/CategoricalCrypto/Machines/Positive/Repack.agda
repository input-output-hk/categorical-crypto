{-# OPTIONS --safe --without-K --guardedness #-}

module CategoricalCrypto.Machines.Positive.Repack where

open import Categories.Category.Monoidal.Bundle
open import Data.Product.Base
open import Data.Sum.Base using (_⊎_)
open import Level
import Relation.Binary.Construct.Closure.Equivalence as EqC

open import ProbabilisticLogic.Dp.Positive.Monad
import CategoricalCrypto.Machines.Base as PM
import CategoricalCrypto.Machines.Core as Core
import CategoricalCrypto.Machines.Sim as Sim
import CategoricalCrypto.Machines.Tensor as Tensor
import CategoricalCrypto.Machines.Trace as Trace
import CategoricalCrypto.Machines.Trace.Congruence as TraceCong
import CategoricalCrypto.Machines.Positive.Base as Positive

module At (ℓ : Level) where
  module P = Core (PM.𝒱ₚ ℓ)
  module Q = Core (Positive.𝒱₊ ℓ)
  module PS = Sim (PM.𝒱ₚ ℓ) (PM.𝒫ₚ ℓ)
  module QS = Sim (Positive.𝒱₊ ℓ) (Positive.𝒫₊ ℓ)
  module PT = Tensor (PM.𝒱ₚ ℓ) (PM.distₚ ℓ) (PM.𝒫ₚ ℓ)
  module QT = Tensor (Positive.𝒱₊ ℓ) (Positive.dist₊ ℓ) (Positive.𝒫₊ ℓ)
  module PTr = Trace (PM.𝒱ₚ ℓ) (PM.distₚ ℓ) (PM.𝒫ₚ ℓ) (PM.Elgotₚ ℓ)
  module QTr = Trace (Positive.𝒱₊ ℓ) (Positive.dist₊ ℓ) (Positive.𝒫₊ ℓ) (Positive.Elgot₊ ℓ)
  module QTC = TraceCong (Positive.𝒱₊ ℓ) (Positive.dist₊ ℓ) (Positive.𝒫₊ ℓ) (Positive.Elgot₊ ℓ)
  module PMM = SymmetricMonoidalCategory (PM.ℳₚ ℓ)
  module QMM = SymmetricMonoidalCategory (Positive.ℳ₊ ℓ)

  private variable A B C D X : Set ℓ

  repack : P.Machine A B → Q.Machine A B
  repack f = Q.mk (record { obj = P.St f ; point = P.point (P.state f) }) (P.step f)

  unpack : Q.Machine A B → P.Machine A B
  unpack f = P.mk (record { obj = Q.St f ; point = Q.point (Q.state f) }) (Q.step f)

  repack-sim : {f g : P.Machine A B} → f PS.≲ g → repack f QS.≲ repack g
  repack-sim φ = record
    { θ = PS.θ φ
    ; θ-pure = let fn , eq = PS.θ-pure φ in fn , λ x → ≈ₚ⇒≈₊ (eq x)
    ; θ-point = λ x → ≈ₚ⇒≈₊ (PS.θ-point φ x)
    ; θ-step = λ x → ≈ₚ⇒≈₊ (PS.θ-step φ x)
    }

  repack-resp : {f g : P.Machine A B} → f PS.≈ᴹ g → repack f QS.≈ᴹ repack g
  repack-resp = EqC.gmap repack repack-sim

  repack-unpack : (f : Q.Machine A B) → repack (unpack f) QS.≈ᴹ f
  repack-unpack f = QS.reflᴹ

  opaque
    unfolding P._∘ᴹ_ Q._∘ᴹ_

    repack-mealy-compose : (g : P.Machine B C) (f : P.Machine A B)
      → repack (g P.∘ᴹ f) QS.≈ᴹ (repack g Q.∘ᴹ repack f)
    repack-mealy-compose g f = QS.reflᴹ

  repack-mealy-tensor : (f : P.Machine A B) (g : P.Machine C D)
    → repack (f PT.⊗ᵉ g) QS.≈ᴹ (repack f QT.⊗ᵉ repack g)
  repack-mealy-tensor f g = QS.reflᴹ

  repack-trace : (f : P.Machine (A ⊎ X) (B ⊎ X))
    → repack (PTr.traceᴹ A B X f) QS.≈ᴹ QTr.traceᴹ A B X (repack f)
  repack-trace f = QS.reflᴹ

  mapped-compose : {g : P.Machine B C} {f : P.Machine A B}
    {g′ : Q.Machine B C} {f′ : Q.Machine A B}
    → repack g QS.≈ᴹ g′ → repack f QS.≈ᴹ f′ → repack (g P.∘ᴹ f) QS.≈ᴹ (g′ Q.∘ᴹ f′)
  mapped-compose {g = g} {f} p q = QS._○ᴹ_ (repack-mealy-compose g f) (QMM.∘-resp-≈ p q)

  mapped-tensor : {f : P.Machine A B} {g : P.Machine C D}
    {f′ : Q.Machine A B} {g′ : Q.Machine C D}
    → repack f QS.≈ᴹ f′ → repack g QS.≈ᴹ g′ → repack (f PT.⊗ᵉ g) QS.≈ᴹ (f′ QT.⊗ᵉ g′)
  mapped-tensor {f = f} {g} p q = QS._○ᴹ_ (repack-mealy-tensor f g) (QT.⊗ᵉ-resp-≈ᴹ p q)
