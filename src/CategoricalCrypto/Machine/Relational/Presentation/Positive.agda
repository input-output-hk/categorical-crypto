{-# OPTIONS --safe --guardedness #-}

module CategoricalCrypto.Machine.Relational.Presentation.Positive where

open import Categories.Category.Monoidal.Bundle
open import Data.Maybe.Base using (just)
open import Data.Product.Base
open import Data.Sum.Base
open import Data.Unit.Polymorphic.Base
open import Function.Bundles
open import Level using (0ℓ)

open import ProbabilisticLogic.Dp using (Dₚ)
open import ProbabilisticLogic.Dp.Positive

open import CategoricalCrypto.Channel.Core
import CategoricalCrypto.Machine.Core as M
open import CategoricalCrypto.Machine.Relational
open import CategoricalCrypto.Machine.Relational.Presentation
open import CategoricalCrypto.Machines.Positive.Base
import CategoricalCrypto.Machines.Core as Core
import CategoricalCrypto.Iface as I
import CategoricalCrypto.Machines.Positive.Model as Model
import CategoricalCrypto.UC.Model.Seal as Seal

module Target = Core (𝒱₊ 0ℓ)

private variable A B : Channel

interface : Channel → Set × Set
interface A = Channel.inType A , Channel.outType A

-- The explicit sums keep the G-construction bundle out of conversion-sensitive
-- hom types, as for UC.Machine.Proc.
Proc : Channel → Channel → Set₁
Proc A B = Target.Machine (Channel.inType A ⊎ Channel.outType B) (Channel.outType A ⊎ Channel.inType B)

opaque
  unfolding _⊗₀_

  machine-input : {A B : Channel} → Channel.inType A ⊎ Channel.outType B → Channel.inType (A M.⊗ᵀ B)
  machine-input i = i

  machine-output : {A B : Channel} → Channel.outType A ⊎ Channel.inType B → Channel.outType (A M.⊗ᵀ B)
  machine-output o = o

  positive-step : {R : Initialized A B} → Presentation R
    → M.Machine.State (machine R) × (Channel.inType A ⊎ Channel.outType B)
    → Dₚ (M.Machine.State (machine R) × (Channel.outType A ⊎ Channel.inType B))
  positive-step P (s , i) = stepₚ P s i

toPositive : {R : Initialized A B} → Presentation R → Proc A B
toPositive {R = R} P = Target.mk
  (record { obj = M.Machine.State (machine R) ; point = λ _ → initialₚ P })
  (positive-step P)

initial-agreement : {R : Initialized A B} (P : Presentation R) (s : M.Machine.State (machine R))
  → Positive (Target.point (Target.state (toPositive P)) tt) s ⇔ initial R s
initial-agreement P s = mk⇔ (initial-sound P) (initial-complete P)

opaque
  unfolding _⊗₀_ machine-input machine-output positive-step

  step-agreement : {R : Initialized A B} (P : Presentation R)
    (s s′ : M.Machine.State (machine R)) (i : Channel.inType A ⊎ Channel.outType B)
    (o : Channel.outType A ⊎ Channel.inType B)
    → Positive (Target.step (toPositive P) (s , i)) (s′ , o)
      ⇔ M.Machine.stepRel (machine R) s (machine-input {A} {B} i) (just (machine-output {A} {B} o)) s′
  step-agreement P s s′ i o = mk⇔ (step-sound P) (step-complete P)

private module Quotient = MonoidalCategory Model.𝔾₊

target-interface : Channel → Quotient.Obj
target-interface A = Seal.ifaceᵒ (Channel.inType A I.⇿ Channel.outType A)

toQuotient : {R : Initialized A B} → Presentation R → target-interface A Quotient.⇒ target-interface B
toQuotient {A} {B} P = Model.pack-positive
  {Channel.inType A I.⇿ Channel.outType A} {Channel.inType B I.⇿ Channel.outType B} (toPositive P)
