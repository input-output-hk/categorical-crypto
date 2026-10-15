{-# OPTIONS --safe --without-K --guardedness #-}

module CategoricalCrypto.Machines.Positive.Setup where

open import Categories.Category.Monoidal.Bundle
open import Categories.Category.Instance.Setoids
open import Categories.Functor.Monoidal
open import Categories.Functor.Presheaf
open import Categories.Functor.Presheaf.Morphism
open import Categories.NaturalTransformation using (ntHelper)
import Categories.Morphism as Mor

open import Data.Bool.Base
open import Data.Empty
open import Data.Product.Base
open import Data.Sum.Base
open import Data.Unit.Base
open import Level
open import Relation.Binary.PropositionalEquality

open import ProbabilisticLogic.Dp
open import ProbabilisticLogic.Dp.Positive.Monad
open import ProbabilisticLogic.Dp.Positive.Observation

open import CategoricalCrypto.Iface
open import CategoricalCrypto.Machines.Positive.Base using (D₊-setoid)
import CategoricalCrypto.Machines.Positive.Repack as Re
open import CategoricalCrypto.Machines.Positive.Model
import CategoricalCrypto.Machines.Positive.Run as Run
open import CategoricalCrypto.Strategy
open import CategoricalCrypto.UC.Core
import CategoricalCrypto.UC.Machine.Run as OldRun
import CategoricalCrypto.UC.Model.Observation as Observation
import CategoricalCrypto.UC.Model.Seal as Seal
import CategoricalCrypto.UC.Model.Setup as Source
open import CategoricalCrypto.UCSetup.Coverage
open import CategoricalCrypto.UCSetup.Morphism
import CategoricalCrypto.Abstract2.Morphism as Transfer
import CategoricalCrypto.Standard2 as Std
import CategoricalCrypto.Standard2.Morphism as StdM
import CategoricalCrypto.Standard2.Coverage as StdC

private
  module G = MonoidalCategory 𝔾₊
  module F = StrongMonoidalFunctor forget-probabilities

opaque
  unfolding Seal.𝔾ᵒ Seal.ifaceᵒ Seal.unprocᵒ positive-congruence _≈⁺_

  readout-comparison : (f : Observation.𝟘ᵒ G.⇒ Observation.Ωᵒ)
    → Observation.Obs f ≈ₚ Run.run (Re.At.repack 0ℓ (Seal.unprocᵒ f)) (OldRun.closeˢ (ask tt out))
  readout-comparison f = >>=ₚ-cong _ _ _ _ (≈ₚ-refl _) λ s →
    >>=ₚ-cong _ _ _ _ (≈ₚ-refl _) λ where
      (s′ , inj₁ ())
      (s′ , inj₂ b) → ≈ₚ-refl _

  observation-resp : {f g : Observation.𝟘ᵒ G.⇒ Observation.Ωᵒ} → f G.≈ g
                   → Observation.Obs f ≈₊ Observation.Obs g
  observation-resp {f} {g} eq = ≈₊-trans (≈ₚ⇒≈₊ (readout-comparison f))
    (≈₊-trans (Run.run-resp eq (OldRun.closeˢ (ask tt out))) (≈₊-sym (≈ₚ⇒≈₊ (readout-comparison g))))

evaluation₊ : Evaluation G.U 0ℓ 0ℓ
evaluation₊ = record
  { J = Observation.𝟘ᵒ
  ; Ω = Observation.Ωᵒ
  ; S = D₊-setoid Bool
  ; eval = record { to = Observation.Obs ; cong = observation-resp }
  }

private module E = Evaluation evaluation₊

ℰ₊ : Presheaf G.U (Setoids (suc 0ℓ) (suc 0ℓ))
ℰ₊ = Observable.ℰᴼ E.observable

module Target = Std.StdUC 𝔾₊ ℰ₊

tests : PresheafMorphism F.F Source.ℰᵒ ℰ₊
tests = record { ν = ntHelper record
  { η = λ A → record { to = λ t → t ; cong = λ eq m → all-slacks⇒may (eq m) }
  ; commute = λ f m → ≈₊-refl
  } }

tests-epi : PresheafMorphism.Epi tests
tests-epi t = t , λ m → ≈₊-refl

PM→positive : UCSetupMorphism Source.StdSetup Target.StdSetup
PM→positive = StdM.StdUCMorphism Seal.𝔾ᵒ 𝔾₊ Source.ℰᵒ ℰ₊ forget-probabilities tests

module Coverage = StdC.Coverage Seal.𝔾ᵒ 𝔾₊ Source.ℰᵒ ℰ₊ forget-probabilities tests
module Cross = Transfer.Transfer PM→positive

test-coverage : TestCoverage PM→positive
test-coverage = epi⇒TestCoverage PM→positive tests-epi

ancilla-coverage : Coverage.AncillaCoverage
ancilla-coverage = Coverage.essentiallySurjective⇒AncillaCoverage λ W → W , record
  { from = G.id ; to = G.id ; iso = record { isoˡ = G.identity² ; isoʳ = G.identity² } }

preserves-≈ᵁ : Cross.Preserves-≈ᵁ
preserves-≈ᵁ = Coverage.covered-≈ᵁ test-coverage ancilla-coverage

preserves-≤UC : Cross.Preserves-≤UC
preserves-≤UC = Coverage.covered-≤UC test-coverage ancilla-coverage
