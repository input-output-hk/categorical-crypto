{-# OPTIONS --safe --without-K --guardedness #-}

-- Finite static tables, perfect pulled-back tests, and initialized execution:
-- docs/uc-setup-itm.md §6.1. No PPT or general ITM→PM security transfer is used.

module CategoricalCrypto.Examples.ITM.Tests where

open import Categories.Category.Monoidal
open import Categories.FreeMonoidal

open import Data.Bool.Base
open import Data.Product.Base
open import Data.Rational as ℚ
open import Data.Rational.Properties
open import Data.Rational.Properties.Ext
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary.Decidable
open import Relation.Nullary.Negation.Core

open import ProbabilisticLogic.Distribution.Uniform
open import ProbabilisticLogic.Dp
open import ProbabilisticLogic.Dp.Advantage

open import CategoricalCrypto.Approx.Error
open import CategoricalCrypto.Examples.ITM.Interpretation
open import CategoricalCrypto.Examples.ITM.Tables
open import CategoricalCrypto.ITM.Core
open import CategoricalCrypto.UC.Machine
open import CategoricalCrypto.UC.Model.Seal

import CategoricalCrypto.ITM.Setup as ITM

private
  module T = FreeMonoidal itmData
  module G = MonoidalCategory 𝔾ᵒ
  module Ap = AllPositive ℚ-refinement Approximationᴹ

marker-environment : ITM.Env (Service ITM.⊗₀ Service)
marker-environment = probeTest false

explicit-simulator : real ITM.≈ᵁ simulated
explicit-simulator = ITM.≈ᴾ⇒≈ᵁ (G.Equiv.sym compiled-correct)

secure : real ITM.≤UC ideal
secure = ITM.dummy-complete (T.var simulator , explicit-simulator)

markers-separated : ¬ (observation false real Ap.∼ᵃ observation false ideal)
markers-separated e =
  let m , le = proj₁ (≈ₚ[]-resp real-marker ideal-marker (e ½ (toWitness {a? = 0ℚ <? ½} _))) true 1
  in 1≰½ (≤-trans (≤-reflexive (sym (returnₚ-cum 0 true (indᵇ true))))
          (≤-trans le (≤-trans (+-monoˡ-≤ ½ (returnₚ-cum-≤ m false (indᵇ true) (indᵇ-nn true)))
                               (≤-reflexive (+-identityˡ ½)))))

marker-pull-distinct : ¬ (ITM.Env._≈_ {D = T.unit}
  (ITM.pull real marker-environment) (ITM.pull ideal marker-environment))
marker-pull-distinct e = markers-separated (e emptyClosure)

initialized-distinct : ¬ (real ITM.≈ℰ ideal)
initialized-distinct e = marker-pull-distinct (ITM.KE.run∼ e {marker-environment})

initialized-distinctᵁ : ¬ (real ITM.≈ᵁ ideal)
initialized-distinctᵁ e = initialized-distinct (ITM.≈ᵁ⇒≈ℰ e)

simulation-observable : ¬ (simulated ITM.≈ℰ ideal)
simulation-observable e = initialized-distinct (ITM.≈ℰ-trans (ITM.≈ᵁ⇒≈ℰ explicit-simulator) e)

simulator-nonidentity : ¬ (T.var simulator ITM.≈ T.id)
simulator-nonidentity e = simulation-observable (ITM.≈C⇒≈ℰ
  (ITM.𝒞.Equiv.trans (ITM.𝒞.∘-resp-≈ˡ (ITM.⊗.F-resp-≈ (e , ITM.𝒞.Equiv.refl)))
    (ITM.𝒞.Equiv.trans (ITM.𝒞.∘-resp-≈ˡ ITM.⊗.identity) ITM.identityˡ)))
