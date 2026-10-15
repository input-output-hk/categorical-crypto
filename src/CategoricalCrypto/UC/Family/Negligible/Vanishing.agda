{-# OPTIONS --safe --without-K #-}

-- Identity computational data, with context-local negligible observation
-- witnesses forgotten to convergence.  No witness is moved outside its
-- closure, test or ancilla quantifier.  The UC map retains the source's
-- simulator at each adversary, not just its dummy-adversary simulator.

open import Categories.Category.Instance.Rates
open import Categories.Category.Monoidal.Bundle
open import Categories.Functor using () renaming (id to idF)
open import Categories.Functor.Presheaf.Morphism
open import Categories.LocallyGraded.SubCategory
open import Categories.NaturalTransformation using (ntHelper)

open import Data.Nat.Base as ℕ using (ℕ)
open import Data.Product.Base using (Σ-syntax; _,_; proj₁)
open import Level using (Level)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import CategoricalCrypto.Abstract2.Morphism using (module Refine)
open import CategoricalCrypto.Approx.Error using (ℚ-ordered)
open import CategoricalCrypto.Approx.Evaluation ℚ-ordered using (QEvaluation)
open import CategoricalCrypto.UC.Approximate using (Negligible⇒→0)
open import CategoricalCrypto.UC.Core using (Evaluation; Observable)
open import CategoricalCrypto.UCSetup using (UCSetup)
open import CategoricalCrypto.UCSetup.Morphism using (UCSetupMorphism; changeKernel)

import CategoricalCrypto.UC.Family.Negligible as Negᴹ
import CategoricalCrypto.UC.Family.Negligible.Setup as Setupᴹ
import CategoricalCrypto.UC.Family.Vanishing as Vanᴹ

module Rates = SymmetricMonoidalCategory Rates

module CategoricalCrypto.UC.Family.Negligible.Vanishing
  {o ℓ e os ℓa qs : Level}
  (M : MonoidalCategory o ℓ e)
  (qro : QEvaluation (MonoidalCategory.U M) os ℓa)
  (Rg : GradedSubCat Rates.monoidalCategory M qs)
  (Ix : Set) (κ : Ix → ℕ) (κ-cofinal : (N : ℕ) → Σ[ i ∈ Ix ] N ℕ.≤ κ i) where

open import CategoricalCrypto.UC.Family M qro Rg Ix κ κ-cofinal
  using (Evaluation^ω; ucSetup^ω)
open import CategoricalCrypto.UC.Family.Negligible.Setup M qro Rg Ix κ κ-cofinal
  using (ucSetupᴺ)

module Source = Setupᴹ.Canonicalᴺ M qro Rg Ix κ κ-cofinal
  using (Channel; _⇒_; T₀; _∘_; sub; _≈ᵁ_; _≤UC_; module KE)
module Target = Vanᴹ.Canonical^ω M qro Rg Ix κ κ-cofinal
  using (_≈ᵁ_; _≤UC_; module KE)

private
  module N = Negᴹ M qro Rg Ix κ κ-cofinal using (Evaluationᴺ)
  module ON = Observable (Evaluation.observable N.Evaluationᴺ)
  module OW = Observable (Evaluation.observable Evaluation^ω)
  module Q = QEvaluation qro
  variable A B X Y X′ : Source.Channel

observationsᴺ⇒observationsω : (t u : ON.Test A) → t ON.≋ u → t OW.≋ u
observationsᴺ⇒observationsω t u h m ε ε>0 =
  let δ , neg , bnd = h m
      N , tail = Negligible⇒→0 neg ε ε>0
  in N , λ i le → Q.≈[]-mono (tail (κ i) le) (bnd i)

νᴺω : PresheafMorphism idF (UCSetup.ℰ ucSetupᴺ) (UCSetup.ℰ ucSetup^ω)
νᴺω = record { ν = ntHelper record
  { η = λ A → record { to = λ t → t ; cong = λ {t} {u} → observationsᴺ⇒observationsω t u }
  ; commute = λ f {x} → OW.≈⇒≋ {t = x Source.∘ f} {u = x Source.∘ f}
      (λ _ → MonoidalCategory.Equiv.refl M) } }

negligible⇒vanishing : UCSetupMorphism ucSetupᴺ ucSetup^ω
negligible⇒vanishing = changeKernel (UCSetup.ℰ ucSetupᴺ) (UCSetup.ℰ ucSetup^ω) νᴺω

private
  module SN = UCSetup ucSetupᴺ
  module SW = UCSetup ucSetup^ω

≈ℰᴺ⇒≈ℰω : (f g : Source._⇒_ A B) → f SN.≈ℰ g → f SW.≈ℰ g
≈ℰᴺ⇒≈ℰω f g h = Target.KE.mk∼ λ {t} →
  observationsᴺ⇒observationsω (t Source.∘ f) (t Source.∘ g) (Source.KE.run∼ h {t})

private
  module R = Refine ucSetupᴺ (UCSetup.ℰ ucSetup^ω)
    (λ {_} {_} {f} {g} → ≈ℰᴺ⇒≈ℰω f g)

≈ᵁᴺ⇒≈ᵁω : (f g : Source._⇒_ A (Source.T₀ X B)) → f Source.≈ᵁ g → f Target.≈ᵁ g
≈ᵁᴺ⇒≈ᵁω f g = R.≈ᵁ-refine {f = f} {g = g}

≤UCᴺ⇒≤UCω : (f : Source._⇒_ A (Source.T₀ X B)) (g : Source._⇒_ A (Source.T₀ Y B))
            → f Source.≤UC g → f Target.≤UC g
≤UCᴺ⇒≤UCω f g le a =
  let s , h = le a
  in s , ≈ᵁᴺ⇒≈ᵁω (Source.sub a Source.∘ f) (Source.sub s Source.∘ g) h

same-simulator : (f : Source._⇒_ A (Source.T₀ X B)) (g : Source._⇒_ A (Source.T₀ Y B))
                 (le : f Source.≤UC g) (a : Source._⇒_ X X′)
               → proj₁ (≤UCᴺ⇒≤UCω f g le a) ≡ proj₁ (le a)
same-simulator f g le a = refl
