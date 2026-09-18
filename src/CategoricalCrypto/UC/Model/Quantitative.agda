{-# OPTIONS --safe --without-K --guardedness #-}

-- The model's quantitative UC setup: the test presheaf valued in `Approx`
-- (`docs/quantitative-uc-setup-plan.typ` §6).
--
-- `UC.Model.Setup.ℰᵒ` compares two tests by closing the observation of
-- every closure under every positive slack.  This is the same construction
-- with the slack still VISIBLE, so `ℰᵒ` is recovered as the `F₊` image
-- (`≋⇔∼₊`): the two differ by the order of two quantifiers and nothing else.
--
-- ALL closures are admitted.  This is deliberately not the budget-restricted
-- comparison of `UC.Budget`/`UC.Family`: nothing here restricts the test or the
-- closure by an allowance, and no claim is made that the errors of this
-- instance agree with those of the query-aware APIs.
--
-- `Obs` is untouched, and pullback is nonexpansive for the reason `ℰᵒ` is
-- well defined at all — `h ∘ m` is another closure — so the only quantitative
-- input is `obs-resp`, which observes the seal's hom equality EXACTLY.

open import Categories.Category.Monoidal.Bundle using (MonoidalCategory)
open import Categories.Functor.Presheaf using (Presheaf)

open import Data.Rational using (ℚ; 0ℚ)
open import Function.Bundles using (_⇔_; mk⇔)
open import Level using (0ℓ; suc)
open import Relation.Binary.Bundles using (Setoid)

open import ProbabilisticLogic.Dp.Advantage using (≈ₚ[]-resp; ≈ₚ⇒≈ₚ[0])

open import CategoricalCrypto.Approx.Error using (ℚ-ordered)
open import CategoricalCrypto.UC.Approximate using (Approximation; ℚ-errors)
open import CategoricalCrypto.UC.Machine using (Approximationᴹ)
open import CategoricalCrypto.UC.Model.Enrichment using (budgetᵒ)
open import CategoricalCrypto.UC.Model.Observation
  using (Closure; Obs; Test; obs-resp; Ωᵒ; 𝟘ᵒ)
open import CategoricalCrypto.UC.Model.Seal using (∣𝔾ᵒ∣; 𝔾ᵒ)
open import CategoricalCrypto.UC.Model.Setup using (_≋_; ℳ-standard)
open import CategoricalCrypto.UC.Quantitative.Query using (fromBudget; module Tests)

module CategoricalCrypto.UC.Model.Quantitative where

open import CategoricalCrypto.Approx.Forget ℚ-ordered (suc 0ℓ) (suc 0ℓ)
open import CategoricalCrypto.Approx.Space ℚ-ordered
open import CategoricalCrypto.UC.Quantitative ℚ-ordered
open import CategoricalCrypto.UC.Quantitative.Bridge ℚ-ordered

private
  module Ap = Approximation Approximationᴹ
  module G = MonoidalCategory 𝔾ᵒ

------------------------------------------------------------------------
-- Tests at a measured error

infix 4 _≈ᵗ[_]_

_≈ᵗ[_]_ : {A : G.Obj} → Test A → ℚ → Test A → Set (suc 0ℓ)
_≈ᵗ[_]_ {A} E ε F = (m : Closure A) → Obs (E G.∘ m) Ap.≈[ ε ] Obs (F G.∘ m)

approxᵗ : (A : G.Obj) → Approximation (Test A) ℚ-errors (suc 0ℓ)
approxᵗ A = record
  { _≈[_]_    = _≈ᵗ[_]_
  ; ≈[]-refl  = λ _ → Ap.≈[]-refl
  ; ≈[]-sym   = λ h m → Ap.≈[]-sym (h m)
  ; ≈[]-trans = λ h k m → Ap.≈[]-trans (h m) (k m)
  ; ≈[]-mono  = λ le h m → Ap.≈[]-mono le (h m)
  }

spaceᵗ : G.Obj → ApproxSpace (suc 0ℓ) (suc 0ℓ)
spaceᵗ A = record { Carrier = Test A ; approx = approxᵗ A }

private
  -- Every presheaf law is the seal's hom equality observed at zero error.
  cast : {A : G.Obj} {E F : Test A} → E G.≈ F → E ≈ᵗ[ 0ℚ ] F
  cast eq _ = ≈ₚ⇒≈ₚ[0] (obs-resp (G.∘-resp-≈ˡ eq))

Qᵒ : Presheaf ∣𝔾ᵒ∣ (Approx (suc 0ℓ) (suc 0ℓ))
Qᵒ = record
  { F₀ = spaceᵗ
  ; F₁ = λ h → record
      { map       = G._∘ h
      ; preserves = λ hyp m →
          ≈ₚ[]-resp (obs-resp G.sym-assoc) (obs-resp G.sym-assoc) (hyp (h G.∘ m))
      }
  ; identity     = λ _ → cast G.identityʳ
  ; homomorphism = λ _ → cast G.sym-assoc
  ; F-resp-≈     = λ eq _ → cast (G.∘-resp-≈ʳ eq)
  }

QSetupᵒ : QUCSetup (suc 0ℓ) (suc 0ℓ) (suc 0ℓ) (suc 0ℓ) (suc 0ℓ) (suc 0ℓ) (suc 0ℓ) (suc 0ℓ)
QSetupᵒ = record { 𝒞 = ∣𝔾ᵒ∣ ; ℐ = 𝔾ᵒ ; ℳ = ℳ-standard ; Q = Qᵒ }

-- The quantitative metatheory at this instance.  Named rather than opened: a
-- consumer that also opens `Model.Setup` would otherwise see each of the two
-- theories' names twice.
module QUCᵒ = QBridge QSetupᵒ

------------------------------------------------------------------------
-- …and its `F₊` image is the existing qualitative test presheaf

≋⇒∼₊ : {A : G.Obj} {E F : Test A} → E ≋ F → Setoid._≈_ ⟦ spaceᵗ A ⟧₊ E F
≋⇒∼₊ h ε pos m = h m ε pos

∼₊⇒≋ : {A : G.Obj} {E F : Test A} → Setoid._≈_ ⟦ spaceᵗ A ⟧₊ E F → E ≋ F
∼₊⇒≋ h m ε pos = h ε pos m

≋⇔∼₊ : {A : G.Obj} {E F : Test A} → (E ≋ F) ⇔ Setoid._≈_ ⟦ spaceᵗ A ⟧₊ E F
≋⇔∼₊ = mk⇔ ≋⇒∼₊ ∼₊⇒≋

-- The same observation restricted by allowance: `UC.Quantitative.Query` at
-- this branch's budget.  It is a DIFFERENT space from `spaceᵗ` above, which
-- admits every closure at one scalar error.
module Queryᵒ = Tests ∣𝔾ᵒ∣ (fromBudget budgetᵒ) Approximationᴹ 𝟘ᵒ Ωᵒ Obs
                     (λ e → ≈ₚ⇒≈ₚ[0] (obs-resp e))
