{-# OPTIONS --safe --without-K --guardedness #-}

-- `UCSetup` at the machine FAMILY: `UC.Family.Monoidal` instantiated at the
-- sealed bundle, so the inherited metatheory is available asymptotically.
--
-- `docs/protocol-implementation-review.md` §4 asks for the intended
-- machine-family UC setup to be CONSTRUCTED rather than described.  Every
-- ingredient is already proved: the monoidal bundle is the seal's own, the
-- observation is the model's (`UC.Model.Bridge`), the budget is
-- `UC.Model.Enrichment`'s, and the approximation is the very one
-- `observationᵒ`'s equivalence was induced from — so `induces` is the
-- identity and `⟦⟧-resp-≈₀` is the model's exact respect of the seal's hom
-- equality.  The index is the security parameter itself, cofinal by `≤-refl`.
--
-- What this module does NOT supply is the ingestion: turning a level-indexed
-- layer-1 bound into `_≈ℰ[_]_` here needs `UC.Machine.Bridge.ContextDominated`
-- read at SEAL objects, where it is stated at `Iface`-images.  The asymptotic
-- consumer that closes today goes through the trivial-grade collapse instead
-- (`UC.Asymptotic`).

open import Data.Nat.Base using (ℕ)
open import Data.Nat.Properties using (≤-refl)
open import Data.Product.Base using (_,_)
open import Level using (0ℓ)

open import ProbabilisticLogic.Dp.Advantage using (≈ₚ⇒≈ₚ[0])

open import CategoricalCrypto.UC.Approximate using (ApproximateObservation; ℚ-errors)
open import CategoricalCrypto.UC.Machine using (Approximationᴹ)
open import CategoricalCrypto.UC.Model.Bridge using (observationᵒ)
open import CategoricalCrypto.UC.Model.Enrichment using (budgetᵒ)
open import CategoricalCrypto.UC.Model.Observation using (obs-resp)
open import CategoricalCrypto.UC.Model.Seal using (𝔾ᵒ)

module CategoricalCrypto.UC.Model.Family where

approximateᵒ : ApproximateObservation observationᵒ ℚ-errors 0ℓ
approximateᵒ = record
  { approx     = Approximationᴹ
  ; induces    = λ h → h
  ; ⟦⟧-resp-≈₀ = λ e → ≈ₚ⇒≈ₚ[0] (obs-resp e)
  }

open import CategoricalCrypto.UC.Family.Monoidal
  𝔾ᵒ observationᵒ approximateᵒ budgetᵒ ℕ (λ n → n) (λ N → N , ≤-refl) public
