{-# OPTIONS --safe --without-K --guardedness #-}

-- `UCSetup` at the machine FAMILY: `UC.Family.Monoidal` instantiated at the
-- sealed bundle, so the inherited metatheory is available asymptotically, with
-- `UC.Family.Vanishing` on the same ingredients supplying `Canonical^ω` and
-- `≈ℰ^ω⇒≤UC` — the step into the INHERITED order, where `UC-compose` is.
--
-- `docs/protocol-implementation-review.md` §4 asks for the intended
-- machine-family UC setup to be CONSTRUCTED rather than described.  Every
-- ingredient is already proved: the monoidal bundle is the seal's own, the
-- budget is `UC.Model.Enrichment`'s, and the observation and its `qapx` are
-- the pair `UC.Model.Observation` gets from one `Induced` — so `induces` is
-- the identity and `⟦⟧-resp-≈₀` is the model's exact respect of the seal's hom
-- equality.  The index is the security parameter itself, cofinal by `≤-refl`.
--
-- The ingestion is next door: turning a level-indexed layer-1 bound into
-- `_≈ℰ[_]_` here needs `UC.Machine.Bridge.ContextDominated` read at SEAL
-- objects, which is `UC.Model.Dominated`, and `UC.Model.Family.Ingest` is what
-- spends it.  The other asymptotic consumer goes through the trivial-grade
-- collapse instead (`UC.Asymptotic`).

open import Data.Nat.Base using (ℕ)
open import Data.Nat.Properties using (≤-refl)
open import Data.Product.Base using (_,_)

open import CategoricalCrypto.UC.Model.Enrichment using (budgetᵒ)
open import CategoricalCrypto.UC.Model.Observation using (approximateᵒ; observationᵒ)
open import CategoricalCrypto.UC.Model.Seal using (𝔾ᵒ)

module CategoricalCrypto.UC.Model.Family where

open import CategoricalCrypto.UC.Family.Monoidal
  𝔾ᵒ observationᵒ approximateᵒ budgetᵒ ℕ (λ n → n) (λ N → N , ≤-refl) public

open import CategoricalCrypto.UC.Family.Vanishing
  𝔾ᵒ observationᵒ approximateᵒ budgetᵒ ℕ (λ n → n) (λ N → N , ≤-refl) public
