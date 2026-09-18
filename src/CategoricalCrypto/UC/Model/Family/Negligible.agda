{-# OPTIONS --safe --without-K --guardedness #-}

-- `UC.Family.Negligible` at the machine family: the negligible tier's
-- observation and emulation order inhabited at the intended model, on the same
-- ingredients `UC.Model.Family` feeds the qualitative tier.
--
-- So the tier is not a construction awaiting a model — `_≈ℰᴺ_` exists HERE,
-- and `UC.Family.Negligible.Setup.≈ℰⁿ⇒≤UC` puts an ingested bound
-- (`UC.Model.Family.Ingest.ingest-≈ℰⁿ`) into the INHERITED order with its
-- error witness kept, which is where `ingest-≤UCᵁ` lands it too.

open import Data.Nat.Base using (ℕ)
open import Data.Nat.Properties using (≤-refl)
open import Data.Product.Base using (_,_)

open import CategoricalCrypto.UC.Model.Enrichment using (budgetᵒ)
open import CategoricalCrypto.UC.Model.Observation using (approximateᵒ)

import CategoricalCrypto.UC.Model.Family as F

module CategoricalCrypto.UC.Model.Family.Negligible where

open import CategoricalCrypto.UC.Family.Negligible
  F.baseᴹ approximateᵒ budgetᵒ ℕ (λ n → n) (λ N → N , ≤-refl) public
