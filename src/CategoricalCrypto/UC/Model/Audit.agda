{-# OPTIONS --safe --without-K --guardedness #-}

-- `UC.Audit` at the intended instance: the sealed bundle, its observation, and
-- `UC.Model.Enrichment`'s grading and mass.

open import CategoricalCrypto.UC.Model.Enrichment
open import CategoricalCrypto.UC.Model.Observation
open import CategoricalCrypto.UC.Model.Seal

import CategoricalCrypto.UC.Audit as Aud

module CategoricalCrypto.UC.Model.Audit where

private
  module A = Aud 𝔾ᵒ evaluationᵒ gradingᵒ massᵒ

open A public
  using (_≤UC[_]_; ≤UC[]⇒≤UC; Context; observeᶜ; _∙ᶜ_; Certified; _∙ˢ_; budget-∙ˢ;
         Permitted; AuditBound; pinned; pinned-bound; absorb; Absorbs; ≈ᵁ-at; audit-carry)
