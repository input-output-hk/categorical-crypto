{-# OPTIONS --safe --without-K --guardedness #-}

-- `UC.Quantitative.Family` at the sealed machine bundle: the quantitative
-- contextual relation `_≈ctx[_]_` on families of graded morphisms, and the
-- simulator-bearing emulation witness `_≤UC^ωᵉ_` over it.

open import CategoricalCrypto.Approx.Error
open import CategoricalCrypto.Approx.Evaluation ℚ-ordered

open import CategoricalCrypto.UC.Model.Enrichment
open import CategoricalCrypto.UC.Model.Observation
open import CategoricalCrypto.UC.Model.Seal

module CategoricalCrypto.UC.Model.Family.Contextual where

private module Q = QEvaluation qevaluationᵒ

open import CategoricalCrypto.UC.Quantitative.Family
  𝔾ᵒ gradingᵒ Q.approx Q.J Q.Ω Q.read Q.read-resp₀ public
