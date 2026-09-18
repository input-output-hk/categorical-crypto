{-# OPTIONS --safe --without-K --guardedness #-}

-- `UC.Quantitative.Family.Compose` at the sealed machine bundle: composition of
-- quantitative emulation witnesses with the error kept — `≤UC^ωᵉ-trans` and
-- `UC-composeᵉ`, each with its exact allowance substitution, and
-- `≈ctx-dom`/`≤UC^ωᵉ-dom`, which plug a rate-zero process under the domain for
-- free.

open import CategoricalCrypto.UC.Asymptotic.Contextual using (module Compose)

module CategoricalCrypto.UC.Asymptotic.Compose where

open Compose public
