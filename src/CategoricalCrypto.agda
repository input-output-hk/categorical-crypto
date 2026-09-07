{-# OPTIONS --safe #-}
module CategoricalCrypto where

-- Open problems

-- We want to conveniently specify a machine that, on an input, sends
-- messages to other machines, waits for replies and then continues
-- execution.

-- Can we write constructors more monadically?

-- Improve syntax generally

open import Categories.MonoidalCoherence

open import CategoricalCrypto.Channel.Category public
open import CategoricalCrypto.Channel.Core public
open import CategoricalCrypto.Channel.Selection public
open import CategoricalCrypto.Machine.Constraints public
open import CategoricalCrypto.Machine.Core public
open import CategoricalCrypto.Machine.Iso public
open import CategoricalCrypto.SFunM public

-- The monoidal laws of the machine category and the n-ary rewiring lemmas.
-- Checked from here, but not re-exported: they are large, and their working
-- vocabulary (`Pair`, `Trc`, `Reindex`, …) would crowd the namespace.  Import
-- `CategoricalCrypto.Machine.Monoidal` or `…Machine.NAry` explicitly.
import CategoricalCrypto.Machine.Monoidal
import CategoricalCrypto.Machine.NAry
open import CategoricalCrypto.Examples.Basic
open import CategoricalCrypto.Examples.Commitment
open import CategoricalCrypto.Examples.Signatures
