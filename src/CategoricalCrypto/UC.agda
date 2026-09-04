{-# OPTIONS --safe --without-K --guardedness #-}

-- The UC layer's entry point: one import for a consumer.
--
--   `UC.Base`        what the layer asks of an ambient category — the grading
--                    action, the ε-indexed observation, the query-budget
--                    plumbing
--   `UC.Machine`     the intended model: `𝒫ᴵ`, processes on `Iface`s, the
--                    ticked verdict interface, the observation at `Dₚ`
--   `UC.QueryBound`  the amortised-potential certificate and the counting
--                    statement — a query bound with content
--   `UC.Bridge`      `Reflects`, the interface to layer 1's concrete theorems
--
-- The four parameterized layers take a `UCBase` (or, for the last two, the
-- `Grading 𝒫ᴵ` this branch still owes) and so are imported directly:
--
--   `UC.Environment`  the environment presheaf, `_≈ℰ_`, `grade-stable`
--   `UC.Emulation`    `_≤UC_` and its four metatheorems
--   `UC.Family`       `𝒞^ω` at a parameterized index, `absorb`
--   `UC.Seam`         where layer 1's `transfer` meets an emulation
--
-- Everything is `--safe --without-K`; the `Dₚ`-facing modules add
-- `--guardedness` and nothing adds anything else.  In particular there is no K
-- island: the reference arc needed one because its environment relation
-- bundled the ancilla existentially, and `UC.Environment` does not.

module CategoricalCrypto.UC where

open import CategoricalCrypto.UC.Base public
open import CategoricalCrypto.UC.Bridge public
open import CategoricalCrypto.UC.Machine public
open import CategoricalCrypto.UC.QueryBound public
