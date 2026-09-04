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
--   `UC.Bridge`      `ContextDominated`, the interface to layer 1's concrete
--                    theorems, and the budget a context affords a strategy
--   `UC.Seam`        where layer 1's `transfer` meets an emulation: a strategy
--                    as an environment, `Adequacy`, the POV carry
--                    (`UC.Seam.Carry` proves the carry's premise from
--                    `Adequacy` and `PrAgree`)
--
-- The parameterized layers take a `UCBase` (or, for the last two, the
-- `Grading 𝒫ᴵ` this branch still owes) and so are imported directly:
--
--   `UC.Environment`     the environment presheaf, `_≈ℰ_`, `grade-stable`
--   `UC.Emulation`       `_≤UC_`, its four metatheorems, and the collapse at a
--                        degenerate grade (`unit-grade`)
--   `UC.Family`          `𝒞^ω` at a parameterized index, `absorb`
--   `UC.Audit`           `audit-carry`: an audit-form bound across an emulation,
--                        the simulator absorbed into the environment leg
--   `UC.Seam.Grounding`  the seam's grading-dependent statements
--   `UC.Seam.Audit`      `UC.Audit` at the intended instance
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
