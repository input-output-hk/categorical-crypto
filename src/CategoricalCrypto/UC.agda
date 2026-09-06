{-# OPTIONS --safe --without-K --guardedness #-}

-- The UC layer's entry point: one import for a consumer.
--
-- The layer is three tiers, and the split is the point.  The CORE is
-- qualitative: a category, the grading action of adversary interfaces, and an
-- equivalence on what closed runs show.  The ENRICHMENT adds what a model may
-- know and general UC must not assume — a measurable error, a query budget, a
-- mass.  The MODEL is the `Dₚ` machine instance, where the enrichment is
-- discharged and the core's equivalence is CONSTRUCTED from rational advantage.
--
--   core         `UC.Core`         `Grading`, `Observation`, `UCBase`
--                `UC.Environment`  the environment presheaf, `_≈ℰ_`,
--                                  `grade-stable`
--                `UC.Emulation`    `_≤UC_`, its four metatheorems, the collapse
--                                  at a degenerate grade (`unit-grade`)
--                `UC.Core.Standard`
--                                  `gradingᵗ`: a monoidal category grades
--                                  itself — the inherited `UCSetup` doctrine's
--                                  action, weakened to what the core asks
--   enrichment   `UC.Approximate`  `ErrorAlgebra`, `Approximation`,
--                                  `ApproximateObservation`, `Induced`, `Mass`
--                `UC.Budget`       `Budget`, `ctxBudget` — the resource doctrine
--                `UC.Environment.Approximate`
--                                  `_≈ℰ[ ε ]_` and its collapse
--                `UC.Audit`        `audit-carry`: an audit-form bound across an
--                                  emulation, the simulator absorbed into the
--                                  environment leg
--                `UC.Family`       the asymptotic constructor — `𝒞^ω` at a
--                                  parameterized index, and `absorb`, where a
--                                  vanishing bound BECOMES the core's `_≈ℰ_`
--   model        `UC.Machine`      `𝒫ᴵ`, processes on `Iface`s, the ticked
--                                  verdict interface, the observation at `Dₚ`
--                `UC.QueryBound`   the amortised-potential certificate — a
--                                  query bound with content; what it means on a
--                                  run is `UC.QueryBound.Counting`, and
--                                  `UC.QueryBound.Compose{,.Step,.Laws}` is
--                                  where it multiplies along composition, up to
--                                  `BudgetLawsᴹ`.  Only the counting theorem is
--                                  re-exported below: the composition line
--                                  spends the `Proc` inversion per field (its
--                                  headers carry the measured costs), which no
--                                  consumer of this entry point should pay
--                                  unless it is assembling a `Budget`
--                `UC.Machine.Grading`
--                                  where a query-bound certificate about a
--                                  pinned relay meets the derived grading's
--                                  action, through `UC.Machine.Dictionary`'s
--                                  zigzags
--                `UC.Machine.Bridge`
--                                  `ContextDominated`, the interface to layer
--                                  1's concrete theorems
--                `UC.Seam`         where layer 1's `transfer` meets an
--                                  emulation: a strategy as an environment,
--                                  `Adequacy`, the POV carry (`UC.Seam.Carry`
--                                  proves its premise from `Adequacy` and
--                                  `PrAgree`); `UC.Seam.Grounding` and
--                                  `UC.Seam.Audit` name what the instance owes
--                `UC.Saturated`    the saturated form of a concrete safety
--                                  bound, the shape invariant under the core's
--                                  equivalence
--
-- The parameterized modules take a `UCBase` and so are imported directly
-- rather than re-exported here; `UC.Machine.ucBaseᴹ` is the one to feed them at
-- the model.
--
-- Everything is `--safe --without-K`; the `Dₚ`-facing modules add
-- `--guardedness` and nothing adds anything else.  In particular there is no K
-- island: the reference arc needed one because its environment relation
-- bundled the ancilla existentially, and `UC.Environment` does not.

module CategoricalCrypto.UC where

open import CategoricalCrypto.UC.Approximate public
open import CategoricalCrypto.UC.Budget public
open import CategoricalCrypto.UC.Core public
open import CategoricalCrypto.UC.Machine public
open import CategoricalCrypto.UC.Machine.Bridge public
open import CategoricalCrypto.UC.Machine.Grading public
open import CategoricalCrypto.UC.QueryBound public
open import CategoricalCrypto.UC.QueryBound.Counting public
open import CategoricalCrypto.UC.Saturated public
