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
--                `UC.Emulation`    `_≤UC_` and its three metatheorems.
--                                  Universal composition is the inherited
--                                  theorem, not one of these —
--                                  `UC.Model.Bridge` carries it across
--                `UC.Robust`       `SaturatedProperty`, `Robust` and
--                                  `uc-preserves`: the carry with no
--                                  probability under it, where the simulator
--                                  slides into the test and an
--                                  observation-invariant property needs no
--                                  budget to pay for it.  `UC.Robust.Model`
--                                  runs it at the inherited emulation
--                `UC.Core.Standard`
--                                  `gradingᵗ`: a monoidal category grades
--                                  itself — the inherited `UCSetup` doctrine's
--                                  action, weakened to what the core asks
--   enrichment   `UC.Approximate`  `ErrorAlgebra`, `Approximation`,
--                                  `ApproximateObservation`, `Induced`, `Mass`
--                `UC.Budget`       `Budget`, `ctxBudget` — the resource doctrine
--                `UC.Environment.Approximate`
--                                  `_≈ℰ[ ε ]_` and its collapse
--                `UC.Audit`        `AuditEvent`, the audit event a premise is
--                                  about, and `audit-carry`: a bound on it
--                                  across an emulation, the simulator absorbed
--                                  into the environment leg
--                `UC.Family`       the asymptotic constructor — `𝒞^ω` at a
--                                  parameterized index, and `absorb`, where a
--                                  vanishing bound BECOMES the core's `_≈ℰ_`
--                `UC.Family.Monoidal`
--                                  `Famᴹ`, the family's grades made monoidal
--                                  by the budget's four unitor certificates,
--                                  and `ucSetup^ω` — so the INHERITED
--                                  metatheory runs at the asymptotic family
--                `UC.Family.Negligible`
--                                  the same layer's negligible tier: a second
--                                  `Observation` on `Fam` keeping the error
--                                  witness (`_∼ᴺ_`, `_≤UCᴺ_`), and `≈ℰⁿ⇒≈ℰᴺ`;
--                                  `UC.Model.Family.Negligible` inhabits it at
--                                  the machine family, and its §1 acceptance
--                                  tests are `UC.Approximate.LocalTests`
--   model        `UC.Machine`      `𝒫ᴵ`, processes on `Iface`s, the ticked
--                                  verdict interface, the observation at `Dₚ`
--                `UC.QueryBound`   the amortised-potential certificate — a
--                                  query bound with content; what it means on a
--                                  run is `UC.QueryBound.Counting`, and
--                                  `UC.QueryBound.Compose{,.Step,.Laws}` is
--                                  where it multiplies along composition, which
--                                  `UC.Machine.Budget` feeds to the resource
--                                  doctrine.  Only the counting theorem is
--                                  re-exported below: the composition line
--                                  spends the `Proc` inversion per field (its
--                                  headers carry the measured costs), which no
--                                  consumer of this entry point should pay
--                                  unless it is assembling a `Budget`
--                `UC.QueryBound.Object`
--                                  the same predicate at 𝒢's own objects — the
--                                  spelling `gradingᴹ`'s action is stated in
--                `UC.Machine.Grading`
--                                  where a query-bound certificate about a
--                                  pinned relay meets the derived grading's
--                                  action, through `UC.Machine.Dictionary`'s
--                                  zigzags
--                `UC.Machine.Budget`
--                                  `budgetᴹ`: the enrichment's `Budget`
--                                  inhabited at `gradingᴹ`.  Not re-exported
--                                  below either — it is the one consumer that
--                                  pays for the composition line
--                `UC.Machine.Bridge`
--                                  `ContextDominated`, the interface to layer
--                                  1's concrete theorems
--                `UC.Machine.Dominated`
--                                  `dominated`: that interface DISCHARGED, via
--                                  the two-machine skeleton
--                `UC.Seam`         where layer 1's `transfer` meets an
--                                  emulation: a strategy as an environment,
--                                  `Adequacy`, the POV carry (`UC.Seam.Carry`
--                                  proves its premise from `Adequacy` and
--                                  `PrAgree`); `UC.Seam.Grounding` and
--                                  `UC.Seam.Audit` name what the instance owes
--                `UC.Seam.Grounded`
--                                  and what discharges it at the trivial
--                                  grade: `SubBlind`, `StratIsEnv` and with
--                                  them `UnitGrade`
--                `UC.Factor`       `closedᵒ`/`stageᵒ` and `factorᵖ`/`liftᵖ`:
--                                  the UC-object image of `_∘ᵖ_` factors on
--                                  the nose, so a sub-protocol emulation
--                                  lifts to the composed system by
--                                  `UC-compose` (the retraction-conjugated
--                                  `sub` congruence is `Abstract2.Factor`)
--                `UC.Seam.Audit.Prefix`
--                                  the BUDGETED route's consumer end:
--                                  `uc-audit-bounded` turns an ideal monitor
--                                  bound into the real system's own
--                                  probability across a budgeted emulation,
--                                  the simulator's initialization tolerated as
--                                  a prefix and its queries charged
--                `UC.Saturated`    the saturated form of a concrete safety
--                                  bound — one slack per polynomial allowance,
--                                  at the vanishing grade and at the
--                                  negligible one, with the invariance proved
--                                  for each
--                `UC.Asymptotic`   the consumer end: an emulation FAMILY, and
--                                  the two ways a bound crosses it — graded
--                                  (`simCost` charged) and probabilistic (the
--                                  trivial-grade collapse into `UC.Saturated`)
--
-- The parameterized modules take a `UCBase` and so are imported directly
-- rather than re-exported here; `UC.Machine.ucBaseᴹ` is the one to feed them at
-- the model.
--
-- `UC.Model` is the layer's SECOND root, and it is deliberately not re-exported
-- here: it instantiates the INHERITED abstract theory (`UCSetup`/`Abstract2`
-- via `Standard2.StdUC`) at the same machine layer, behind an `opaque` seal —
-- the measured recipe without which the setup does not typecheck at all — so
-- its names only make sense inside that `open StdUC` discipline.
-- `UC.Model.Bridge` identifies the two, and `UC.Seam.Grounded` above is where
-- they meet.  `CategoricalCrypto` reaches both roots.
--
-- Everything is `--safe --without-K`; the `Dₚ`-facing modules add
-- `--guardedness` and nothing adds anything else.  In particular there is no K
-- island; `UC.Environment`'s header says why the reference arc needed one.

module CategoricalCrypto.UC where

open import CategoricalCrypto.UC.Approximate public
open import CategoricalCrypto.UC.Asymptotic public
open import CategoricalCrypto.UC.Asymptotic.Audit public
open import CategoricalCrypto.UC.Asymptotic.Family public
open import CategoricalCrypto.UC.Budget public
open import CategoricalCrypto.UC.Core public
open import CategoricalCrypto.UC.Machine public
open import CategoricalCrypto.UC.Machine.Bridge public
open import CategoricalCrypto.UC.Machine.Dominated public
open import CategoricalCrypto.UC.Machine.Grading public
open import CategoricalCrypto.UC.QueryBound public
open import CategoricalCrypto.UC.QueryBound.Counting public
open import CategoricalCrypto.UC.Saturated public
open import CategoricalCrypto.UC.Seam.Audit.Prefix public
open import CategoricalCrypto.UC.Factor public
open import CategoricalCrypto.UC.Seam.Grounded public

-- Closure-only: the negligible tier's acceptance tests (leaf, nothing to open).
import CategoricalCrypto.UC.Approximate.LocalTests
