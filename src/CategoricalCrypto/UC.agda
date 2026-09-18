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
--                                  `grade-stable`, and `tv₁-∘`, the slide by
--                                  which a stage of the process becomes a stage
--                                  of the test
--                `UC.Emulation`    `_≤UC_` and its three metatheorems.
--                                  Universal composition is the inherited
--                                  theorem, not one of these —
--                                  `UC.Model.Bridge` carries it across
--                `UC.Robust.Observation`
--                                  `SaturatedProperty`, `Robust` and
--                                  `uc-preserves` at a `UCBase`: the carry with
--                                  no probability under it, where the simulator
--                                  slides into the test and an
--                                  observation-invariant property needs no
--                                  budget to pay for it.  Independently scoped:
--                                  the canonical statement is the inherited
--                                  layer's `UC.Robust` (below)
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
--                                  into the environment leg.  `carry-obs` is
--                                  that carry's structural content with neither
--                                  class nor budget on it, which is what a
--                                  direct consumer spends
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
--                                  witness (`_∼ᴺ_`, `_≈ℰᴺ_`) and the one-way
--                                  bridge `≈ℰⁿ⇒≈ℰᴺ` into it.  It has no order
--                                  of its own: that was `UC.Emulation`'s
--                                  renamed and is retired
--                                  (`docs/retirement-negligible-order.md`).
--                `UC.Audit.Canonical`
--                                  an audit emulation read as a cost-certified
--                                  witness for the INHERITED order: the
--                                  simulator and its budget cross untouched,
--                                  and forgetting the cost is a separate step
--                                  `UC.Model.Family.Negligible` inhabits it at
--                                  the machine family, and its §1 acceptance
--                                  tests are `UC.Approximate.LocalTests`
--                `UC.Family.Negligible.Setup`
--                                  `ucSetupᴺ`: the same four fields at
--                                  `Observationᴺ`, so the negligible tier
--                                  INHERITS `Abstract2` too, and `≈ℰᴺ⇒≤UC`
--                                  carries its agreement into that order —
--                                  `UC.Family.Vanishing` is the counterpart at
--                                  `Observation^ω`, so `absorb`'s result
--                                  reaches the inherited order without
--                                  re-basing `absorb` itself
--   quantitative `Approx.Space`    `Approx`: approximate spaces and
--                                  nonexpansive maps, `Approximation` packaged
--                                  as a category, `Approx.Forget` the two ways
--                                  out of it (`F₀`, `F₊`) and
--                                  `Approx.Separating` why they differ
--                `UC.Quantitative` `QUCSetup`: the same computational data at
--                                  an `Approx`-valued presheaf, its two
--                                  ordinary setups, and `_≈ᵁ[ ε ]_`, the
--                                  contextual comparison with the error kept.
--                                  `.Witness` is `At`/`Witness` and their
--                                  composition, `.Bridge` the exact links to
--                                  the two inherited theories
--                `Approx.Controlled`
--                                  the resource-aware half: maps carrying an
--                                  error control, `Approx.Filtered` the second
--                                  index (which allowance admits which test),
--                                  `Approx.Schedule` the schedule-valued errors
--                                  and allowance reindexing as a control, and
--                                  `Approx.Small` the existential collapse at a
--                                  class of small errors — distinct from `F₊`
--                                  and the source of `UC.Approximate.Local`'s
--                                  `_∼ᴺ_`, whose equivalence is now that one —,
--                                  and `Approx.Controlled.Forget` the zero-error
--                                  one, which needs no restriction on controls
--                `UC.Quantitative.Query`
--                                  the query-sensitive model those hold: tests
--                                  compared through CERTIFIED closures at a
--                                  schedule read off the closure's allowance,
--                                  a filtered presheaf over the BUDGETED
--                                  morphisms, with `UC.Budget`'s two
--                                  absorptions separated into the exact one
--                                  and the bound.  `UC.Model.Quantitative`
--                                  instantiates it, and `.Contextual` is the
--                                  comparison over it — `ctx-absorb`, the one
--                                  principle behind both existing schedule
--                                  substitutions.  The family models,
--                                  collapses and the migration are NOT built
--                                  (`docs/quantitative-uc-setup-plan.typ` §§8–10)
--   model        `UC.Machine`      `𝒫ᴵ`, processes on `Iface`s, the ticked
--                                  verdict interface, the observation at `Dₚ`
--                `UC.QueryBound`   the amortised-potential certificate — a
--                                  query bound with content, inhabited at a
--                                  wire, at a closed process and, by
--                                  `qb-oneCall`, at any protocol whose step
--                                  factors through `OracleCall.fromCall`; what
--                                  it means on a run is `UC.QueryBound.Counting`, and
--                                  `UC.QueryBound.Compose{,.Step,.Laws}` is
--                                  where it multiplies along composition, which
--                                  `UC.Machine.Budget` feeds to the resource
--                                  doctrine; `.Step`'s `Nᶜ`/`unfoldᶜ`/`eq-∘ᶜ`
--                                  are also how a consumer reads a composite's
--                                  BEHAVIOUR off without unrolling a trace
--                                  (`Examples.CoinToss.Ideal.Hybrid`).  Only
--                                  the counting theorem is
--                                  re-exported below: the composition line
--                                  spends the `Proc` inversion per field (its
--                                  headers carry the measured costs), which no
--                                  consumer of this entry point should pay
--                                  unless it is assembling a `Budget`
--                `UC.QueryBound.Exact`
--                                  the EXACT counterpart: a per-step ledger
--                                  equation, so that "this process performs a
--                                  query" is expressible and not just "at
--                                  most `c` of them"
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
--                                  `PrAgree`); `UC.Seam.Grounding` names what
--                                  the instance owes, and `UC.Seam.Audit` is
--                                  `UC.Audit` applied to the sealed model
--                `UC.Seam.Grounded`
--                                  and what discharges it at the trivial
--                                  grade: `SubBlind`, `StratIsEnv` and with
--                                  them `UnitGrade`; also `closedᵒ`/`stageᵒ`,
--                                  the trivially graded images every consumer
--                                  downstream of the collapse is stated at
--                `UC.Graded`       the same images at a NONTRIVIAL grade: a
--                                  `Proc A (X ⊗ᴵ B)` is a graded hom
--                                  (`Seal.gradedᵒ`) and a machine-level
--                                  factoring of it through a simulator is an
--                                  emulation, with no error.
--                                  `UC.Seam.Graded` attaches the simulator's
--                                  query bound, which is what the graded carry
--                                  consumes; `Examples.HashForward` is the
--                                  EXACT application and
--                                  `Examples.ROCommitment` the approximate one
--                                  (both corruption halves, `.Hiding` the
--                                  receiver's) — same images and the same
--                                  certificates, with the error priced in
--                                  `GamePlaying`.  `ext-graded`, `graded₂-∘`
--                                  and `sub-graded₂` are the same readings for
--                                  a COMPOSED system — a stage on top, a
--                                  closed process under, a joint simulator in
--                                  front — which `Examples.CoinToss.Ideal.UC`
--                                  consumes
--                `UC.Factor`       `factorᵖ`/`liftᵖ`: the UC-object image of
--                                  `_∘ᵖ_` factors on the nose, so a
--                                  sub-protocol emulation lifts to the
--                                  composed system by `UC-compose` (the
--                                  retraction-conjugated `sub` congruence is
--                                  `Abstract2.Factor`)
--                `UC.Seam.Audit.Prefix`
--                                  the BUDGETED route's consumer end:
--                                  `uc-audit-bounded` turns an ideal monitor
--                                  bound into the real system's own probability
--                                  across a budgeted emulation, the simulator's
--                                  initialization tolerated as a prefix and its
--                                  queries charged.  No event class is on the
--                                  route: `sim-prefixed` is the one-sided mass
--                                  consequence, `bounded-carry` is where the
--                                  route's actual premises show,
--                                  `UC.Seam.Audit.Context`'s `extract-obs` is
--                                  its numerical half and `UC.Seam.Slide` the
--                                  one place the simulator slide is spelled
--                                  (`docs/direct-extraction.md`)
--                `UC.Saturated`    the saturated form of a concrete safety
--                                  bound — one slack per polynomial allowance,
--                                  at the vanishing grade and at the
--                                  negligible one, with the invariance proved
--                                  for each
--                `UC.Asymptotic`   the consumer end: an emulation FAMILY, and
--                                  the two ways a bound crosses it — graded
--                                  (`simCost` charged) and probabilistic (the
--                                  trivial-grade collapse into `UC.Saturated`).
--                                  `UC.Asymptotic.Audit` states the graded one
--                                  as `uc-audit-carryᵈ`, at the test, closure,
--                                  monitor and budget witness directly
--                                  (`docs/consumer-migration.md`)
--                `UC.Asymptotic.Contextual`
--                                  the ONE quantitative relation, `_≈ctx[_]_`,
--                                  on families of graded morphisms with the
--                                  context's certificates read into the
--                                  allowance, and the simulator-bearing witness
--                                  `_≤UC^ωᵉ_` (`UC.Asymptotic.Family`'s
--                                  `_≈ᶠ[_]_`/`_≤UC^ωⁿ_` are its unit-grade
--                                  aliases and specializations)
--                `UC.Asymptotic.Compose`
--                                  its composition laws with the error
--                                  retained: `≤UC^ωᵉ-trans` and `UC-composeᵉ`,
--                                  each with its exact allowance substitution
--                                  (`docs/quantitative-family.md`), and
--                                  `≈ctx-dom`/`≤UC^ωᵉ-dom`, which plug a
--                                  rate-zero process under the domain for
--                                  free.  Its consumers are
--                                  `ChimericLedger.FactorEps`, which lifts a
--                                  premise through a factoring,
--                                  `Examples.CoinToss.Compose`, which stacks a
--                                  protocol on a realized one, and
--                                  `Examples.CoinToss.Ideal.Compose`, which
--                                  closes the comparison boundary
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
-- The inherited layer's own preservation theorem lives there too, not here:
-- `Abstract2.Action` is the environment presheaf's action read as `run` and
-- `regradeEnv` at any `UCSetup`, `UC.Robust` is `SaturatedProperty`/`Robust`/
-- `uc-preserves` over that action with an admissibility class and its
-- `ClosedUnder` obligation, `UC.Robust.Selected` a selected class with a real
-- closure proof, and `UC.Robust.Model` runs them at the machine model
-- (`docs/uc-presheaf-preservation-plan.md` §2, §3.1).
--
-- Everything is `--safe --without-K`; the `Dₚ`-facing modules add
-- `--guardedness` and nothing adds anything else.  In particular there is no K
-- island; `UC.Environment`'s header says why the reference arc needed one.

module CategoricalCrypto.UC where

open import CategoricalCrypto.UC.Approximate public
open import CategoricalCrypto.UC.Asymptotic public
open import CategoricalCrypto.UC.Asymptotic.Audit public
open import CategoricalCrypto.UC.Asymptotic.Compose public
open import CategoricalCrypto.UC.Asymptotic.Family public
open import CategoricalCrypto.UC.Budget public
open import CategoricalCrypto.UC.Core public
open import CategoricalCrypto.UC.Machine public
open import CategoricalCrypto.UC.Machine.Bridge public
open import CategoricalCrypto.UC.Machine.Dominated public
open import CategoricalCrypto.UC.Machine.Grading public
open import CategoricalCrypto.UC.Machine.Plug public
open import CategoricalCrypto.UC.QueryBound public
open import CategoricalCrypto.UC.QueryBound.Counting public
open import CategoricalCrypto.UC.QueryBound.Exact public
open import CategoricalCrypto.UC.Saturated public
open import CategoricalCrypto.UC.Seam.Audit.Context public
open import CategoricalCrypto.UC.Seam.Audit.Prefix public
open import CategoricalCrypto.UC.Factor public
open import CategoricalCrypto.UC.Graded public
open import CategoricalCrypto.UC.Seam.Graded public
open import CategoricalCrypto.UC.Seam.Grounded public

-- Closure-only: the negligible tier's acceptance tests (leaf, nothing to open).
import CategoricalCrypto.UC.Approximate.LocalTests

-- …and the quantitative tier: parameterized by an error algebra and a
-- `QUCSetup`, so imported rather than re-exported, `Bridge` reaching the rest.
import CategoricalCrypto.Approx.Controlled.Forget
import CategoricalCrypto.Approx.Filtered
import CategoricalCrypto.Approx.Schedule
import CategoricalCrypto.Approx.Separating
import CategoricalCrypto.Approx.Small
import CategoricalCrypto.Approx.Small.Controlled
import CategoricalCrypto.UC.Quantitative.Bridge
import CategoricalCrypto.UC.Audit.Canonical
import CategoricalCrypto.UC.Family.Negligible.Setup
import CategoricalCrypto.UC.Family.Vanishing
import CategoricalCrypto.UC.Quantitative.Contextual
