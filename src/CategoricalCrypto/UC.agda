{-# OPTIONS --safe --without-K --guardedness #-}

-- The UC layer's entry point: one import for a consumer.
--
-- The layer is three tiers, and the split is the point.  The CORE is
-- qualitative: a monoidal category, whose tensor is the action of adversary
-- interfaces, and an equivalence on what closed runs show.  The ENRICHMENT
-- adds what a model may
-- know and general UC must not assume — a measurable error, a query budget, a
-- mass.  The MODEL is the `Dₚ` machine instance, where the enrichment is
-- discharged and the core's equivalence is CONSTRUCTED from rational advantage.
--
--   core         `UC.Core`         `Observation`
--                `UC.Environment`  the environment presheaf, `_≈ℰ_`,
--                                  `grade-stable`, and `tv₁-∘`, the slide by
--                                  which a stage of the process becomes a stage
--                                  of the test
--                `UC.Robust.Observation`
--                                  `SaturatedProperty`, `Robust` and
--                                  `robust-sub` at a monoidal base: the
--                                  ingredients of the carry with no probability
--                                  under it, where the simulator slides into
--                                  the test and an observation-invariant
--                                  property needs no budget to pay for it.  The
--                                  carry itself is the inherited layer's
--                                  `UC.Robust` (below)
--                `UC.Core.Bridge`  `StdUC` over the environment layer's own
--                                  presheaf, so the core's `_≈ℰᶜ_` IS the
--                                  inherited `_≈ᵁ_` and the inherited order
--                                  follows
--   enrichment   `UC.Approximate`  `ErrorAlgebra`, `Approximation`,
--                                  `ApproximateObservation`, `Induced`, `Mass`
--                `UC.Budget`       `Budget`, `ctxBudget` — the resource doctrine
--                `UC.Audit`        `AuditEvent`, the audit event a premise is
--                                  about, and `audit-carry`: a bound on it
--                                  across an emulation, the simulator absorbed
--                                  into the environment leg.  `carry-obs` is
--                                  that carry's structural content with neither
--                                  class nor budget on it, which is what a
--                                  direct consumer spends
--                `UC.Family`       the asymptotic constructor — `𝒞^ω` at a
--                                  parameterized index, and `absorb`, where a
--                                  vanishing bound BECOMES the core's `_≈ℰ_`.
--                                  `Famᴹ` makes the family's grades monoidal
--                                  by the budget's four unitor certificates,
--                                  and `ucSetup^ω` — so the INHERITED
--                                  metatheory runs at the asymptotic family
--                `UC.Family.Negligible`
--                                  the same layer's negligible tier: a second
--                                  `Observation` on `Fam` keeping the error
--                                  witness (`_∼ᴺ_`, `_≈ℰᴺ_`) and the one-way
--                                  bridge `≈ℰⁿ⇒≈ℰᴺ` into it.  It has no order
--                                  of its own: that was a renaming of the
--                                  core's, and is retired
--                                  (`docs/retirement-negligible-order.md`).
--                                  `UC.Model.Family.Negligible` inhabits it at
--                                  the machine family, and its §1 acceptance
--                                  tests are `UC.Approximate.LocalTests`
--                `UC.Audit.Canonical`
--                                  an audit emulation read as a cost-certified
--                                  witness for the INHERITED order: the
--                                  simulator and its budget cross untouched,
--                                  and forgetting the cost is a separate step
--                `UC.Family.Negligible.Setup`
--                                  `ucSetupᴺ`: the same four fields at
--                                  `Observationᴺ`, so the negligible tier
--                                  INHERITS `Abstract2` too, and `≈ℰᴺ⇒≤UC`
--                                  carries its agreement into that order —
--                                  `UC.Family.Vanishing` is the counterpart at
--                                  `Observation^ω`, so `absorb`'s result
--                                  reaches the inherited order without
--                                  re-basing `absorb` itself.  A quantitative
--                                  witness reaches it with its schedule KEPT
--                                  by `UC.Asymptotic.Family.≤UC^ωᵉ⇒≤UCᴺ`,
--                                  where `≤UC^ωᵉ⇒≤UCᵁ` spends it
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
--                                  the two inherited theories, and
--                                  `.Observed` the setup an approximate
--                                  observation carries: the test presheaf,
--                                  `_≈ℰ[ ε ]_`, its collapse, and the two
--                                  recoveries of the qualitative theory
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
--                                  and the zero-error one is `F₀ᶜ` here, which
--                                  needs no restriction on controls
--                `UC.Quantitative.Query`
--                                  the query-sensitive model those hold: tests
--                                  compared through CERTIFIED closures at a
--                                  schedule read off the closure's allowance,
--                                  a filtered presheaf over the BUDGETED
--                                  morphisms, with `UC.Budget`'s two
--                                  absorptions separated into the exact one
--                                  and the bound.  `UC.Model.Quantitative`
--                                  instantiates it, `.Contextual` is the
--                                  comparison over it — `ctx-absorb`, the one
--                                  principle behind both existing schedule
--                                  substitutions — and `.Family` the FAMILY
--                                  tier over that comparison, `_≈ctx[_]_`,
--                                  `_≤UC^ωᵉ_` and their composition laws
--                                  (`docs/quantitative-family.md`)
--                `UC.Family.Quantitative`
--                                  the family tier's own instance: `Observed`
--                                  at `Famᴹ` over scalar errors, whose `F₊`
--                                  image is `ucSetup^ω` — so the two orders
--                                  coincide — while
--                                  `.Negligible.Quantitative` is the same
--                                  instance over SCHEDULE errors, collapsed at
--                                  `Negligible`, which reaches `ucSetupᴺ`'s
--                                  order ONE WAY only: the uniformization is
--                                  open (`docs/quantitative-uc-setup-plan.typ`
--                                  §8), as is the migration (§10)
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
--                                  spelling the 𝒢-tensor's action is stated in
--                `UC.Machine.Grading`
--                                  where a query-bound certificate about a
--                                  pinned relay meets the 𝒢-tensor's own
--                                  action, through `UC.Machine.Dictionary`'s
--                                  zigzags
--                `UC.Machine.Budget`
--                                  `budgetᴹ`: the enrichment's `Budget`
--                                  inhabited at `𝒢ₚᴹ`.  Not re-exported below
--                                  either — it is the one consumer that pays
--                                  for the composition line
--                `UC.Machine.Bridge`
--                                  `ContextDominated`, the interface to layer
--                                  1's concrete theorems
--                `UC.Machine.Dominated`
--                                  `dominated`: that interface DISCHARGED, via
--                                  the two-machine skeleton
--                `UC.Machine.Monitor`
--                                  the compiled readout: a process wrapping a
--                                  test so that what a context observes is an
--                                  accumulated EVENT, with the certificate
--                                  `κμ` it costs.  `.Agree` is its semantic
--                                  agreement — the compiled experiment at an
--                                  embedded strategy IS layer 1's run of that
--                                  strategy under the watch, a SPAN through
--                                  the reachable configurations rather than a
--                                  simulation either way
--                                  (`docs/event-bounds-in-setup.md` §2)
--                `UC.Seam`         where layer 1's runs meet an emulation: a
--                                  strategy as an environment and `Adequacy`
--                                  (`UC.Seam.Carry` turns run closeness into
--                                  `_≈adv[_]_`); `UC.Seam.Grounding` names
--                                  what the instance owes, and `UC.Seam.Audit`
--                                  is `UC.Audit` applied to the sealed model
--                `UC.Seam.Grounded`
--                                  and what discharges it at the trivial
--                                  grade: `SubBlind`, hence the collapse
--                                  `emulAgreeᵁ`; also `closedᵒ`/`stageᵒ`, the
--                                  trivially graded images every consumer
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
--                `UC.Factor`       `factorᵖ`: the UC-object image of `_∘ᵖ_`
--                                  factors on the nose, exposing the
--                                  sub-protocol's interface as a port
--                                  (`Examples.ChimericLedger.Transfer`)
--                `UC.Saturated`    the saturated form of a concrete safety
--                                  bound — one slack per polynomial allowance,
--                                  at the vanishing grade and at the
--                                  negligible one, with the invariance proved
--                                  for each.  Its remaining consumer is the
--                                  ledger's trajectory appendix; the headline
--                                  there is stated on the compiled monitor
--                                  instead (`UC.Quantitative.Hits.Hitsᴺ`)
--                `UC.Asymptotic`   the consumer end: an emulation FAMILY, and
--                                  how a bound crosses it — the trivial-grade
--                                  collapse into `UC.Saturated`
--                `UC.Asymptotic.Contextual`
--                                  `UC.Quantitative.Family` at the sealed
--                                  bundle: the ONE quantitative relation,
--                                  `_≈ctx[_]_`, and the simulator-bearing
--                                  witness `_≤UC^ωᵉ_` (`UC.Asymptotic.Family`'s
--                                  `_≈ᶠ[_]_`/`_≤UC^ωⁿ_` are its unit-grade
--                                  aliases and specializations)
--                `UC.Asymptotic.Compose`
--                                  that module's `Compose`: the composition
--                                  laws with the error retained, whose
--                                  consumers are `ChimericLedger.Transfer`,
--                                  which lifts a premise through a factoring,
--                                  `Examples.CoinToss.Compose`, which stacks a
--                                  protocol on a realized one, and
--                                  `Examples.CoinToss.Ideal.Compose`, which
--                                  closes the comparison boundary
--
-- The parameterized modules take a monoidal base and an observation and so are
-- imported directly rather than re-exported here; `𝒢ₚᴹ 0ℓ` and
-- `UC.Machine.Observationᴹ` are what to feed them at the model.
--
-- `UC.Model` is the layer's SECOND root, and it is deliberately not re-exported
-- here: it instantiates the INHERITED abstract theory (`UCSetup`/`Abstract2`
-- via `Standard2.StdUC`) at the same machine layer, behind an `opaque` seal —
-- the measured recipe without which the setup does not typecheck at all — so
-- its names only make sense inside that `open StdUC` discipline.
-- `UC.Core.Bridge` identifies the two — generic in the base and the
-- observation, and `UC.Model.Setup` IS that application at the seal — and
-- `UC.Seam.Grounded` above is where they meet.
-- `CategoricalCrypto` reaches both roots.
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
open import CategoricalCrypto.UC.Asymptotic.Compose public
open import CategoricalCrypto.UC.Asymptotic.Family public
open import CategoricalCrypto.UC.Budget public
open import CategoricalCrypto.UC.Core public
open import CategoricalCrypto.UC.Machine public
open import CategoricalCrypto.UC.Machine.Bridge public
open import CategoricalCrypto.UC.Machine.Dominated public
open import CategoricalCrypto.UC.Machine.Grading public
open import CategoricalCrypto.UC.Machine.Monitor public
open import CategoricalCrypto.UC.Machine.Plug public
open import CategoricalCrypto.UC.QueryBound public
open import CategoricalCrypto.UC.QueryBound.Counting public
open import CategoricalCrypto.UC.QueryBound.Exact public
open import CategoricalCrypto.UC.Saturated public
open import CategoricalCrypto.UC.Seam.Audit.Context public
open import CategoricalCrypto.UC.Factor public
open import CategoricalCrypto.UC.Graded public
open import CategoricalCrypto.UC.Seam.Graded public
open import CategoricalCrypto.UC.Seam.Grounded public

-- Closure-only: the negligible tier's acceptance tests, and the monitor
-- agreement (leaves, nothing to open).  The event-bound layer's compiled
-- instances — `UC.Quantitative.Hits`, `UC.Seam.EventTransfer`,
-- `UC.Quantitative.EventLift` — stay OUT of the closure because they carry
-- the ledger at one level in their own text; the ledger example's leaves are
-- what checks them (`docs/event-bounds-in-setup.md`).
import CategoricalCrypto.UC.Approximate.LocalTests
import CategoricalCrypto.UC.Machine.Monitor.Agree

-- …and the quantitative tier: parameterized by an error algebra and a
-- `QUCSetup`, so imported rather than re-exported, `Bridge` reaching the rest.
import CategoricalCrypto.Approx.Controlled
import CategoricalCrypto.Approx.Filtered
import CategoricalCrypto.Approx.Schedule
import CategoricalCrypto.Approx.Separating
import CategoricalCrypto.Approx.Small
import CategoricalCrypto.Approx.Small.Controlled
import CategoricalCrypto.UC.Quantitative.Bridge
import CategoricalCrypto.UC.Quantitative.Observed
import CategoricalCrypto.UC.Audit.Canonical
import CategoricalCrypto.UC.Family.Negligible.Quantitative
import CategoricalCrypto.UC.Family.Negligible.Setup
import CategoricalCrypto.UC.Family.Quantitative
import CategoricalCrypto.UC.Family.Vanishing
import CategoricalCrypto.UC.Quantitative.Contextual
