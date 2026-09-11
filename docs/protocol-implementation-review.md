# Protocol rewrite: remaining review work

Follow-up review of source at `6f48aa5d`, the proposal documents at `3d7d9305`,
and the real-ledger corollary added in `950ec080`. This document keeps only
remaining work and the constraints needed to implement it. The original review
is available in commit `97063c50`.

## Current scope and target

The branch proves a **unit-grade, pointwise-UC-to-negligible-POV theorem**.
The designated ideal audit supply, allowance-dependent saturation, and direct
negligible transfer are implemented. `ChimericLedger.Real.ledger-pov` additionally
supplies totality and truthful auditing for the ledger over a dead-free hash
implementation, assuming ledger-level pointwise UC emulation.

The remaining target is an **asymptotic-family, nontrivial-grade,
simulator-costed UC-to-POV theorem**. It should consume the actual ideal birthday
bound and a genuine family UC premise, retain the required negligible error
evidence, and conclude a real trajectory bound at each polynomial allowance.
The present special case is valid; it does not establish that more general result.

Source paths below are relative to `src/CategoricalCrypto/`. Line references
are at `6f48aa5d`, except references to `Real.agda`, which are at `950ec080`.
The proposed interfaces are schematic, not existing Agda declarations.

## 1. Replace pointwise agreement with the intended family premise

**High: remaining scope/integration gap.** `UC/Asymptotic.agda:71-73` defines
`R ≤UC^ω I` as a separate single-level inherited emulation for every `n`, not
as the relation of `UC.Model.Family`. With totality, `uc-agree` derives direct
agreement at every level; `uc-≈negl` can then choose any positive negligible
slack (`UC/Asymptotic.agda:79-92`).

This excludes systems whose verdict probabilities differ by `2⁻ⁿ`: they are
negligibly different but not arbitrarily close at every fixed `n`. The current
theorem obtains negligible security from a stronger pointwise premise rather
than from asymptotic UC.

### Concrete steps

1. Keep the existing theorem as a pointwise/unit-grade specialization. Name or
   document its premise accordingly; do not silently reinterpret `_≤UC^ω_` as
   the relation of the constructed family setup.
2. Build a separately named negligible family observation and instantiate the
   inherited UC machinery at it. Use the local-instance approach in section 4
   before considering changes to the qualitative core.
3. State the target error quantifiers explicitly. To retain the current
   `SaturatedHitᴺ` conclusion, carry an allowance-uniform quantitative error
   witness through emulation and simulator composition. Per-context negligible
   agreement alone does not supply that witness; section 4 identifies the choice.
4. Prove frontend quantitative ingestion into the family contextual relation
   using bounded-context domination at the actual model objects. Supply the
   family counterpart of the inherited-relation bridge, not just a citation to
   the single-model theorem. For the seal-object mismatch, first investigate
   exporting object/hom transport witnesses from the existing seal. If those
   cannot express the needed transport, state domination at the underlying
   machine objects and transport it once. Do not assume the missing lift.
5. Assemble a second ledger theorem consuming the family premise and its
   retained error evidence. Keep the existing pointwise theorem unchanged.

**Acceptance criteria:** the new negligible relation admits a one-shot `2⁻ⁿ`
difference and rejects a one-shot `1/(n+1)` difference. The final theorem
consumes that relation or an explicitly stronger uniform quantitative refinement;
it must not obtain negligible error solely from agreement at every positive
error at fixed `n`.

## 2. Connect the carried event to the real monitor probability

**High: the simulator-costed route stops short of probability extraction.**
`UC/Audit.agda:107-123` defines `absorb s cs 𝔉` as the pullback of the ideal
event class. Its closure proof returns the membership witness unchanged. That
is valid, but does not prove that a predetermined real monitor lies in the class.

`ChimericLedger.EndToEnd.ledger-audit-carry` concludes a bound for that
simulator-dependent class (`Examples/ChimericLedger/EndToEnd.agda:139-147`).
The extraction theorem's existing witness establishes membership in
`watched R badR`, not in the pullback (`UC/Seam/Audit/Bounded.agda:109-115`).
The missing membership is application work; `absorb-absorbs` is not its substitute.

### Concrete steps

1. State the missing inclusion/extraction lemma at the actual real monitor and
   audit-instrumented strategy. Its conclusion should establish membership in
   the carried event at the adjusted budget, or a one-sided comparison sufficient
   to extract the probability bound.
2. For the smaller unit-grade bridge, add a new event class tolerating an
   almost-surely-total silent prefix, then prove ideal supply and real extraction
   for it. Keep the exact `watched` interface and its proved consumers intact.
3. Alternatively, make approximate membership retain an explicit error `η`:
   witness a monitored ideal strategy, its budget certificate, and one-sided
   observation domination up to `η`. Supply then yields `ε + η`. Prove how
   these witnesses compose and include `η` in the final negligible slack. Do
   not hide an arbitrary vanishing error in membership or assume uniform
   negligibility over an allowance.
4. Prove the concrete monitoring contexts satisfy the new inclusion/comparison,
   including simulator composition. For interactive simulators, use section 3;
   initialization-prefix tolerance alone is insufficient.
5. Compose ideal `audit-target`, generic `audit-carry`, real probability
   extraction, and the truthful audit-to-trajectory theorem in one consumer.

**Acceptance criteria:** for an arbitrary permitted real monitoring strategy,
derive its actual `Pr`/`PrHit` inequality. No membership or robustness premise
may stand in for an unproved ledger-specific inclusion. The bound must account
for instrumentation, simulator cost, and any membership approximation error.

## 3. Exercise the graded carry at a nontrivial simulator interface

**High scope issue.** Both current application relations inflate their endpoints
using `ιᴳ`, including the budgeted relation (`UC/Asymptotic/Audit.agda:41-43`).
The budgeted simulator is therefore `unit ⇒ unit`. A positive query-budget
certificate is an upper bound, not evidence that a scalar has an oracle-facing
interface or actually spends oracle queries.

`scalar-blindᵒ` is expressly restricted to `unit ⇒ unit`
(`UC/Seam/Grounding/Prefix.agda:113-122`). Prefix congruence propagates a supplied
prefix witness; it cannot turn arbitrary answer-dependent interaction into
silent initialization. The general `UC.Audit.audit-carry` retains the simulator
and requires `Absorbs` evidence instead of declaring its interaction silent.

### Concrete steps

1. Narrow [the prefix proposal](prefix-tolerant-audit-plan.md) to the budgeted
   unit-grade probability bridge. Its claim to handle a simulator that
   "actually burns oracle queries" is not supported by the existing application
   types. Almost-sure totality does not guarantee exact `≈ₚ` equality, but
   exact equality is not impossible for every prefix either.
2. State a separate application at explicit nontrivial grades: process families
   of the generic `A ⇒ X ⊛ B` shape and simulator families `Y ⇒ X`. Identify
   the simulator's ports and which public audit answers remain under ledger
   control. If the relevant interface is hidden inside closed `Sys`, expose it
   at the appropriate resource boundary instead of merely adding a unit grade.
3. Supply a polynomial query allowance for the simulator family and prove the
   composed monitored experiment's budget using `qb-∘`, the grading budget
   laws, and `simCost`. Query bounds are not runtime bounds; no PPT claim
   should be inferred without an additional computational-cost doctrine.
4. Show operationally that a simulator-composed real monitoring context is an
   admissible ideal monitored experiment at that budget. Use prefix tolerance
   only for initialization; retain actual simulator interaction in the ideal
   experiment.
5. Apply the generic graded carry, section 2's probability extraction, and the
   real truthful-audit connection. This is the nontrivial-grade extension,
   rather than a larger numerical bound on the existing unit-grade theorem.

**Acceptance criteria:** include a small example with an inhabited
simulator-facing port whose simulator actually performs a query. Prove the
query's occurrence/count, not just a positive upper bound. The probability
theorem must apply without identifying the simulator with a silent scalar, and
its accounting must include the interaction.

## 4. Prefer a local negligible observation; resolve uniformity explicitly

**Medium: design recommendation with a substantive quantifier choice.**
[The graded-observation proposal](graded-observation-redesign.md) treats
negligible observation as necessarily a core-interface redesign. But
`UC.Core.Observation` already accepts an arbitrary equivalence
(`UC/Core.agda:80-93`). A second local instance can use:

```text
μ ∼ᴺ ν = exists negligible δ,
          for every index i, μ(i) is δ(κ(i))-close to ν(i).
```

Zero error, symmetry, and `Negligible-+` give the equivalence laws; exact
respect of hom equality gives observation congruence. `Induced` does not
construct this witness-retaining relation, but that limits the helper, not
`Observation` itself.

Keep the following contracts distinct:

```text
local negligible observation:
  for every context, there exists a negligible error for that context;

current _≈ℰⁿ_:
  one global budget-indexed error bounds every context;

current SaturatedBoundedᴺ:
  for every polynomial allowance, one negligible slack covers all its strategies.
```

The global relation (`UC/Family.agda:279-298`) should imply local contextual
agreement by specialization to each context's carried allowance. Neither the
converse nor the move from per-context error to allowance-uniform saturation
follows automatically.

### Concrete steps

1. Add a local `Observationᴺ`/UC instance on the existing family category, reusing
   the generic environment presheaf and inherited UC machinery without changing
   the qualitative core.
2. Prove the one-way bridge from `_≈ℰⁿ_` into its contextual agreement. Do not
   identify the relations without a separate uniformization theorem.
3. Choose the public security contract. To retain allowance-uniform saturation,
   keep uniform evidence in a quantitative refinement of UC and prove its
   simulator/composition laws. A per-adversary negligible property can instead
   match the local qualitative relation, but it is a different theorem and must
   be stated separately, not substituted for `SaturatedBoundedᴺ`.
4. Consider a grade-indexed core only if these local constructions demonstrate
   a concrete need to retain and compose quantitative evidence generically.
   Reusing `Induced` alone is not sufficient justification for a core rewrite.

The probability-free `SaturatedProperty` / `Robust` / `uc-preserves` API also
remains absent. Add it independently by defining an observation-invariant
property, quantifying robustness over closing contexts, and sliding the
simulator into the test. Reuse the inherited relation/bridge, not another UC
metatheory. This generic theorem does not discharge the concrete monitor
inclusion or error-uniformity obligations.

## Suggested order and completion test

1. Fix the scope labels in the two continuation proposals and state the target
   quantifiers and nontrivial interfaces before proving more lemmas.
2. Build the local negligible observation and its one-way bridge. In parallel,
   prove the unit-grade prefix-tolerant extraction as a separately scoped result.
3. Carry the chosen uniform quantitative evidence through family emulation and
   composition, and finish frontend-to-model ingestion.
4. Prove monitor admissibility for a genuinely interactive simulator and combine
   that graded carry with real probability extraction.
5. Instantiate the complete chain at the actual ideal birthday theorem and the
   real-ledger shape, retaining serialization and liveness assumptions explicitly.

The final public theorem should start from a genuine emulation in the intended
family model, the actual ideal bound, and appropriate admissibility evidence.
At each polynomial allowance it should bound the real monitored trajectory by
the simulator/instrumentation-adjusted birthday term plus a negligible slack
with the chosen uniformity. No direct `Agreeˢ`, unproved event-membership
inclusion, or stronger pointwise-equality premise should stand in for those steps.

A particular hash implementation's UC realization may remain a visible premise.
The current real-ledger corollary assumes emulation at the ledger; deriving that
from a hash-level emulation via family composition is useful integration work,
not a requirement to prove a new cryptographic construction. Neither a named
Merkle-Damgård realization nor the optional confidential ledger is a prerequisite
of this review's completion goal.

## Verification boundary

The follow-up typechecked `ChimericLedger.EndToEnd` and `UC.Model.Family` at
`6f48aa5d`, without the flagged warning classes. The end-to-end dependency rebuild
exhausted a 3 GiB heap and passed with `-M8G -H1G`; the full repository closure
was not checked. The later `950ec080` real-ledger corollary was inspected, not
re-typechecked in this review. Future completion claims should check the final
consumer and its closure at the revised statements, not only their component
types or the already-checked pointwise specialization.
