# Protocol rewrite implementation review

Reviewed on 2026-09-11 at `6256a140`, against the `string-diagram-solver`
merge `f71a2381`. Scope: the actual implementation added after that merge,
compared with `protocol-rewrite.md`, `protocol-rewrite-theory-review.md`, and
`protocol-rewrite-abstraction-notes.md`. This is a review output, not an
implementation plan already executed.

## Verdict

The branch is a largely successful foundational rewrite, but not yet a complete
implementation of the security-property preservation vision. The main remaining
problems are theorem statements and their integration, not proof style. Two
interfaces need correction before further proof work: `AuditBound` does not
identify the intended audit event, and `SaturatedRespects` is false as stated.
The distinction between vanishing and negligible error also needs to be enforced
at the property-preservation boundary.

Source references below are relative to `src/CategoricalCrypto/` at the reviewed
commit; line numbers refer to that snapshot.

## 1. High: the audit premise bounds arbitrary verdicts

`UC/Audit.agda:78-81` defines `AuditBound f ε` by bounding the true mass of
**every** budgeted test. There is no designated audit monitor, bad-event predicate,
or requirement that the test truthfully report a failure. A test can report
`true` without querying the process.

The proved `UC/Seam/Audit/Bounded.agda:58-107` makes the consequence explicit.
Specialize `auditIsBounded` to `bad = λ _ → out true`. This transformation
preserves every query bound. Instantiate the resulting `Bounded` at any `q`
and `d = out true`: its direct probability is one. Thus, at the implemented
trivial-grade embedding of any protocol, `AuditBound` implies `1 ≤ ε q` for
every `q`. Even a protocol with `dead` steps has this consequence: the experiment
executes no step, and protocol initialization is a supplied state. This claim
does not extend indiscriminately to arbitrary machines with lossy initialization.

`audit-carry` (`UC/Audit.agda:104-133`) is a valid simulator-sliding proof about
this overly strong premise. It cannot transport a small ledger birthday/audit
bound through that interface. The existing bridge extracts a protocol bound
**from** `AuditBound`; it does not construct `AuditBound` from `POVaudit`.

**Required correction:** distinguish the trusted observable audit event from the
adversarial context around it, and prove closure of the permitted contexts under
simulator composition. An ordinary ideal `POVaudit` theorem must actually supply
the corrected premise. The previous claim that the graded UC-to-POV path was
closed is withdrawn; proving `AuditIsBounded` alone did not close it.

## 2. High: saturation has the wrong quantifier order

`UC/Saturated.agda:62-65` asks for one slack uniform over all query counts:

```text
exists ν tending to zero,
  for every n, q, and strategy d with asks≤ q d,
    watched probability ≤ ε n q + ν n.
```

But `SaturatedRespects` (`UC/Saturated.agda:80-86`) assumes only
`VanishingBound δ`: the difference vanishes along each polynomial allowance.
This cannot yield a slack uniform over arbitrary, potentially exponential `q`.

A mathematical counterexample uses deterministic, terminating protocols on unit
queries and Boolean answers. `P n` always answers false; `Q n` does so until
query `2^n`, when it answers true. Let `δ n q` be zero below that threshold and
one at or above it. Below the threshold all transcripts agree, including against
randomized adaptive strategies; above it either verdict's advantage is at most
one. Every polynomial allowance is eventually below the threshold, so
`VanishingBound δ` holds.

A query-preserving watch follows the supplied strategy's queries and coin nodes,
replacing its terminal verdict with whether a true answer was seen. Its
probability against `P` is always zero. A strategy making `2^n` queries to `Q`
has watched probability one. With `ε = 0`, the proposed conclusion therefore
requires `ν n ≥ 1` for every `n`, contradicting convergence to zero.

**Required correction:** quantify over polynomial allowances before choosing a
slack, allowing that slack to depend on the allowance, or strengthen the premise
to uniform control over all query counts. `SaturatedRespects` has no inhabitant;
it is not merely awaiting the arithmetic lemmas advertised in its comment.
`UC/Approximate.agda:118-123` already records the correct allowance discipline.

## 3. High: negligible security is lost at the qualitative boundary

`SaturatedBounded` and `SaturatedHit` use `_→0`, not `Negligible`
(`UC/Saturated.agda:63,70`), despite their description as
"POV-modulo-negligible". They admit inverse-linear excess probability.

Changing that predicate alone is insufficient. `UC/Family.agda:156-186`
constructs qualitative observation as eventual closeness at every constant
positive error: **vanishing advantage**, not negligible advantage.
`absorb-negl` (`UC/Family.agda:260-263`) is a valid sufficient-condition theorem
into that same weaker relation; it does not strengthen the relation itself.

An equivalence that forgets inverse-linear differences cannot generally preserve
a property allowing only negligible excess. For example, a one-shot observable
bad bit with probability `1/(n+1)` differs vanishingly from an always-safe bit,
but does not satisfy a zero baseline bound modulo negligible slack.

**Required correction:** align the property and the relation transporting it.
A vanishing model may remain useful alongside a negligible model. Preserving
negligible security requires a suitable negligible observational relation or a
stronger quantitative carry premise that retains the error witness. Merely
passing a negligible bound through `absorb-negl` does not establish preservation
of all negligible-slack properties by the resulting qualitative UC relation.

## 4. Medium: property preservation is not integrated end to end

The abstraction notes' probability-free `SaturatedProperty` / `Robust` /
`uc-preserves` API and theorem are absent. The generic theorem should be a small
generalization of the existing simulator-sliding argument; the substantial
unresolved work is supplying useful concrete robust properties.

The remaining integration gaps are:

- `Examples/ChimericLedger/Carry.agda:36-46` names direct `Agreeˢ` as `Emulᴸ`.
  Its public carry premise is not simulator-bearing UC emulation.
- `UC.Family.Monoidal` supplies a genuine `UCSetup`, but its bridge from the
  family bound-ingestion relation to inherited agreement is described rather
  than proved there (`UC/Family/Monoidal.agda:14-19`). The single-model bridge
  does not itself provide the family theorem.
- `UC.Machine.Dominated.dominated` proves bounded-context domination, but the
  frontend-to-family ingestion path is not assembled into a consumer theorem.
- The ledger birthday theorem is proved at a fixed hash width. There is no
  completed family application proving its `NegligibleBound` and transporting
  the resulting property through UC.

These are omissions, not refutations of the categorical constructions. They are
also why a collection of closed component proofs is not yet a completed
security-property pipeline.

## Completion goal: an end-to-end theorem

The acceptance goal is a public theorem for the ledger example that starts with
the actual ideal birthday/audit result and a genuine UC-emulation premise, then
concludes a real-system POV bound modulo negligible error at every polynomial
allowance. Its statement must use the repaired notions from findings 1-3, not
silently assume the desired direct-run agreement or an uninhabitable audit bound.

The intended shape is schematic, not an existing Agda declaration:

```text
proved ideal birthday/audit bound
  + serialization and security-parameter hypotheses
  + real ≤UC ideal in the intended asymptotic model
  + admissibility / polynomial simulator-cost evidence
  + the real system's truthful-audit-to-trajectory connection
    implies
for each polynomial allowance p,
  there is negligible ν_p such that every strategy with at most p(n) queries
  has real POV-failure probability bounded by the appropriately
  simulator-adjusted birthday bound plus ν_p(n).
```

Acceptance requirements:

1. Instantiate the ideal side with the proved ledger theorem, retaining its
   injective-serialization assumption. Specify how hash width grows with the
   security parameter and prove negligibility of the resulting birthday bound
   at every polynomial allowance.
2. Construct the intended machine-family UC setup and supply the relation
   bridges needed to use inherited UC metatheorems. Where a protocol bound is
   lifted to bounded machine contexts, consume the proved adequacy/domination
   results rather than assume that lift.
3. Preserve a property of the designated observable audit event under admissible
   contexts, including the simulator-absorbed context. Prove robustness for the
   concrete ideal property; do not require a bound on arbitrary true verdicts.
4. Charge simulator and audit instrumentation costs explicitly. Establish the
   negligible-slack closure at each polynomial allowance with the corrected
   quantifier order and security relation.
5. Recover the real trajectory statement through the real implementation's
   truthful audit connection. UC alone does not identify internal state
   trajectories of real and ideal machines.
6. Expose and typecheck the assembled theorem at the public consumer surface,
   with no remaining bridge hypotheses standing in for the work above.

The theorem may assume a genuine UC emulation between the chosen real and ideal
families: proving a particular cryptographic construction realizes the ideal is
a separate obligation unless explicitly included in scope. That assumption must
remain visible and must not be replaced by direct `Agreeˢ`. Nor does this goal
assert that the two ledger variants emulate each other; the chimeric attack
precludes treating the insecure variant as a secure refinement without further
changes. The optional confidential-ledger construction is not made a prerequisite
by this review.

## Reconciled implementation status

The following are proof terms or constructions, not just stated types:

| Component | Current status |
|---|---|
| Direct protocols, executable pins, live genesis | Implemented |
| `Dₚ`, machine category, trace laws, G-construction, monoidal bundle | Implemented |
| `morphism-∘`, `PrAgree`, strategy/environment adequacy | Proved |
| Query counting and composition; guarded context budget | Proved; the zero-budget defect is repaired |
| `ContextDominated` | Proved for `QB`-certified contexts |
| Intended qualitative UC model and inherited relation bridge | Constructed/proved, using `≈ᵁ` rather than the weaker bare kernel |
| `IotaBlind`, `EnvAsCtx`, `StratIsEnv` | Proved |
| Repaired `SubBlind`, `UnitGrade` | Proved with `SimTotal` and `TotalRun` restrictions respectively |
| `AuditIsBounded` | Proved, but does not repair finding 1 |
| `TrajectoryFromAudit`, ledger birthday `target` | Proved; the birthday theorem retains injective serialization |
| Family category, monoidal structure, `ucSetup^ω` | Constructed; integration in finding 4 remains |
| `SaturatedRespects` | Uninhabited and false as stated |
| End-to-end asymptotic UC-to-POV theorem above | Not implemented |

Two limitations should remain explicit without being mistaken for new proof
obligations. The protocol interpretation preserves composition, but not the
unrestricted machine identity, so "semantics functor" is not literal. The
unit-grade theorem has necessary totality restrictions; protocols permit `dead`,
and totality of protocol images requires the corresponding protocol premise.

Older status/pricing passages are historical evidence, not the current obligation
list. In particular, both "composition is still only stated" and "the graded
audit path is closed" are superseded, in opposite directions, by this review.

## Verification and limits

This review inspected source statements and proof terms. Targeted checks of
`UC/Saturated.agda` and `UC/Audit.agda` with
`pagda --useUntracked false check ... -- +RTS -M3G -H1G -RTS` passed without the
flagged warning classes. The full branch closure was not checked. The
counterexamples above were reasoned through against the source definitions,
not mechanized in Agda during the review. A checked type alias is not evidence
that it is inhabited, and a proved implication can still have an unsuitable
premise for its advertised application.
