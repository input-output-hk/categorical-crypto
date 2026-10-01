# Event bounds in the setup's own vocabulary

Original baseline: `protocol-rewrite` at `9d33f783`. Paths below are relative to
`src/CategoricalCrypto/` unless prefixed with `docs/`. Recheck current signatures
before implementation. Definitions and theorem shapes marked as proposed are
specifications, not checked Agda declarations.

**Status.** The monitor-side certificate development this plan built (WP4: `compileᴹ`,
`eventRun`, `Monitor.Agree`'s `Watch`/`Span`/`tower`, `Monitor.Slide`, `EventLift.Cov`,
`Seam.EventTransfer`, `Dominated.CovCtx`/`eventSkeleton`) is retired; see "The two
readers are now one" below and `docs/monitor-flag-spike.md`. Sections citing those
names are the plan's record, not the current code.

## Goal

State and transport the ledger's observable event bound using the same processes,
certified contexts, and explicit-error comparisons as quantitative UC. The
headline remains a probability bound against polynomially query-bounded
environments, not merely an emulation statement.

The event to preserve is the one implemented by
`Examples.ChimericLedger.Observable.auditWatch`: when the interaction terminates,
report whether **any audit answer encountered during that interaction** reported
a total different from the initial total. This is an accumulated event, not
automatically a final-state check or a single final audit.

The construction must agree with the existing strategy-level watch before its
consumers are restated. If a single final audit is desired instead, make that a
separate semantic decision and account for its queries; do not introduce it as a
notation change. The state-trajectory property remains separate, with its existing
truthfulness and instrumentation obligations.

This proposal complements `docs/explicit-error-certificates-plan.md`: event
bounds consume explicit-error certificates. They need not pass through a
qualitative UC corollary or make `_≤UC^ωᵉ_` into a setup's order.

## Architectural clarification after the spike

The governing goal is:

> Give event bounds one quantitative transport theory. Preserve the useful
> strategy-level presentation, add a faithful context-level presentation, and
> prove the bridge before choosing what to retire.

This supersedes any reading of the plan as requiring every event to be an
ordinary monitor morphism or requiring deletion of the strategy-level layer
as evidence of success. Two projects were initially coupled too tightly:
consolidating event-bound transport and compiling a watch into an arbitrary
machine context. The latter requires substantive adequacy proofs; it is not
a routine prerequisite for using the former.

### Separate transport from the monitor compiler

The reusable transport argument needs an observed experiment, a lawful event
readout, an explicit-error comparison, and resource accounting. It does not
require that every event originate from a process `μ : B → B ⊗ Flag`.

The intended organization is:

```text
             Quantitative event-bound transport
                            ↑
                  Observed experiments
                   ↗                 ↖
       Strategy/watch reading   Monitored-context reading
                   ↖                 ↗
                     Adequacy bridge
```

The monitor compiler is one construction of event-observing contexts, not the
definition of an event bound. Keep the pure observation transports independent
of that compiler. Start with the concrete observation terms and small required
lemmas rather than introducing a large experiment/setup record.

### Preserve useful strategy structure

`auditWatch` has explicit event semantics, exact query preservation, and an
induction principle suited to the existing birthday proof. `Systems` and
`Watch` are not inherently architectural defects. The target is duplicated
security definitions and transport arguments lacking a proved connection, not
the existence of a strategy-level vocabulary.

Retain strategy definitions and lemmas when they serve probability proofs,
compiler adequacy, or the trajectory appendix. Retirement remains conditional
on genuine redundancy after migration; the retirement table is not a deletion
quota.

### Keep three resource quantities distinct

Name separately the original environment's ledger queries, internal queries
used to retrieve the flag, and the coarse compiled-context certificate used by
quantitative comparison. The spike's `2 · (c ⊔ 1)` certificate does not by
itself establish that monitoring intrinsically doubles the ledger-query cost.

Prefer a local accounting proof for this consumer. A port-sensitive or
distinguished-hole resource theory becomes a justified follow-up if multiple
consumers need it; it is not a prerequisite imposed by this plan.

### Acceptance is semantic agreement, not a representation change

The diagram to establish is:

```text
original interaction  →  watched event
         │                     │
         │ interpretation      │ probability bound
         ▼                     ▼
compiled context run  →  the corresponding event bound
```

Use equality or the precise one-sided inequality required by the theorem.
Neither a well-typed compiler nor a new property with a similar-looking type
establishes this diagram. Ordinary domination loses the connection between a
verdict and the event that produced it; the event-sensitive proof must retain
that connection.

### Two-stage delivery

**Stage A — consolidate the available mathematics.** Land `Upper` and its
explicit-error transport, factor the reusable event absorption/accounting from
`UC.Audit`, and keep the existing strategy-level ledger theorem operational.
State the intended contextual theorem and its bridge obligation precisely.
This stage is useful progress, but does not complete the contextual headline.

**Stage B — prove contextual adequacy for the audit event.** Establish monitor
agreement at embedded strategies, prove event-sensitive finite-strategy
decomposition, discharge the ideal contextual bound, and migrate the contextual
ledger transfer. Retire redundant infrastructure afterward.

The post-spike work package below specifies Stage B's obligations. A substantial
proof is justified if it establishes this concrete semantic connection and
reuses the existing machinery. The success measure is the checked connection
and its exercised consumer, not a short proof or disappearance of the old
presentation. A headline over all admitted machine contexts still requires
Stage B; the strategy theorem alone is not that result.

### The two readers are now one

The monitored-context reading and the state-event reading were two readers over
two hand-built `+1` certificates (`EventLift.Cov` for the monitor,
`StateEvent.Lift.FlagCert` for the flag wire). They are one reader now:
`UC.Machine.Monitor.flagReader` is the only readout, `HitsAt q r f μ` is
`BoundedAt q r (μ ∘ f) (flagReader B)`, and a monitored process is a flag-wire process —
`monitor-flag : monitorᴹ report ∘ u ≈ accᴹ report u ▷ reported report u`. The monitor's
lift `hitsᵘ` is therefore `stateLift` at `accᴹ`, read back at the watch by `flag-agree`,
and the strategy agreement `agree` is their corollary. Only the state-event certificate
survives, and since its one extra unit is the flag ask — inside the extracted strategy's
cap — the monitor costs no extra query: `hitsᵘ`'s premise is at the context's own cap
`q`. Details and the landing commits: `docs/monitor-flag-spike.md`.

## 1. Placement and required observation structure

A bare `QUCSetup` supplies approximate comparisons, not a Boolean event or a
probability readout. Start at the machine observation and reuse its existing
`Pr≤` operation. Put event-bound definitions in a focused module, tentatively
`UC.Model.EventBounds`, rather than adding machine-specific probability notions
to `UC.Quantitative.Contextual`.

Generalize an event transport lemma only when its actual readout and
comparison-compatibility assumptions are clear. No new one-sided
`Approximation` is needed merely to express an upper bound: an upper-bound
predicate is not a symmetric approximate equality.

### Finite-depth upper bounds

For an arbitrary `d : Dₚ Bool`, the library does not generally form its limiting
probability as a rational number. Use the existing finite approximants:

```agda
Upper d r = (k : ℕ) → Pr≤ k d ≤ r
```

Here `k` is observation depth, distinct from the security parameter and query
allowance. Spell out the types and qualified arithmetic in the implementation.

The elementary transport target is:

```text
d ≈ₚ[ε] e → Upper e δ → Upper d (δ + ε).
```

At each depth of `d`, the comparison supplies a depth of `e`; apply `Upper e δ`
there. This step does not itself need an extra positive slack. Any slack paid by
the separate strategy-to-context lift must remain visible.

**Do not replace an event bound by two-sided closeness to `returnₚ false`.**
`Upper botₚ 0` holds, while `botₚ ≈ₚ[0] returnₚ false` does not: approximate
equality compares both verdict masses. A one-sided comparison may be useful,
but the existing two-sided domination theorem cannot simply be specialized to a
false-answering process to prove the desired lift.

## 2. Compile the watch, including completion and query accounting

The candidate monitor is a stateful relay on the honest interface:

```text
μ : B → B ⊗ Flag.
```

This type is a starting point, not a completed implementation of `auditWatch`.
The watch can replace a strategy's `out` node directly; an ordinary relay does
not automatically know when an arbitrary test finishes.

Construct a monitored-test transformation, written schematically as
`compile μ E`, with explicit wiring for the ancilla and adversarial grade. It
must yield a test on the original process interface, so contextual comparison
can be applied to it. Define `eventRun f μ C` as the observation of this compiled
experiment, where `C` contains the original test, closure, ancilla, and budget
certificates. Do not leave a primitive `flag E` with unspecified semantics.

Prove the following before accepting the construction:

1. **Traffic agreement.** Honest-interface queries and answers are relayed as
   in the original experiment. Track the query associated with an answer so
   `reportsLoss` is evaluated exactly as in the watch.
2. **Completion behavior.** Specify how completion of the original test is
   detected and how its verdict is replaced by the accumulated flag. The test
   cannot forge or access the private flag port.
3. **Divergence behavior.** The construction does not turn a diverging watched
   interaction into a terminating verdict. A flag set before divergence is not
   automatically a reported `true` result.
4. **Strategy agreement.** At embedded finite strategies, the compiled
   experiment agrees with running the original process under `auditWatch d`.
   Reuse the existing protocol/machine transport to state this in the supported
   observation relation; do not assume structural machine equality.
5. **Budget accounting.** Certify the complete compiled test and its closure,
   including completion detection and flag reading. Establish the relationship
   with `Strategy.asks≤-watch`, not merely a certificate for the relay itself.

`QB 1 μ` is not by itself `QueryPreserving`: it is a rate certificate for a
process, not a proof that the compiled experiment spends the original allowance.
State and prove the actual allowance transformation. If it can be expressed as
`κμ(n,q)`, record its exactness or upper-bound status and polynomial closure.
If it depends separately on the test and closure budgets, retain those
arguments; do not assume it factors through `scale c (positive c′)`. In particular,
check zero allowance explicitly.

**Acceptance:** the monitor compiler has both semantic agreement and a proved
budget transformation. Typechecking a flag projection alone is insufficient.

## 3. Fixed-allowance and saturated event bounds

Let a base context `C` consist of:

```text
W, E : W ⊗ (X ⊗ B) → Ω, m : 𝟙 → W ⊗ 𝟙,
QB c E, QB c′ m.

allow(C) = scale c (positive c′).
```

For a closed process `f : 𝟙 → X ⊗ B`, define the proposed fixed-allowance bound:

```text
HitsAt q r f μ =
  ∀ certified base contexts C.
    allow(C) ≤ q → Upper (eventRun f μ C) r.
```

The allowance here is explicitly that of the original environment. The monitor's
instrumentation cost is recorded by its compiler and charged wherever a
comparison or lifting theorem needs it. If another allowance convention is
chosen, state it and prove its relationship to this one and to `asks≤ q`.

Families then have the proposed definitions:

```text
Hitsᶠ[ε] f μ = ∀ n q. HitsAt q (ε n q) (f n) (μ n).

Hitsᴺ f μ ε =
  ∀ p. Poly p →
    ∃ ν. Negligible ν ∧
      ∀ n. HitsAt (p n) (ε n (p n) + ν n) (f n) (μ n).
```

The slack is chosen after the polynomial allowance but before the level and
context. It is uniform over all admitted contexts within that allowance.

The restriction `allow(C) ≤ p n` is essential. Quantifying over every context
while replacing its error schedule by the constant `ε n (p n) + ν n` would
bound arbitrarily large contexts even when `p = 0` and is not the intended
statement.

Do not silently identify this capped-allowance presentation with a comparison
evaluated at the budget a context carries. Prove any required certificate
enlargement or supply an explicit error majorant. Monotonicity of an arbitrary
error schedule is not available by default; `NegligibleBound` alone is not a
license to move its argument along an inequality.

**Acceptance:** the fixed-allowance restriction and the slack quantifiers match
the claimed property. The relation to the old strategy-level property is proved
through the monitor agreement and the lifting results below, not a vocabulary
table alone.

## 4. Transport a bound through an explicit-error simulation

Start from the fixed-data comparison:

```text
f ≈ctx[ε] subᶠ s g,
```

with the existing certified simulator `s`. Prove transport for one monitored
context first:

1. Compile the real-side context, with its actual budget certificate, and apply
   the quantitative comparison at that budget.
2. Move the simulator into the ideal-side context using the existing absorption
   lemmas. Prove the equation between the two monitored experiments: the
   monitor is on the honest interface and the simulator on the grade, but the
   required rebracketing and compatibility still need proof.
3. Apply the ideal event bound to the resulting admitted context.
4. Use the one-sided observation transport from §1.

Name the two actual allowances: the comparison is read at the compiled
real-side allowance `rμ`, while the ideal event bound is read at the allowance
`rI` certified for the absorbed ideal context. The pointwise estimate is:

```text
real monitored upper bound ≤ ε(n,rμ) + ideal event bound at rI.
```

Only if the compilation and absorption proofs establish the relevant identities
may this simplify to the originally intended formula:

```text
ε(n,q) + δ(n,scale(q,cost(s,n))).
```

In particular, do not leave the first summand at `ε(n,q)` when applying the
comparison actually costs a monitored test at a larger allowance.

Lift the pointwise theorem to `HitsAt`, `Hitsᶠ`, and then `Hitsᴺ`. For contexts
with allowance at most `p(n)`, provide the uniform error majorants or exact
certificate reindexings needed to produce one negligible slack for that `p`.
Prove polynomial closure of the allowance transformations and negligibility of
the resulting error. Keep any larger base event bound explicit: simulator
absorption can change its allowance, not just add negligible slack.

The ledger's direct-agreement case uses the identity simulator and should be
the first family instance. Do not claim the same unchanged ledger bound for an
arbitrary simulator without the corresponding accounting proof.

**Acceptance:** transport is a consumer of explicit-error comparison and the
monitor compiler, with no new UC order. Its numerical statement follows the
proved costs and retains the required quantifier order.

## 5. Lift the strategy-level event bound to contexts

`Birthday.target` bounds the trajectory event under strategies. The observable
audit bound first uses the existing watch/trajectory soundness result. Keep
this step explicit: the compiler implements `auditWatch`, not a private-state
trajectory observer.

Prove a one-sided contextual lift by reusing the finite-strategy domination
machinery and `ctxRunᵒ` where applicable. A sufficient intermediate statement
has the following shape:

```text
for each certified context C, observation depth k, and positive slack η,
there is an admitted finite strategy d such that

  Pr≤ k (eventRun u μ C)
    ≤ watched strategy-run upper bound for d + η.
```

The strategy's allowance must be the one proved by the instrumentation and
domination accounting. Its observation must retain the watched event. An
arbitrary extracted strategy on a monitor-extended interface is not sufficient:
prove it factors through the watch, or prove the corresponding event-sensitive
inequality. Truncation and divergence must not create spurious reported hits.

Use the strategy-level bound for that strategy to obtain the contextual bound.
Do not assume the two-sided `dominatedᵒ` theorem already proves this statement,
and do not introduce a false-answering comparator without proving all of its
required comparison premises.

For the asymptotic result, choose a positive negligible slack independently of
the context at the required quantifier position. Account for every additional
slack and allowance change. Reuse existing protocol/machine transport for the
`Dist⊥` and `Dₚ` readings; do not equate their probability expressions by fiat.

**Acceptance:** a checked bound against all admitted contexts is obtained from
the existing strategy-level event theorem. It does not assume the desired
contextual event bound or read a hidden machine state.

## 6. Migrate one ledger consumer, then consider retirement

First restate the observable property using `Hitsᴺ` on the existing `imgᶠ`
images. Prove the comparison with the previous property needed by the public
results. Preserve `SerInj`, initialization, honesty/truthfulness assumptions,
the event, and the exact allowance/slack accounting.

Then migrate the ideal bound and the hash-to-ledger transfer body. Keep the
public counterexample `chimeric-loses-value` about the same event and experiment.
Preserve the trajectory appendix through its explicit watch soundness,
completeness, and query-instrumentation results; a generic raw morphism does not
have a protocol state on which `Bad` can automatically be defined.

Recheck consumers before changing `Systems` telescopes. Replacing protocol
families by arbitrary raw hom families expands the domain; use the existing
embedding and prove the required bridge instead of calling that change a
definitional alias.

Retirement candidates, conditional on successful migration:

| Candidate | Gate |
|---|---|
| `UC.Saturated` observable-bound machinery | Public consumers use the new property with the required semantic comparison proved; independently used trajectory machinery is retained or relocated |
| `UC.Asymptotic` | Its remaining consumers and public results have replacements with justified premises and conclusions |
| `≤UC^ωⁿ⇒≈negl` | No active consumer needs the strategy-level bridge after event transport is migrated |
| `Observable` watch implementation and lemmas | Retain what proves monitor agreement or supports the trajectory appendix; remove only genuine duplicates |
| `Protocol.Observe` probability and transfer lemmas | Preserve uses by protocol safety and game-playing developments |

No module deletion or line-count reduction is an acceptance criterion before
these gates are met. Retire adapters after their final callers migrate rather
than retaining parallel proof implementations.

## Implementation sequence and stop conditions

1. Pin the accumulated audit event, finite-depth upper-bound predicate, and
   fixed-allowance convention. Prove elementary observation transport.
2. Spike the monitor compiler: type it, prove agreement with `auditWatch`, and
   establish the full budget transformation, including completion and zero
   allowance. Test returning, querying, and diverging experiments.
3. Prove the event-sensitive one-sided domination result and instantiate it with
   the ledger's existing observable bound.
4. Implement fixed-context transport and its correctly quantified family and
   saturated forms. Reuse the existing filtered/contextual API where useful;
   no new categorical construction is a prerequisite.
5. Migrate one existing ledger transfer and its public counterexample; compare
   statements and accounting before retiring any infrastructure.
6. Retire only the demonstrated redundancies and update `docs/end-to-end.md`,
   the UC inventory, and affected cross-references.

Stop and report the exact obstruction if completion cannot be monitored without
changing the experiment, flag reading needs private state, the event-sensitive
finite-strategy lift fails, or no claimed allowance bound can be proved. Do not
resolve such an obstruction by admitting fewer contexts, assuming termination,
moving the slack inside the context quantifier, or changing the event silently.

Verification follows the shared Agda instructions: record the current
escape-hatch baseline, check changed modules and importers, the root closure,
`Examples/ChimericLedger/{Transfer,Replay}.agda`, and relevant event, protocol,
and ledger test suites. Reject flagged warnings. Measure significant
elaboration regressions under the prescribed timeout discipline. Historical
counts and proof-length estimates are not substitutes for these checks.

## Spike findings (2026-09-21, branch `hits-spike`, not merged)

Steps 1–3 were attempted in one scratch module, `UC/Quantitative/Hits.agda` (456 lines,
green, no existing module edited, hatch count unchanged). Outcome: the construction and
certificate checks pass, but semantic agreement with the watch and event-sensitive
contextual adequacy remain open. The spike establishes neither of those obligations by
the behavior pins alone. Substantial event-bound infrastructure exists in `UC.Audit`.

### Delivered and checked

- **Monitor.** `μ : Proc B (B ⊗ᴵ Flagᴵ)` is buildable and certifiable, but a relay alone
  cannot detect completion. The working shape pairs it with a completion reader ABOVE the
  test: `compileᴹ Y B μ E = flagReadᴹ ∘ subᴵ E ∘ a⇒ᴵ ∘ T₁ᴵ Y μ`, where `flagReadᴹ` waits
  for the test's verdict, discards it, and outputs the flag. The pending query is monitor
  state (`Bool × Maybe (Neg B)`) because `reportsLoss` reads the (query, answer) pair.
  Divergence stays divergence (`flagRead-diverges ≡ botₚ`); a flag raised before it is not
  reported. The ledger instance is `auditMonitor = monitorᴹ (reportsLoss s₀)`.
- **The flag survives the context run.** It is a port, not a state: the compiled
  experiment's verdict IS the flag, read off the run's output, and `ctxRunᵒ`
  (`UC/Model/Dominated.agda`) carries it unchanged. The design is not wrong here.
- **`Upper d r = (k : ℕ) → Pr≤ k d ≤ r`** with transports `upper-≼[]`/`upper-≈[]`
  (`d ≼ₚ[ε] e → Upper e r → Upper d (r + ε)`, no extra slack) and `upper-≼`/`upper-≈`.
- **`HitsAt q r f μ`** with the capped allowance `ctxBudget c c′ ≤ q`, `Hitsᶠ`, `Hitsᴺ`
  (slack after `Poly p`, before the level), and the compiled-experiment transports.
- **Budget transformation, proved:** `κμ c = 2·(c ⊔ 1)`, from `Certified 1 monitorᴹ` and
  `Certified 2 flagReadᴹ` (at `waitE` one downward unit is already owed, so no potential
  makes it 1). `κμ 0 = 2`: the process spelling of the watch is NOT allowance-preserving
  at the certificate level, where `Strategy.asks≤-watch` is exact. The over-charge is
  irreducible under `ctxBudget`, which cannot tell a flag-port query from an honest one
  (the port-specific bound `UC/Budget.agda`'s header prices and does not build).
- **Ledger chain composes end to end modulo the lift:**
  `Birthday.target → auditWatch-bounded → upper-run → EventDominated → HitsAt`, with the
  `Dist⊥`/`Dₚ` seam crossed one-sidedly by `prAgree` and the cap absorbed by `asks≤-mono`.
  `IsWatch report w` (three equations, all `refl` for `auditWatchFrom`) replaces an
  identification of the two strategy transformers, which would need funext.

### Where it stops: the strategy-to-contexts lift (§5)

`EventDominated` is stated and consumed; nothing inhabits it.

- The false-comparator route is dead for a stronger reason than §1 gives: `dominated`'s
  hypothesis ranges over ALL budgeted strategies and `runᴹ u d`'s verdict is `d`'s own, so
  at `d = out true` every process has mass 1 and no one-sided `Upper (runᴹ u d) r` with
  `r < 1` holds for any `u`, any comparator.
- `skeleton` (`UC/Machine/Dominated.agda`, `Decompose.half`) is one-sided-ready — it uses
  only the forward half — but applies its hypothesis at `dstrat b n₁ z`, a strategy read
  off the context's certificate by `UC.Seam.Extract.extract`, which carries no syntactic
  invariant. Nothing says it factors through `w false (·)`. Closing this needs either
  (i) a theorem that extraction from `compileᴹ Y μ E` lands in the watch's image, not
  currently expressible about `Extract`'s output, or (ii) a new event-sensitive
  decomposition redoing `UC.Seam.Transfer` (355 lines) with the accumulator threaded.
  Either is a new module, not a 40-line restatement.
- §2 obligation 4 (agreement of the compiled experiment with `runᴹ u (auditWatch d)` at
  embedded strategies) is blocked the same way: an adequacy statement for a five-machine
  trace tower, where `UC.Seam.Adequacy`+`Plug` are the ~250 lines for the two-machine case.
- The reverse direction (context bound → strategy `Pr≤` bound) exists:
  `UC.Seam.Audit.Context.extractᵍ`. The forward direction exists nowhere in the repo.

### What already exists: `UC.Audit`

`Mass.at` is `Pr≤` (`UC/Model/Enrichment.agda`); `AuditBound f 𝔈 ε` (`UC/Audit.agda`) is
`(n : ℕ) → at n (obs (tv₁ Y f Et) m) ≤ ε (ctxBudget c c′)` at every permitted context —
`Upper` at every context, unnamed. `audit-carry` supplies the structural pattern for
§4 (simulator absorbed into the test, `simCost` rescaling via `ctxBudget-absorb`, one
positive slack), with `Examples.HashForward.Audit` as a worked instance at a
nontrivial grade. Its premise is QUALITATIVE `f ≤UC[ cs ] g`, however, not an
explicit-error comparison. Its arbitrary positive slack cannot replace a nonzero
quantitative error at a fixed security parameter. Reuse its event designation,
absorption, and accounting machinery, and factor or add an explicit-error carry using
`upper-≈[]`; do not claim the existing theorem already discharges §4.
The gap `Hits` closes is that a bound quantified over every budgeted test bounds the mass
of a constant-`true` verdict too (now stated at `UC.Machine.EventBounds.Reader`); making
the verdict be the flag is the proposed repair, subject to semantic adequacy.

**Two allowance presentations.** `AuditBound` reads the schedule at the CARRIED budget
`ctxBudget c c′`; §3 uses a cap `ctxBudget c c′ ≤ q` for the public statement. Neither
must be discarded: use carried budgets internally and prove the adapter to capped
allowances. For a monotone schedule the carried bound implies the capped bound; a
bound at every cap can be specialized to the carried allowance. At the family level,
also preserve the slack's quantifier position: this pointwise observation does not
produce a uniform capped slack from context-local witnesses.

### Post-spike decision

Continue toward the contextual event theorem. The report identifies missing proofs,
not a counterexample to the construction. Retain the strategy-level results while
proving the lift, but do not treat a contextual headline conditional on
`EventDominated` as completion.

Use carried budgets internally and capped allowances publicly, with proved adapters
for the schedules used by the ledger. Commission event-sensitive adequacy, preferring
factoring or parameterizing the existing decomposition over a second independent
copy of `UC.Seam.Transfer`.

### Landing sites, if continued

`Upper` and its transports → `ProbabilisticLogic.Dp.Advantage` (or `.Upper`); `Flagᴵ`,
`monitorᴹ`, `flagReadᴹ`, `compileᴹ`, `κμ`, `qb-compileᴹ`, behaviour pins →
`UC.Machine.Monitor`; `watchFrom`/`IsWatch`/`asks≤-watch` → `Strategy` beside `mapStrat`,
with `Observable.auditWatchFrom = watchFrom (reportsLoss s₀)` so the pin is `refl`;
`upper-run` → `UC.Seam.Carry` beside `adv-at`; `eventRun`/`HitsAt`/`Hitsᶠ`/`Hitsᴺ`/
transports/`EventDominated` → `UC.Model.EventBounds`, after reconciling with `UC.Audit`;
`auditMonitor`, `auditWatch-IsWatch` → `Examples.ChimericLedger.Observable`, `ledger-hits`
→ `Property`.

## Post-spike work package

This is a substantive semantic bridge, not a small vocabulary cleanup. The next
success criterion is an inhabited event-sensitive lift for the actual compiler;
deleting `UC.Saturated` is downstream of that result.

### A. Prove monitor agreement at embedded strategies

Discharge §2 obligation 4 for the compiled monitor and completion reader. Preserve
the accumulated audit event, termination, and divergence. A flag raised before a
diverging continuation must not become a reported hit. The existing behavior pins
are useful checks but do not replace this theorem.

### B. Resolve the closure and zero-allowance accounting

The spike's compiled TEST certificate is `κμ(c) = 2 · (c ⊔ 1)`. With the original
closure certificate, the compiled contextual allowance is:

```text
2 · (c ⊔ 1) · (c′ ⊔ 1).
```

This is not bounded by a function of the original allowance
`q = c · (c′ ⊔ 1)` alone: at `c = 0`, `q = 0` regardless of `c′`.
Do not infer a polynomial-cap theorem from the test certificate alone.

At the concrete closed-machine boundary, try recertifying the SAME closure at
`QB 0` using the closed-process certificate. Prove the passage through the model's
closure representation. This would give:

```text
compiled allowance = 2 · (c ⊔ 1) ≤ 2 · (q ⊔ 1).
```

This is a proposed model-specific proof, not a law of an arbitrary graded subcategory.
It changes a certificate, not the closure or the admitted experiment.

Keep two costs distinct throughout:

- The compiled contextual allowance used to instantiate quantitative comparison.
- The honest-interface query allowance of the strategy used with `Birthday.target`.

A flag-port query need not be a ledger query. First try to preserve the original
honest-query bound in the event-sensitive decomposition even if the coarse compiled
certificate charges more. Do not make a new port-specific budget calculus a
prerequisite. If only a conservative polynomial rescaling can be established,
expose it in the numerical statement and check it against the intended public
bound; do not silently retain the old formula.

### C. Prove semantic event-sensitive decomposition

Do not require the extracted strategy to be syntactically equal to `auditWatch d`.
Truncation may make that formulation unsuitable. The sufficient target is the
one-sided semantic estimate:

```text
for every certified context C, depth k, and positive slack η,
there exists a finite strategy d with the proved honest-query allowance such that

Pr≤ k (compiled monitored context run)
  ≤ watched-event probability under d + η.
```

The strategy may depend on the context, depth, slack, and compared process. The
ideal-side strategy bound must apply uniformly to every strategy so obtained.
Identify the precise accumulator invariant that connects extracted verdicts to the
audit event. Reuse or factor the existing extraction/decomposition proof where
possible; a semantic relation or inequality is enough, without function
extensionality or equality of strategy syntax.

Check the stop/return, query/answer, random choice, and truncation cases explicitly.
The proof must establish the required direction of the event inequality, not merely
preserve an arbitrary Boolean verdict.

### D. Discharge the lift and migrate the quantitative carry

Instantiate `EventDominated` for the actual compiler using C, then derive the ideal
contextual event bound from `Birthday.target` and watch soundness. Choose positive
negligible slack at the required position, independently of the context, to obtain
the family result.

Factor or add the explicit-error audit carry described above. Preserve event-class
membership under simulator absorption and charge the comparison at the compiled
test's actual allowance. Reuse `upper-≈[]` for the numerical step; do not replace
the explicit error by the qualitative carry's arbitrary slack.

Migrate the ledger transfer through this proved lift and quantitative carry before
retiring any old event machinery.

### Acceptance and sequence

1. Checked agreement with `auditWatch` at embedded strategies.
2. Checked compiled-context and honest-query accounting, including allowance zero.
3. Event-sensitive one-sided decomposition and an inhabited `EventDominated`.
4. The ideal contextual bound and explicit-error transfer applied to the ledger.
5. The existing observable counterexample and trajectory appendix retain their
   events and justified accounting.
6. Only then, retirement and full closure checks under the existing verification
   rules.

The contextual acceptance theorem must have neither `EventDominated` nor the
desired contextual event bound as a remaining premise. Retain the semantic stop
conditions above: proving a useful conditional lemma is progress, but is not a
substitute for discharging the bridge.

## Stage B status (2026-09-22)

Corrections from the three landed work packages. Earlier sections stay as
written; this one overrides them where they differ.

**§2 obligation 4 is DISCHARGED.** `UC.Machine.Monitor.Agree:agree` proves the
compiled monitored experiment at an embedded strategy equal to layer 1's run of
that strategy under the watch, as full `_≈ₚ_` and not a one-sided estimate, for
any transformer satisfying `Strategy:IsWatch` — so verbatim for
`Examples.ChimericLedger.Observable:auditWatchFrom`. Three pins fix the
behaviours: `…Agree:monitor-returns`, `…:monitor-queries` and
`…:monitor-diverges`, the last pinning divergence rather than a raised flag.
The obligation was never coupled to the §5 lift, and the lift does not use it.

**The agreement is a SPAN, not a simulation in either direction.** The compiled
five-machine tower is live at configurations no strategy environment matches,
and `UC.Seam:EnvSt` holds trees no watch produces; `Maybe`-padding one side does
not repair it. The proof goes through the reachable-configuration machine
`…Agree:reachᴹ`, with one leg to each side.

**`EventDominated` is down to one premise.** `UC.Quantitative.EventLift` needs
only `UC.Machine.Dominated:CovCtx` at the COMPILED context. Two obligations
remain: O1, carrying that invariant through `UC.QueryBound.Compose`; O2, a tight
`UC.QueryBound:QB` for the compiled test — `qb-∘` multiplies rates,
`UC.Machine.Monitor:κμ` is `λ c → 2 · (c ⊔ 1)`, and the flag channel is internal
to the compiled context.

**§B closure accounting.** Recertification with `UC.QueryBound:qb-closed` works
verbatim: the closure is a closed process, so `EventBounds:carry-boundedBy`
takes `qb-closed m` for the closure's own certificate. The ledger bound is then
cappable (`UC.Quantitative.Hits:κμ-cap`) and tight at allowance zero, where
`…:κμ-cap-zero` gives `κμ 0 = 2` rather than a vacuity.

**§4 at the total event class.** Absorption is the readout-commutation square
`UC.Model.EventBounds:Absorbsᵣ` — a real obligation on the ideal-side monitor,
not a corollary — and the machine-side budget identity is
`UC.Budget:ctxBudget-simCost` (one guard), NOT `UC.Budget:ctxBudget-absorb`.

**Landing sites, corrected.** Monitor-free generics: `UC.Model.EventBounds`.
Compiled `Hits*` instances (`HitsAt`/`Hitsᶠ`/`Hitsᴺ`, `hits-carry`):
`UC.Quantitative.Hits`. The compiler: `UC.Machine.Monitor`.

**§C cost and direction.** The spike's 355-line estimate was too high: about 85
lines of new forward induction, with `UC.Seam.Transfer` reused. Route (i) is
unnecessary — `Cov` is leafwise. §C's direction above is the right one (the
watched event bounds the extracted verdict); the work-package-C agent brief
paraphrased it inverted.

**Performance.** Never pass a `QB`/`Certified` VALUE to a pattern-matching type
family: quantifying the certificate instead of naming it took one check from
18 min / 12 GiB to 10 s.

**Housekeeping done.** `watchFrom`/`IsWatch`/`watchFrom-IsWatch`/`asks≤-watch`
now live in `CategoricalCrypto.Strategy`, generic in the two alphabets, with
`UC.Quantitative.Hits` re-exporting them. `UC.Machine.Monitor.Agree` is in
`CategoricalCrypto.UC`'s closure; `Hits`, `UC.Seam.EventTransfer` and
`UC.Quantitative.EventLift` stay out while Stage B is in flight. Held back:
`…Agree:simFn`, `…:point-⊛`, `…:discard-⊛` are general and belong in
`Machines.Pointwise` (rule 27), which has 82 transitive in-repo importers
(`Machines.Sim` 130, `Machines.Frame` 132) — the recheck is not paid here.

## Stage B status, corrections 2026-09-22 (2)

The section above stays as written; this one overrides it where they differ.

**O1 and O2 are discharged, and the compiled context is not over-charged.**
O2 is `UC.Machine.Monitor.Tight:qb-compileᵀ`: the compiled test spends the
allowance of the test it was compiled from, rate `c`, not `κμ c`. It is bought
by reading the composite as ONE machine (`UC.QueryBound.Compose.Step`'s
`Nᶜ`/`unfoldᶜ`, with `Monitor.Agree`'s collapse of `flagReadᴹ ∘ subᴵ E`), not
by refining `QBᵢ`. §B's `compiled allowance = 2 · (c ⊔ 1)` therefore
over-charges: with the closure recertified by `qb-closed`,
`UC.Quantitative.EventLift.Budget:qb-compiled′` gives the compiled CLOSED
context rate `c` on the nose. The coarse `qb-compileᴹ`/`qb-compiled` at `κμ c`
is kept as the cheaper term, not as the accounting. O1 is
`UC.Quantitative.EventLift.Cov`, and it does not walk `qb-∘`: the certificate
is built on the collapsed tower (`Monitor.Agree.Watch:watchᴹ`), where the
accumulator is a state component and the invariant is an induction on the
test's own emission tree.

**`c + 1` is optimal for the invariant, not slack.** `CovCtx` is read at EVERY
zero-potential state, so a raised accumulator must carry potential; `Cov:pend`
is that potential, and it costs one unit of the rate rather than a factor. At
rate `c` the premise is FALSE, not merely unproved — the five-fold `qb-∘`
tower's monitor potential is constantly zero
(`UC.Machine.Monitor:qbᵢ-monitor`), so a state with the flag raised and the
whole allowance spent still has potential zero and reports `true` with no
traffic covering it. `EventLift:eventDominatedᵘ` at `c + 1` is therefore the
one rate the lift can be discharged at; `EventLift:eventDominated` keeps its
premise at `c` because the `QB` half exists there (`qb-compiled′`) while the
`CovCtx` half does not.

**The ledger consumer** is `Property.hitsᴸ` (formerly `ledger-hitsᵘ`), unconditional, with the
schedule read one query past the environment's own cap. The leaf it serves
is `Examples.ChimericLedger.Transfer` — the wiring is a separate work package
and is not landed here. Its last section is the replay generalisation, the attack at every `ℓ`, `ser` and `V` at a FUNDED
initialization; its gap to the positive theorem is that no prefix from the
UTxO genesis credits an account (`Examples.ChimericLedger:checkWdrls-[]`, read
at the ledger's activation by `…System:ledger-keeps-accts-[]`).

**Closure, corrected.** `UC.Quantitative.Hits` and `UC.Seam.EventTransfer` were
never out of it: `UC.Machine.Monitor.Agree` imports the first and
`UC.Machine.Dominated` — public in `CategoricalCrypto.UC` — the second. The
event-bound layer is now listed explicitly in that module's closure-only block
(`Monitor.Slide`, `Monitor.Tight`, `EventLift.Budget`, `EventLift.Cov`,
`Seam.EventTransfer`), through which `UC.Quantitative.EventLift` also arrives.

**Placement, done.** The held-back `…Agree:simFn`, `…:point-⊛` and
`…:discard-⊛` now live in `Machines.Pointwise`, beside the `⊗-pureˡ` that
`simFn` packages. `Monitor.Slide:sub-resp-≈` was an exact duplicate of
`UC.Machine.Dictionary:sub-resp-≈` and is gone; `sub-∘` joins `T₁-∘` there.
The hole-wire block (`sub-wire`, `λ-tri`, `ρᴵ⇒`, `ρ-tri`) moves beside
`T₁-wire` in `UC.Machine.Slide`, and the interchange `relay-slide` into
`UC.Machine.Slide.Relay` — its own module because the elaborated 45-step
monoidal chain costs every importer of `UC.Machine.Slide` about 17 s of
deserialization (warm `Monitor.Tight` 21 s baseline, 52 s undivided, 21 s
split). `…System:checkWdrls-[]` moves beside `checkWdrls` in
`Examples.ChimericLedger`.

**The two collapses are not factorable.** `Tight:qb-compileᵀ` and `Cov:covCtx`
unfold the same tower, but they certify DIFFERENT machines — the generic
composite `CStep.Nᶜ` at `Y ⊗ᴵ B` and the hand-written `Watch.watchᴹ` at `B` —
so their `cohL`/`cohR` obligations are against different `step`s, and that
proof is most of each body (`Tight`'s `cohE`/`pump` against the unfolding,
`Cov`'s four-line chains against `wPass`). Their potentials differ in kind
too: `Tight`'s ignores the monitor state, which is exactly what `CovCtx`
refutes. What they do share is one plumbing step,
`mapₚ forget (d >>=ₚ ref) ≈ₚ (e >>=ₚ base)`, worth about 9 lines against a
10-line lemma; it was measured and not taken.

## Retired 2026-09-22

The migration left the following without any consumer; each was grep-verified
against the whole `src` tree before deletion. Nothing that survived changed
statement except the two the maintainer ruled, recorded at the end.

**Modules deleted outright.** `UC.Quantitative.EventLift.Budget`,
`UC.Saturated`, `UC.Asymptotic`. Nothing named `UC.Asymptotic*` remains.

**Modules renamed** (content unchanged): `UC.Asymptotic.Contextual` →
`UC.Model.Family.Contextual`, `UC.Asymptotic.Compose` →
`UC.Model.Family.Contextual.Compose`. `UC.Asymptotic.Family` moved to
`UC.Model.Family.Emulation` and kept only `gradedᶠ`, `imgᶠ`, `_≈ᶠ[_]_`,
`_≤UC^ωⁿ_` (since renamed `_≈ᶠᴺ_`), `≈ctxᴬ⇒≈ℰ[]`, `subQB`, `certᶠ`, `≤UC^ωᵉ⇒≈ℰⁿ`, `≤UC^ωᵉ⇒≤UCᴺ` and
`≈ᶠ-runs`; `UC.Saturated.Systems` is the one alias that followed them there,
the telescope `(n : ℕ) → Protocol unitᴵ (B n)` appearing in far more than four
signatures.

**Exports retired.**

- `UC.Quantitative.Hits`: `chargeᴹ`, `κμ-cap`, `κμ-cap-zero`, `hits-transport`,
  `hits-transport-ctx`, `hits-carry`, `hits-carryᶠ`, `NegligibleBound-carry`,
  `watchOf`, `EventDominated`, `ledger-hits`.
- `UC.Quantitative.EventLift`: `eventDominated`, `ledger-hitsᶜ`; the `Set₁`
  alias `EventDominatedᶜ` is inlined into `eventDominatedᶜ`'s signature.
- `UC.Quantitative.EventLift.Budget`: `qb-reopen`, `qb-opened`, `qb-opened′`,
  `qb-compiled`, `qb-compiled′` — hence `UC.Machine.Monitor.Tight.qb-compileᵀ`,
  `UC.Machine.Monitor.qb-compileᴹ` and `…:poly-κμ` are retained but currently
  unused.
- `UC.Model.EventBounds`, cascading from `hits-carry`: `carry-boundedBy`,
  `carry-upper`, `Absorbsᵣ`, `NegligibleBound-charge`. `Readout`, `Charge`,
  `readRun`, `BoundedAt`, `BoundedBy`, `Monotone`, `carried⇒capped`,
  `capped⇒carried`, `carriedᶠ⇒boundedᶠ`, `Boundedᶠ`, `Boundedᴺ`,
  `boundedᶠ⇒boundedᴺ`, `ctxRun-∘` and `qb-absorb` stay.
- `UC.Saturated`, with the module: `Systems` (relocated), `Watch`, `Bad`,
  `QueryPreserving`, `SaturatedBounded[_]`, `SaturatedHit[_]`,
  `SaturatedBounded`, `SaturatedHit`, `SaturatedBoundedᴺ`, `SaturatedHitᴺ`,
  `saturatedᴺ⇒saturated`, `saturatedHitᴺ⇒saturatedHit`, `SaturatedRespects[_]`,
  `saturated-respects[_]`, `SaturatedRespects`, `saturated-respects`,
  `SaturatedRespectsᴺ`, `saturated-respectsᴺ`, `_≈negl_`, `≈negl-refl`,
  `≈negl-sym`, `≈negl-trans`, `≈negl-respects`.
- `UC.Asymptotic`, with the module: `_≤UC^ω_`, `boundedᴺ`, `uc-preservesᴺ`,
  `saturatedHitᴺ-from-monitor`.
- `UC.Asymptotic.Family`: `≤UC^ωⁿ-refl`, `≤UC^ωⁿ-sym`, `≤UC^ωⁿ-trans`,
  `Imageᶠ`, `imageᶠ`, `≈ᶠ⇒≈ℰ[]`, `≤UC^ωⁿ⇒≈ℰⁿ`, `≤UC^ωⁿ⇒≈ℰᶠ`, `≤UC^ωⁿ⇒≤UCᵁ`,
  `≤UC^ωⁿ⇒≤UCᴺ`, `≤UC^ωⁿ⇒≤UC^ωᵉ`, `≤UC^ωᵉ⇒≤UC^ωⁿ`, `≤UC^ωᵉ⇒≈ℰᶠ`,
  `≤UC^ωᵉ⇒≤UCᵁ`, `admits-inv-pow-2`, `rejects-inv-suc`, `uc-≈ᶠ[_]`,
  `uc-≤UC^ωⁿ`, `pointwise-exact`, `pointwise-rejects`, `≤UC^ωⁿ⇒≈negl`.
- `Examples.ChimericLedger.Transfer`: `watched-transfer`.

Consequently consumer-free but kept as general-purpose lemmas:
`UC.Seam.Carry.adv-from-runs`, `Protocol.Observe._≈adv[_]_`/`transfer-at`,
`…RationalDist.Advantage.advᵇ⊥-refl`/`-triangle`.

### Orphan sweep, same day

A second pass, ruled by the maintainer, deleted what the retirement above left
consumer-free. Where the two lists disagree, this one is current.

**Modules deleted outright.** `UC.Machine.Monitor.Tight`; `Protocol.Live` (the
structural-liveness layer `NoDead`/`NoDeadStep`/`live`, which nothing imported
and which only `Protocol.Machine.Total.totalRun-morphism` was ever aimed at).

**Retired result** (`Monitor.Tight`, recorded so the fact is not lost).
`qb-compileᵀ` certified the compiled test at the allowance of the test it was
compiled from: `QB c E → QB c (compileᴹ Y B (monitorᴹ report) E)`, rate `c` and
not `κμ c`. The flag query `flagReadᴹ` makes is answered by `monitorᴹ` and
never leaves the composite, so the compiled test's downward traffic on `Y ⊗ᴵ B`
is exactly `E`'s and the potential of the composite IS `E`'s. It was bought by
reading the composite as ONE machine (`UC.QueryBound.Compose.Step`'s
`Nᶜ`/`unfoldᶜ`, with `Monitor.Agree`'s collapse of `flagReadᴹ ∘ subᴵ E`), not
by refining `QBᵢ`. Its consumer was `UC.Quantitative.EventLift.Budget`.

**Exports retired.**

- `UC.Machine.Monitor`: `κμ`, `qb-compileᴹ`, `poly-κμ` — the coarse
  certificate of the compiled test and its polynomial closure, superseding the
  "retained but currently unused" note above. `qbᵢ-monitor` and `qbᵢ-flagRead`
  stay.
- `Protocol.Machine.Total`: `totalRun-morphism` — the reading of layer-1
  liveness as `TotalRun` of a protocol image. Nothing in `src/` ever
  discharged its premise. `TotalRun`, `totalRun-resp-≈ᴹ` and `totalRun-∘` stay.
- `UC.Model.EventBounds`: `Charge`, and the whole carried-allowance
  presentation — `BoundedBy`, `Monotone`, `carried⇒capped`, `capped⇒carried`,
  `carriedᶠ⇒boundedᶠ`. Only the capped one was ever consumed, so this
  supersedes the "stay" list above; `Readout`, `readRun`, `BoundedAt`,
  `Boundedᶠ`, `Boundedᴺ`, `boundedᶠ⇒boundedᴺ`, `ctxRun-∘` and `qb-absorb` do
  stay.
- Singletons: `UC.Seam.Carry.adv-from-runs`,
  `…RationalDist.Advantage.advᵇ⊥-refl` (both named as kept above — that note
  is superseded), `UC.Quantitative.Family.≤UC^ωᵉ-sub`,
  `UC.Quantitative.Query.pull-simCost`.

`Protocol.Observe._≈adv[_]_`/`transfer-at` and `…Advantage.advᵇ⊥-triangle`
were listed for retirement too and are NOT gone: each has a real consumer —
`transfer` and `adv⊥-triangle` in their own files, and `_≈adv[_]_` in
`Examples.MerkleDamgard`.

**Merged.** `UC.Quantitative.Hits` is gone as a module: `HitsAt`, `Hitsᶠ`,
`Hitsᴺ`, `hitsᶠ⇒hitsᴺ`, `upper-run` and `run-upper` moved into
`UC.Quantitative.EventLift` (219 lines, one topic — the compiled readout's
event bounds and the lift off them), and `readoutᴹ`/`eventRun` moved into
`UC.Machine.Monitor`. The readout is Monitor's own construction, and it is the
module `UC.Machine.Monitor.Agree` and `EventLift` can both import: `EventLift`
imports `Agree`, so leaving `eventRun` with the bounds would have cycled.

**Relocated.** The ledger-specific tail of the generic modules —
`auditMonitor` and `auditWatch-IsWatch` (from `Hits`) and `ledger-hitsᵘ`
(from `EventLift`; both since inlined into their one consumer) — now lives in `Examples.ChimericLedger.Property`, stated
at `n`/`ser n`/`genesisAt n` inside its `(a V : ℕ)` block, with
`auditMonitor ℓ ser s₀` absorbed into the `auditMonitorᶠ` that was already
there. No module under `UC/` imports `Examples.ChimericLedger*` any more.

**The two ruled statement changes.**

1. `Transfer.ledger-uc-to-pov-family` (the trajectory appendix) now reads its
   schedule at `q + q + 1` rather than `q + q`: it is routed through claim 1
   (`preserves-value-transfer` → `Property.preservesValue⇒saturated` →
   `withAudits`' doubling → `TruthfulAudit`) instead of through the deleted
   strategy-level transfer, so the monitor's one accumulator query is charged
   on top of the honest interface's doubling. The event, the `TruthfulAudit`
   premise and `ledger-pov-family-negligible`'s shape are unchanged, and the
   new schedule's negligibility is `Property.εᴹ-negligible`.
2. `Property.preservesValue⇒saturated` states its conclusion directly — for
   every polynomial allowance `p` there is a negligible `ν` with
   `Pr (R n) (auditWatch n d) ≤ εᴹ n (p n) + ν n` at every `n` and every `d`
   inside `p n` — which is exactly what `SaturatedBoundedᴺ R auditWatch εᴹ`
   unfolded to.

### Second orphan sweep, same day

A third pass, ruled by the maintainer, deleted what the sweep above left
consumer-free. Where the lists disagree, this one is current.

**Module deleted outright.** `UC.Seam.Carry`, with its last export `adv-at`
and the privates `shift`/`Reads`/`one-sided`.

**Exports retired,** each grep-verified against the whole `src` tree:

- `UC.Machine.Monitor`: `qbᵢ-flagRead` and its potential `Φᶠ` (superseding the
  "stay" note above), and the flag-reader behaviour pins `flagRead-start`,
  `flagRead-complete`, `flagRead-report`, `flagRead-diverges`. `qbᵢ-monitor`
  and the traffic pins `monitor-query`/`monitor-answer`/`monitor-flag` stay.
- `UC.Machine.Monitor.Agree`: the behaviour pins `monitor-returns`,
  `monitor-queries`, `monitor-diverges`, with the one-interface fixtures only
  they used — `OneSt`, `B₀`, `rep₀`, `oneStep`, `oneᴹ` and `agree₀`. `agree`
  itself stays; `EventLift` consumes it.
- `UC.Quantitative.Family`: `λ⇐ᶜ`. `λ⇒ᶜ` stays.
- `UC.Model.EventBounds`: `qb-absorb`, retired by maintainer ruling on
  2026-09-22 — superseding the "do stay" note above. `ctxRun-∘` stays.

## WP4 verdict (2026-09-23)

A bounded design review of the event/resource invariant boundary behind the
`q + 1` of the compiled-monitor lift. No source changed. Verdict: **retain the
current interface**; the alternative below is described, not implemented, and
no sharper bound is promised.

### 1. What `CovCtx` quantifies over

`UC/Machine/Dominated.agda:211`:

```agda
CovCtx : (B : Iface) {K : Proc B Ωᴵ} (q : ℕ) → (Neg B → Pos B → Bool) → QB q K → Set
CovCtx B q report (N , cert , _) =
  (f : ℕ) (z : AtMost Φ 0) → Cov false f (Φ (proj₁ z) ℕ.+ q) (onRᵍ (proj₁ z) tt)
  where
  open Ext B N q cert
  open ET B N q cert report
```

- It is a property of the **certificate**, not of `K`: the `QB` triple
  (`UC/QueryBound.agda:287`) is destructured and only `N`'s `Certified q N`
  (`:276`) is read; the `≈ᴹ` witness is discarded. `Φ`, `onRᵍ`, `pointᵍ` are
  `QBᵢ`'s fields (`:147`-`:155`).
- `z : AtMost Φ 0` is `Σ[ s ∈ MC.St N ] Φ s ℕ.≤ 0` (`:120`): **every** state of
  the representative whose potential is zero. Not the support of
  `pointᵍ : Dₚ (AtMost Φ 0)` (`:149`), and not the configurations reachable
  from it through `onLᵍ`/`onRᵍ`. The three notions are distinct here — see §3.
- `f : ℕ` is every fuel. `Cov acc 0 r X = ⊤` (`UC/Seam/EventTransfer.agda:75`),
  so content starts at `suc f`, one `br` per `Dₚ` level (`:76`).
- The index stays `Φ (proj₁ z) ℕ.+ q` although `Φ (proj₁ z) ≤ 0`: the equation
  `Φ s ≡ 0` is propositional, and `Refine` spends it with `ℕP.n≤0⇒n≡0` where it
  needs to (`Dominated.agda:95`-`:97`).
- Restricting `z` would not make `Cov` a local property. `Cov`/`CovL`
  (`EventTransfer.agda:73`-`:82`) still quantify over **every** answer
  `p : Pos B` at a query leaf (`:80`) and recurse into `onLᵍ s p` at the state
  `s` that leaf names, reachable or not.

### 2. Where `eventSkeleton` uses that quantification

`cov` is consumed at **one** place, `Dominated.agda:251`, inside `fwdᵂ`
(`:249`-`:251`):

```agda
  fwdᵂ f = dom≤-bind (indᵇ true) (indᵇ-nn true) f pointᵍ (obsᵍ u true) _
                     λ z → runFwdᵂ f (proj₁ z) (cov f z)
```

`dom≤-bind` (`ProbabilisticLogic/Dp/Dominate.agda:158`-`:176`) asks for
`dm : (p : A) → Dom≤ P k (f p) (g p)` at **every** `p`, because its proof calls
`uniformize` (`:174`, defined `Dp.agda:246`), which maxes the per-value budget
witnesses over a depth-`n` support but draws them from a total function. The
support-restricted `uniformizeˢ` already exists
(`Dp/Support.agda:79`) and is not used here.

Nothing else in `eventSkeleton` (`:239`-`:272`) touches `cov`: `bound`
(`:258`-`:266`) uses only the strategy hypothesis `h` and `dstrat-asks`
(`:94`), and `to-obs` (`:115`) is the `≈ₚ` refinement (`:109`). Downstream the
invariant is spent at exactly one leaf: `runFwdᵂ` (`EventTransfer.agda:227`) →
`treeFwdᵂ` (`:145`) → the verdict clause of `treeFwdLᵂ` (`:182`-`:188`), via
`cov-ind` (`:121`).

**Conclusion.** The all-zero-potential-state quantifier is *not* needed by the
argument. It is what the certificate representation plus the
everywhere-quantified bind congruence deliver: the argument needs the invariant
only at the initial configurations `pointᵍ` actually reaches.

### 3. The extra unit, traced

`UC/Quantitative/EventLift/Cov.agda`: the potential is
`Φᵂ ((_ , se) , m) = qE.Φ se ℕ.+ pend m` (`:101`), with

```agda
  pend : MonSt B → ℕ
  pend (_   , just _)  = 1
  pend (acc , nothing) = bit acc
```

(`:92`, `pend≤1` at `:96`), and the certificate is `Certified (c ℕ.+ 1) watchᴹ`
(`:213`), `onRᵂ` landing in `Aᵂ (Φᵂ s ℕ.+ (c ℕ.+ 1))` (`:168`).

The obligation that forces it is `covᵂ` (`:273`-`:281`) — i.e. exactly
`CovCtx`'s quantifier. Of the six `idle`/`waitE`/`waitF` × accumulator shapes,
three are discharged **only** by `owed` (`:138`), that is only because `pend`
gives them potential ≥ 1: `((idle , _) , (false , just _))`,
`((idle , _) , (true , just _))`, `((idle , _) , (true , nothing))` (`:277`-`:279`).
Were `((idle , se) , (true , nothing))` admissible, `onRᵂ` there is
`qE.onRᵍ se tt >>=ₚ wAns waitE (true , nothing) …`, whose verdict clause
(`:151`) emits `proj₁ m = true` (matching `wPass`'s `inj₂ acc`,
`UC/Machine/Monitor/Agree.agda:291`), and `CovL false f r (inj₁ (inj₂ (_ , true)))`
unfolds to `true ≡ true → false ≡ true` (`EventTransfer.agda:81`).

The rest of `Cov.agda` does **not** need `pend`. The induction
`covTree`/`covLeaf`/`covVal` (`:236`-`:265`) carries
`proj₁ m ≡ true → accᶜ ≡ true` structurally through `∨-cover` (`:226`) and never
reads a potential. What `pend` does cost elsewhere is pure arithmetic: the
query leaf owes one unit for the answer it waits on, which is what `qBound`
(`:116`) charges against the strict drop `rE ℕ.< r` that the `+ 1` in the rate
provides, with `vBound`/`swap₃`/`ltR`/`leR`/`ltL` (`:119`-`:136`) the rest of
that accounting. The five-fold `qb-∘` tower cannot supply it: the monitor's own
potential there is constantly zero (`UC/Machine/Monitor.agda:121`,
`qbᵢ-monitor`), which is why the certificate is built on the collapsed
`Watch.watchᴹ` (`Agree.agda:312`) instead.

So: **one additive unit, paid entirely for `covᵂ`'s entry point**, not for the
invariant's induction and not for the traffic accounting.

*Measured* (throwaway spike, checked green then deleted; not committed). Take
`Cov.agda`'s `Cert` module, replace the potential by
`Φᶜ ((_ , se) , m) = qE.Φ se`, drop `bit`/`pend`/`pend≤1` and the whole
potential-arithmetic block (`:116`-`:139`), weaken `wAns`'s two bound arguments
`(lt : rE ℕ.< r) (le : rE ℕ.+ pend m ℕ.≤ r)` to the single `le : rE ℕ.≤ r` and
build both leaves with `≤-trans lo le`, and take `≤-refl` at both call sites
(`onRᵂ` at `Aᵂ (Φᵂ s ℕ.+ c)`, `onLᵂ` at `Aᵂ (Φᵂ s)`). Then

```agda
certᶜ : Certified c watchᴹ
```

typechecks, `rc=0` with an empty
`ModuleDoesntExport|UselessPublic|UselessPrivate|DuplicateUsing` grep. The
entire `wAns` bound apparatus — `lt`, `qBound`, `vBound`, `swap₃`, `ltR`, `leR`,
`ltL`, `owed` — exists to fund `pend`, and `cohLᵂ`/`cohRᵂ`/`pointᵂ`/`coh₀ᵂ` are
unchanged up to those arguments. **The `+ 1` buys `CovCtx`'s quantifier and
nothing else: the rate-`c` certificate of the collapsed tower exists.**

### 4. The alternative on paper: a support-restricted initial invariant

Not implemented, not promised. Described so WP6 and a later work package can
price it.

**(a) A membership predicate, defined from the library's support semantics.**
`Dp` has `Supp n d Φ` (`Dp.agda:211`) — a *universal* quantifier over the
depth-`n` leaves — and its introduction rules `Supp-bot`/`Supp-return`/
`Supp-bind`/`Supp-all` (`Dp/Support.agda:34`-`:76`), but no membership. Add to
`Dp.Support`:

```agda
data _∈ₚ_ {A : Set a} : A → Dₚ A → Set a where
  here  : {d : Dₚ A} (c : Bool) {p : A} → br d c ≡ inj₁ p → p ∈ₚ d
  there : {d : Dₚ A} (c : Bool) {d′ : Dₚ A} {p : A} → br d c ≡ inj₂ d′ → p ∈ₚ d′ → p ∈ₚ d

supp-∈ : (Φ : A → Set b) (d : Dₚ A) → ((p : A) → p ∈ₚ d → Φ p) → (n : ℕ) → Supp n d Φ
```

`supp-∈` is the introduction rule `Supp` lacks (`Supp-all`, `Support.agda:70`,
is its everywhere-quantified degenerate case); induction on `n`, mutual with a
leaf case, ~15 lines. `InitialSupport pointᵍ z := z ∈ₚ pointᵍ` is then *defined*
from the certificate's own `pointᵍ`, not supplied as a predicate. Caveat: `Supp`
is not `≈ₚ`-stable (`Support.agda:12`-`:15`), so `CovInitial` would be a
property of the literal `pointᵍ` term, exactly as `CovCtx` already is — no
`≈ₚ`-transport may be assumed. Second caveat: the predicate is empty when
`pointᵍ` is `botₚ`, which is sound (nothing observes) but means non-vacuity has
to be read off the concrete `pointᵂ` (`Cov.agda:200`), not off the signature.
`EventTransfer.agda:92`-`:100` (`cov-true`/`covL-true`, consumer-free in `src/`)
is the corresponding non-emptiness demonstration for `Cov` itself.

**(b) The support-aware bind theorem.** In `Dp.Dominate`:

```agda
dom≤-bindˢ : (P : B → ℚ) → NNF P → (k : ℕ) (d : Dₚ A) (f g : A → Dₚ B)
           → ((n : ℕ) → Supp n d (λ p → Dom≤ P k (f p) (g p)))
           → Dom≤ P k (d >>=ₚ f) (d >>=ₚ g)
```

`dom≤-bind` (`Dominate.agda:161`) verbatim, with `uniformize` (`:174`) replaced
by `uniformizeˢ` (`Support.agda:79`) applied to `Supp-map` (`:58`) of the
hypothesis at depth `n`; `cum-mono-Supp`/`>>=ₚ-boundA`/`>>=ₚ-boundB` are already
support-shaped. ~12 lines, plus a new `Dp.Dominate → Dp.Support` import. This is
the whole of the "support-sensitive averaging" the exploratory signature asks
for — the substrate exists.

**(c) `Refine`: no change.** `Refine` (`Dominated.agda:84`-`:130`) re-exports
`pointᵍ`/`onRᵍ`/`Φ` through `open Ext … public` (`:87`), which is everything
`CovInitial` mentions; `dstrat`/`dstrat-asks`/`obsᵍ`/`fwd`/`bwd` are
invariant-free and the ε-side `skeleton` never sees `Cov`.

**(d) `eventSkeleton`: one clause.** With

```agda
CovInitial B q report (N , cert , _) =
  (f : ℕ) (z : AtMost Φ 0) → z ∈ₚ pointᵍ
  → Cov false f (Φ (proj₁ z) ℕ.+ q) (onRᵍ (proj₁ z) tt)

allZero⇒initial : CovCtx B q report kb → CovInitial B q report kb
allZero⇒initial cov f z _ = cov f z
```

the only edit is `fwdᵂ` (`:249`-`:251`), which becomes
`dom≤-bindˢ … (supp-∈ _ pointᵍ λ z i → runFwdᵂ f (proj₁ z) (cov f z i))`.
`runFwdᵂ`, `Cov`, `cov-ind`, `bound`, `to-obs` are untouched. Because
`allZero⇒initial` is a one-liner, the discharged `c + 1` theorem
(`EventLift.agda:144`) survives the change verbatim.

**(e) What would still be missing — a separate concrete obligation.** Proving
`eventSkeleton-initial` establishes nothing about the rate. Obtaining
`CovInitial` for a rate-`c` monitor certificate additionally needs:

1. The rate-`c` certificate `certᶜ : Certified c watchᴹ` — *already verified to
   exist* by the spike in §3, ~35 lines shorter than `certᵂ`. This one is free.
2. An inversion of `_∈ₚ_` along `mapₚ` —
   `y ∈ₚ mapₚ h d → Σ[ x ∈ A ] x ∈ₚ d × y ≡ h x` — to read off
   `pointᶜ = mapₚ (λ z → ((idle , proj₁ z) , (false , nothing)) , _) qE.pointᵍ`
   (`Cov.agda:200`) that every supported initial configuration is
   `((idle , _) , (false , nothing))`. `Dp.Support` has only the forward
   `Supp-bind` (`:46`); no `mapₚ`/`>>=ₚ` inversion exists. ~20-30 lines.
3. `covᶜ` then replaces the three `⊥-elim (owed z)` clauses (`:277`-`:279`) by
   that inversion and keeps the single real clause (`:275`) and the whole
   `covTree`/`covLeaf`/`covVal` induction verbatim.

That is four pieces in three modules (`Dp.Support`, `Dp.Dominate`,
`UC.Machine.Dominated`, plus a `Cov` variant); one of the four (item 1) is
spike-verified, the other three are unwritten, and no consumer is waiting. And landing all four would still only turn `hitsᵘ`'s `q + 1`
(`EventLift.agda:160`) into `q` and the ledger appendix's `q + q + 1`
(`docs/quantitative-family.md`, "Decisions recorded" 1) into `q + q` — a public
statement change, i.e. a maintainer ruling, not a refactor.

### 5. Verdict — retain

Retain `CovCtx`, `eventSkeleton`, `covCtx` and the `c + 1` rate as they stand.

- The cost is one **additive** unit of query allowance on a premise that
  `eventDominatedᶜ` (`EventLift.agda:124`) already exposes as a parameter
  (`k` and `kb` are quantified there), so a consumer that later obtains a
  sharper certificate can use the lift at its own rate without touching
  `UC.Machine.Dominated`. The coupling the interface is accused of is already
  parameterised away.
- No localized refactor is proposed. §4 is a new library predicate, two new
  library lemmas, a rewritten `Cov.agda` and a new `eventSkeleton` theorem —
  perhaps 80 new lines plus the rewrite, so over the bound, but size is not the
  blocker. The blocker is that it is **not statement-preserving in its public
  consequence**: it exists only to change `q + 1` to `q` in `hitsᵘ` and
  `q + q + 1` to `q + q` in the ledger appendix, both ruled public statements
  (`docs/quantitative-family.md`, "Decisions recorded" 1). There is no named
  consumer whose *simplification* it would buy — `hitsᴸ` and
  `hits⇒bounded` would be no simpler, only differently numbered — and §4(b)'s
  `eventSkeleton-initial` is the substantive unproved obligation, exactly as the
  work-package brief warns.
- One documentation defect should be corrected by WP6 rather than by a source
  edit: the phrasing "at the test's own rate `c` the premise is not merely
  unproved but false" (`EventLift.agda:137`-`:143`, and "`c + 1` is optimal for
  the invariant, not slack" in "Stage B status, corrections 2026-09-22 (2)"
  above) is accurate of the certificate `covCtx` builds but reads as a claim
  about every `QB c`. `Cov.agda:7`-`:16` is already correctly scoped to the
  certificate. See §6.

### 6. What is and is not established about `q + 1`

**Established.**

1. `eventDominatedᵘ` (`EventLift.agda:144`) and `hitsᵘ` (`:160`) are theorems at
   `c + 1` / `q + 1`, `--safe`, no postulate, hypothesis read at
   `asks≤ (c ℕ.+ 1)`.
2. For the certificate `covCtx` constructs (`Cov.agda:308`) — the collapsed
   tower `watchᴹ` — `CovCtx`'s all-zero-potential-state quantifier forces the
   accumulator to carry potential, and since `pend ≤ 1` (`:96`) the cost is one
   additive unit, not a factor (§3).
3. With a zero-potential accumulator the invariant is refutable, by the
   `((idle , se) , (true , nothing))` entry at `qE.Φ se = 0` (§3). This is a
   refutation **scheme**: it needs a test `E` with a zero-potential state that
   answers. No such counterexample is constructed in Agda anywhere in the repo,
   and the claim is reasoning about the clause, not a machine-checked `¬`.
4. The `+ 1` is attributable to `CovCtx` **alone**, not to the certificate: a
   rate-`c` `Certified c watchᴹ` of the same collapsed tower typechecks (§3,
   spike). So the accounting question and the invariant question are separable,
   and the public number is set by the invariant.

**Not established.**

(a) *No lower bound over certificates.* `QB c M = Σ[ N ] Certified c N × N ≈ᴹ M`
    (`UC/QueryBound.agda:287`) quantifies the representative, and
    `eventDominatedᶜ` quantifies both the rate `k` and the certificate `kb`.
    Nothing rules out some other `N ≈ᴹ Kctx (openedᴹ …) m` whose potential funds
    the accumulator out of slack the test already carries. "The premise is false
    at rate `c`" is established of `covCtx`'s certificate, not of every `QB c`.

(b) *No lower bound over lifts.* The all-zero-potential-state quantifier is a
    design choice made because `dom≤-bind` (`Dominate.agda:158`) is
    everywhere-quantified (§2), and the §3 refutation does **not** survive
    restriction to the initial support: every leaf of `pointᵂ` (`Cov.agda:200`)
    carries `(false , nothing)`, precisely the shape the refutation needs to
    exclude. So the failure of a zero-potential invariant at rate `q` is *not*
    evidence that a sound contextual event lift needs `q + 1` — and, given
    Established 4, the natural rate-`c` certificate is available to any such
    lift.

(c) *No sharper bound is in hand.* Neither `dom≤-bindˢ`, nor `supp-∈`, nor
    `certᶜ`, nor the `mapₚ` inversion exists. Nothing here promises `q`.

**Phrasing WP6 can use.** "`hitsᵘ` reads its strategy hypothesis one query past
the environment's cap. That unit funds the monitor's accumulator in the
certificate the lift is discharged with, and is optimal for that certificate
under the invariant's all-zero-potential-state quantifier. It is not claimed to
be necessary for every sound contextual event lift, nor for every rate-`c`
certificate of the compiled context."

That phrasing is now carried by check 2 of `docs/quantitative-family.md` §14, which is the current scope statement for the `c + 1` lift; the line "`c + 1` is optimal for the invariant, not slack" in "Stage B status, corrections 2026-09-22 (2)" above is a historical record and is superseded by it.

## WP3 audit (2026-09-23)

The event-bound layer re-audited against the CURRENT module graph, after the
2026-09-22 retirements and the WP1/WP2/WP5 work. Baseline `fbc2cf30`; every
"consumer" column below is a whole-`src` grep with identifier delimiters, run
with the defining file excluded, so "internal" means *used in its own module
only*. Layers are the WP3 plan's table.

**Status at `4aa8d3a9`.** The module is `UC.Machine.EventBounds` (moved at
`df554527`) and `Readout` is `Reader`, whose one instance is `Monitor.compileᴹ`
(`readoutᴹ` is gone). `ctxRun-∘`, `qbᵢ-monitor`, `monitor-query`/`-answer`/`-flag`
and `cov-true`/`covL-true` were deleted at `1f19f73d`; the `EventSkeleton` and
`Skeleton` aliases were unfolded into their theorems at `8a61627a`. The rows below
carry these updates; the rest of the audit is as of `fbc2cf30`.

| # | Layer | Responsibility |
|---|---|---|
| L1 | `Dp.Advantage` or a focused sibling | `Upper` and numerical comparison transport |
| L2 | generic preservation (WP1) | admission, absorption, bound transport |
| L3 | `UC.Machine.EventBounds` | concrete event readouts, capped contextual bounds |
| L4 | `UC.Machine.Monitor.*` | compiler, machine agreement, resource certificates |
| L5 | `UC.Seam.EventTransfer`, `UC.Quantitative.EventLift*` | event-sensitive operational adequacy |
| L6 | ledger modules | reports, truthfulness, birthday bound, concrete property |

### Entry points

| Name | Module | Layer | Consumer | Verdict |
|---|---|---|---|---|
| `Reader` | `UC/Machine/EventBounds` | L3 | `Monitor.compileᴹ` | in place |
| `readRun` | `UC/Machine/EventBounds` | L3 | `Monitor.eventRun` | in place |
| `BoundedAt` | `UC/Machine/EventBounds` | L3 | `EventLift.HitsAt` | in place |
| `Boundedᶠ` / `Boundedᴺ` | `UC/Machine/EventBounds` | L3 | `EventLift.Hitsᶠ`/`Hitsᴺ` | in place |
| `boundedᶠ⇒boundedᴺ` | `UC/Machine/EventBounds` | L3 | `EventLift.hitsᶠ⇒hitsᴺ` | in place |
| `ctxRun-∘` | `UC/Machine/EventBounds` | L3 | **none** | deleted at `1f19f73d` |
| `Flagᴵ`, `MonSt`, `FlagSt` | `UC/Machine/Monitor` | L4 | Agree, Slide, Cov, EventLift, Property | in place |
| `monitorStep`, `flagReadStep` | `UC/Machine/Monitor` | L4 | internal | in place — the observer's update rules, public by the plan's "monitors as observer constructions" |
| `monitorᴹ`, `flagReadᴹ`, `compileᴹ` | `UC/Machine/Monitor` | L4 | Agree, Slide, Cov, EventLift, Property | in place |
| `eventRun` | `UC/Machine/Monitor` | L4 | EventLift, Agree | in place (here, not with the bounds: `Agree` and `EventLift` both need it and the second imports the first); `readoutᴹ` is gone |
| `qbᵢ-monitor` | `UC/Machine/Monitor` | L4 | **none** | deleted at `1f19f73d`; Cov's comment now states the zero-potential point without it |
| `monitor-query`/`-answer`/`-flag` | `UC/Machine/Monitor` | L4 | **none** | deleted at `1f19f73d` |
| `agree`, `stratTest`, `stratTest-embeds`, `m₀` | `UC/Machine/Monitor/Agree` | L4 | EventLift | in place |
| `mon-wire`, `monᴹ`, `module Read`, `module Watch` | `UC/Machine/Monitor/Agree` | L4 | Slide, Cov | in place |
| `watch-collapsed` | `UC/Machine/Monitor/Slide` | L4 | internal (`watch-resp-≈`) | in place |
| `watch-resp-≈`, `closedᴹ`, `compiled-slide` | `UC/Machine/Monitor/Slide` | L4 | Cov | in place |
| `relay-slide` | `UC/Machine/Monitor/Slide` | L4 | internal (`compiled-slide`) | moved 2026-09-30 from `UC/Machine/Slide/Relay` into its only consumer; still out of `UC.Machine.Slide` by the measured 17 s |
| `Cov`, `CovL` | `UC/Seam/EventTransfer` | L5 | Dominated, Cov | in place |
| `cov-bot` | `UC/Seam/EventTransfer` | L5 | Cov | in place |
| `cov-true`, `covL-true` | `UC/Seam/EventTransfer` | L5 | **none** | deleted as a pair at `1f19f73d` |
| `module Watched` internals | `UC/Seam/EventTransfer` | L5 | internal | in place |
| `runFwdᵂ` | `UC/Seam/EventTransfer` | L5 | Dominated | in place |
| `Skeleton`, `skeleton`, `skeleton⇒dominated` | `UC/Machine/Dominated` | — | internal (`dominated`) | `skeleton` in place; `Skeleton` unfolded and `skeleton⇒dominated` inlined into `dominated` at `8a61627a` |
| `dominated` | `UC/Machine/Dominated` | — | `UC/Model/Dominated`, `GamePlaying/Hop` | in place |
| `CovCtx` | `UC/Machine/Dominated` | L5 | EventLift, Cov | in place |
| `EventSkeleton` | `UC/Machine/Dominated` | L5 | internal, ONE use (the type of `eventSkeleton`) | inlined at `8a61627a` |
| `eventSkeleton` | `UC/Machine/Dominated` | L5 | EventLift | kept HERE, not under `EventLift*`: it shares `module Refine` (`dstrat`, `obsᵍ`, `to-obs`) with the plain `skeleton`, and moving it would export that scaffolding (rule 28 beats the table row) |
| `HitsAt`, `Hitsᶠ`, `Hitsᴺ`, `hitsᶠ⇒hitsᴺ` | `UC/Quantitative/EventLift` | L5 | Property | in place |
| `openedᴹ`, `eventRun-closed` | `UC/Quantitative/EventLift` | L5 | internal | in place |
| `eventDominatedᶜ` | `UC/Quantitative/EventLift` | L5 | `eventDominatedᵘ` | in place — see the conditional-lift list |
| `eventDominatedᵘ` | `UC/Quantitative/EventLift` | L5 | `hitsᵘ` | in place |
| `hitsᵘ` | `UC/Quantitative/EventLift` | L5 | Property | in place |
| `qb-stratTest` | `UC/Quantitative/EventLift` | L4 by the table | internal (`hits⇒bounded`) | table says "resource certificates" belong with `Monitor.*`, and `stratTest` lives in `Monitor/Agree`; move DECLINED — see below |
| `hits⇒bounded` | `UC/Quantitative/EventLift` | L5 | Property | in place |
| `upper-run`, `run-upper` | was `UC/Quantitative/EventLift` | **L1** | Property, Transfer, `hits⇒bounded` | MOVED to `Protocol/Machine/Agree` |
| `covCtx` | `UC/Quantitative/EventLift/Cov` | L5 | EventLift | in place |
| `qb-closedᴹ`, `module Cert` | `UC/Quantitative/EventLift/Cov` | L5 | internal | in place |
| `AuditEvent`, `AuditBound`, `pinned`, `pinned-bound` | `UC/Audit` | L2 | `UC/Seam/Audit` (+`.Context`), `HashForward/Audit` | in place |
| `absorb`, `Absorbs`, `absorb-absorbs` | `UC/Audit` | L2 | `UC/Seam/Audit`, `HashForward/Audit` | in place |
| `carry-obs`, `audit-carryᵉ`, `audit-carry` | `UC/Audit` | L2 | `UC/Seam/Audit`, `HashForward/Audit` | in place |
| `SerInj`, `LedgerIf^ω`, `εᴸ`, `εᴹ`, `εᴹ-negligible`, `genesisAt`, `Ideal`, `auditWatch`, `PreservesValue`, `hitsᴸ`, `preservesValue⇒saturated`, `ideal-bounded`, `ideal-preserves-value` | `ChimericLedger/Property` | L6 | Transfer, Serialize | in place |
| `εᴸ-negligible`, `auditMonitorᶠ`, `0≤εᴸ` | `ChimericLedger/Property` | L6 | internal / Transfer | in place |
| `reportsLoss`, `auditWatchFrom`, `auditWatch`, `withAudits`, `asks≤-withAudits`, `badTotal`, `lostValue`, `TrajectoryLossBounded`, `auditWatch-complete`, `auditWatch-bounded` | `ChimericLedger/Observable` | L6 | Property, Transfer, Birthday, Replay | in place |
| `AuditLossBounded`, `auditWatch-sound` | `ChimericLedger/Observable` | L6 | **none** | keep — each is one half of a stated pair (`Trajectory…`/`Audit…`, sound/complete) |
| everything in `ChimericLedger/Transfer` | `ChimericLedger/Transfer` | L6 | **none** | expected: this module is the headline, not a dependency (working rule 5) |

### Surviving conditional lift entry points

Exactly one remains: `EventLift.eventDominatedᶜ`, taking `(k : ℕ) (kb : QB k …)`
and `CovCtx B k report kb` as premises. Its only client is `eventDominatedᵘ` in
the same module, which discharges both with `Cov.covCtx` at `k = c + 1`; `hitsᵘ`
then rescales to the cap and is what the ledger calls. Nothing else in the tree
takes a `CovCtx`- or `EventDominated`-shaped premise — `UC.Quantitative.Hits`'
`EventDominated`, `eventDominated` and `ledger-hitsᶜ` are all gone. So the
supported route has one entry point per stage and one implementation of the
substantive proof (`Dominated.eventSkeleton`); no abandoned duplicate was found
to remove.

### Ruled orphans — one-line recommendations

These are the maintainer's to rule; none was touched. The first three were
deleted at `1f19f73d` (see the status note above).

- `Monitor.monitor-query` / `-answer` / `-flag` — **keep as pins**: three `refl`
  equations fixing the observer's update rules, which the plan wants public.
- `Monitor.qbᵢ-monitor` — **keep as pin**: `EventLift/Cov`'s header cites its
  constantly-zero potential as the reason the five-fold `qb-∘` tower cannot
  carry `CovCtx`; deleting it makes that explanation dangle.
- `EventBounds.ctxRun-∘` — **keep as pin**: the one statement in the tree saying
  simulator absorption is an *equation between observations* at the machine
  layer, which `UC.Audit.absorb` only has as a map on event classes.
All four `Quantitative.Family` items below are in `UC/Quantitative/Family.agda`
(`:176`, `:179`, `:187`, `:192`, `:304`, `:314`, `:328`, `:576`), each appearing
only at its own definition.

- `Quantitative.Family.≈ctx-refl` / `-sym` / `-≤` — **keep**: the equivalence
  structure of the primary quantitative relation; a relation without them
  reads as accidental.
- `≈ᵁ⇒≈ctx` — **keep**: the qualitative-to-quantitative direction, the only
  in-tree statement that exact agreement is a zero-error contextual bound.
- `≤UC^ωᵉ⇒⁺`, `≤UC^ωᵉ⁺⇒`, `≤UC^ωᵉ-∙`, `_≤UC^ωᵉ⁺_` — **delete as a block, or
  keep as a block**: after WP2 made `_≤UC[_,_]_` primary, the primed witness
  bundle and its two transfer directions have no caller; they are only worth
  keeping if the maintainer still wants an existentially hidden witness form.
  Splitting them is the rule-26 error.

### Moves performed

- `upper-run`, `run-upper`: `UC/Quantitative/EventLift.agda` →
  `Protocol/Machine/Agree.agda`, statements unchanged. They contain no event,
  monitor or readout content — they are `prAgree` read as a one-sided bound in
  each direction, i.e. the plan table's L1 row and the WP0 inventory's
  "Protocols → machines" boundary, not the event layer. The smell was concrete:
  `Examples/ChimericLedger/Transfer.agda` imported
  `UC.Quantitative.EventLift` for `upper-run` and nothing else. Importers
  repointed (`Property`, `Transfer`); no forwarding re-export left behind.

Move CONSIDERED and DECLINED: `EventLift.qb-stratTest` → `Monitor/Agree.agda`.
The table assigns resource certificates to `Monitor.*` and `stratTest` is
defined there, but `Monitor/Agree` is the layer's largest module (562 lines) and
imports neither `UC.Seam.Budget` nor `UC.QueryBound.Compose.Laws`; adding both
for one lemma buys a placement point at deserialization cost on a heavy module —
the same trade `UC/Machine/Slide/Relay.agda` was split out to avoid (rule 31).
It stays beside its only consumer, `hits⇒bounded`.

### Other edits

- `EventLift/Cov.agda`: the comment on `covCtx` named the retired
  `EventLift.eventDominated`; corrected to `eventDominatedᶜ`. It was the only
  reference to a retired name left anywhere under `src/` (all of `Hits`,
  `Saturated`, `Asymptotic*`, `Monitor.Tight`, `Charge`, `Seam.Carry`,
  `Protocol.Live` were grepped).
- `ChimericLedger/Property.auditWatch-IsWatch` re-proved, term for term, what
  `Strategy.watchFrom-IsWatch` already proves (`auditWatchFrom` is
  `watchFrom reportsLoss` definitionally). Body replaced by the library lemma;
  statement unchanged. (Both it and `Observable.asks≤-auditWatch` were later
  inlined as the library lemmas they forwarded to.)

### Plan items 3, 4, 5

3. **Event selection vs event construction stay distinct.** `UC.Audit.AuditEvent`
   is a CLASS of permitted contexts at an arbitrary base; `EventBounds.Readout`
   is a way of BUILDING the test. No comment anywhere asserts an equivalence —
   `EventBounds`' header says outright that "the two are not identified —
   bridging them is the sealed model's job", and `Readout` is named in only
   three places, all of them `UC/Machine/Monitor.agda` constructing one. Nothing
   to correct.
4. **No generic module imports the ledger.** `grep` for
   `import CategoricalCrypto.Examples` under `UC/`, `Protocol*` and `Strategy*`
   is empty; the six surviving mentions of `ChimericLedger` under `UC/` are
   comment pointers ("`Examples.ChimericLedger.Observable.auditWatchFrom`" and
   the like), which is the intended direction of citation. Reports
   (`reportsLoss`) and initialization (`genesisAt`, `h₀`, `Ideal`) are all in
   the example layer.
5. **`PreservesValue` reaches the proved lift unconditionally.**
   `PreservesValue R = Hitsᴺ (λ n → morphism (R n)) auditMonitorᶠ εᴹ`, and every
   positive instance goes through `hitsᴸ = hitsᵘ …`, which calls
   `eventDominatedᵘ`, which discharges `CovCtx` internally with `Cov.covCtx`.
   No `EventDominated`, invariant or reachability premise is exposed. The
   quantifiers are as the WP0 inventory records them: `Boundedᴺ ε` is
   `(p : ℕ → ℕ) → Poly p → Σ[ ν ] Negligible ν × ((n : ℕ) → BoundedAt (p n)
   (ε n (p n) + ν n) …)` — cap first, then slack, then level, then context —
   and `BoundedAt q r` caps `ctxBudget c c′ ≤ q`. Unchanged by this work
   package.

### Plan item 6 — the trajectory ruling

Plan item 6 ("preserve useful strategy-level results … do not weaken a sharper
trajectory theorem solely to reuse a coarser contextual bound") does **not**
apply to `Transfer.ledger-uc-to-pov-family`. By the maintainer's 2026-09-22
ruling that appendix reads its schedule at `εᴹ n (p n + p n)`, i.e.
`εᴸ n (q + q + 1)`: it is routed through claim 1
(`preserves-value-transfer` → `Property.preservesValue⇒saturated` →
`withAudits`' doubling → `TruthfulAudit`), and the sharper strategy-level route
was retired deliberately. That number is the public type and is NOT to be
restored to the older one; item 6 governs future cases only. Verified present
and unchanged at `Transfer.agda`'s `ledger-uc-to-pov-family`.
