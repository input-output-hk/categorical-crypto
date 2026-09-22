# Event bounds in the setup's own vocabulary

Original baseline: `protocol-rewrite` at `9d33f783`. Paths below are relative to
`src/CategoricalCrypto/` unless prefixed with `docs/`. Recheck current signatures
before implementation. Definitions and theorem shapes marked as proposed are
specifications, not checked Agda declarations.

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
   with `asks≤-auditWatch`, not merely a certificate for the relay itself.

`QB 1 μ` is not by itself `QueryPreserving`: it is a rate certificate for a
process, not a proof that the compiled experiment spends the original allowance.
State and prove the actual allowance transformation. If it can be expressed as
`κμ(n,q)`, record its exactness or upper-bound status and polynomial closure.
If it depends separately on the test and closure budgets, retain those
arguments; do not assume it factors through `ctxBudget c c′`. In particular,
check zero allowance explicitly.

**Acceptance:** the monitor compiler has both semantic agreement and a proved
budget transformation. Typechecking a flag projection alone is insufficient.

## 3. Fixed-allowance and saturated event bounds

Let a base context `C` consist of:

```text
W, E : W ⊗ (X ⊗ B) → Ω, m : 𝟙 → W ⊗ 𝟙,
QB c E, QB c′ m.

allow(C) = ctxBudget c c′.
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
ε(n,q) + δ(n,simCost(q,cost(s,n))).
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
  at the certificate level, where `asks≤-auditWatch` is exact. The over-charge is
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
`UC/Audit.agda`'s header names the very gap `Hits` closes ("quantifying
over every budgeted test … bounds the mass of a constant-`true` verdict too"); making the
verdict be the flag is the proposed repair, subject to semantic adequacy.

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

This is a proposed model-specific proof, not a law of an arbitrary `Budget`.
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
