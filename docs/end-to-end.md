# The end-to-end asymptotic UC-to-POV theorem

Status of the completion goal of
[the implementation review](protocol-implementation-review.md), on branch
`end-to-end` off `protocol-rewrite`. Everything below is a checked term unless
marked otherwise; hatches stay at zero in `src/`.

## The public theorem

`CategoricalCrypto.Examples.ChimericLedger.EndToEnd`, parameterized by a
per-level serialization `ser : (n : ℕ) → Ledger.Tx n → List Bool`:

```agda
ledger-uc-to-pov :
    (a V : ℕ) → SerInj → (R : Systems LedgerIf^ω) (badR : Bad R)
  → ((n : ℕ) → TotalRun (LedgerIf^ω n) (morphism (R n)))
  → R ≤UC^ω Ideal a V
  → TruthfulAudit a V R badR
  → SaturatedHitᴺ R badR (λ n q → εᴸ n (q + q))
```

and, the same conclusion read as one number,

```agda
ledger-pov-negligible :
    … → (p : ℕ → ℕ) → Poly p
  → Σ[ f ∈ (ℕ → ℚ) ] Negligible f
    × ((n : ℕ) (d : Strats n) → asks≤ (p n) d → PrHit (R n) (badR n) d ≤ f n)
```

Unfolded, the first says: for every polynomial allowance `p` there is a
negligible `νₚ` such that no strategy of query budget `p n` moves the real
system's total value away from genesis with probability above
`((2·p n)² + 2·p n)·2⁻ⁿ + νₚ n`. The second bundles the two summands and
says the whole thing is negligible.

### Hypotheses, and why each is allowed

| hypothesis | status |
|---|---|
| `SerInj` | the birthday theorem's own injective-serialization assumption, per level (`Tx` depends on the hash width, so one `ser` cannot be typed) |
| `R ≤UC^ω Ideal a V` | the UC-emulation premise: the INHERITED `_≤UC_` at each level, a simulator per dummy adversary. Never `Agreeˢ` |
| `TotalRun … (morphism (R n))` | the real side's admissibility. Not decoration — with the real side divergent, a simulator that never starts emulates every ideal. Discharged for any dead-free protocol by `Protocol.Live` + `totalRun-morphism`; the IDEAL side's copy is proved (`ChimericLedger.Total`) |
| `TruthfulAudit a V R badR` | the real implementation's audit-to-trajectory connection, which the review's schematic lists as a hypothesis. UC identifies no internal state trajectory. For a ledger image it is `Trajectory.monitor-complete` (`Schedule.ideal-truthful`) |

No other hypothesis appears, and none of the four stands in for work items 1–5.

## Acceptance requirements

1. **Family instantiation + negligibility — DONE.**
   `ChimericLedger.Schedule` takes hash width `ℓ n = n`, genesis hash
   `replicate n false`, and per-level `ser n`. `εᴸ n q = (q²+q)·2⁻ⁿ` and
   `εᴸ-negligible : NegligibleBound εᴸ` is proved from
   `UC.Approximate.Decay.negligibleBound-inv-pow-2`, which is generic in the
   numerator polynomial and in the schedule (`n ≤ sch n` is all it spends).
   The ideal side is `Birthday.target` read through
   `Trajectory.monitor-bounded`. **Design choice:** serialization is scheduled
   (`ser : (n : ℕ) → Tx n → List Bool`, `SerInj` its levelwise injectivity)
   rather than per-level-ad-hoc; it is forced, since `Tx` depends on `ℓ`.

2. **Family UC setup + consuming adequacy — PARTLY DONE.**
   `UC.Model.Family.ucSetup^ω` is a closed term: `UC.Family.Monoidal`
   instantiated at the sealed bundle, with `approximateᵒ` supplied (the
   approximation `observationᵒ`'s equivalence was induced from, so `induces` is
   the identity). The emulation premise is CONSUMED, not assumed: `uc-agree`
   spends `UC.Seam.Grounded.unitGrade`, which in turn spends `adequacy`,
   `prAgree` and `stratIsEnv` — the proved lift, never an assumed one.
   **Remaining:** the frontend-to-family ingestion,
   `layer-1 bound ⇒ UC.Family._≈ℰ[ ε ]_`, which would consume
   `UC.Machine.Dominated.dominated`. See the obstruction below.

3. **Robustness of the designated event — DONE at the class level.**
   `UC.Asymptotic.Audit.uc-audit-carry` carries the ideal `AuditBound` (supplied by
   `ChimericLedger.Audit.audit-target`, i.e. by the proved birthday theorem)
   across a budgeted emulation at the real-side class
   `absorb (sim em) cs (watched …)` — the largest class closed into the ideal
   one, exhibited by the proved `absorb-absorbs`. Nothing is assumed about
   the real side. At the ledger this is
   `ChimericLedger.EndToEnd.ledger-audit-carry`.

4. **Costs explicit — DONE, split across the two routes.**
   The audit instrumentation's cost is charged in the main theorem: `audited d`
   asks twice what `d` asks (`POV.asks≤-audited`), so the allowance `p` is
   evaluated at `p + p` and that appears in the conclusion's bound. The
   simulator's cost is charged in the graded route: `ledger-audit-carry`'s
   bound is `εᴸ n (simCost q (cs n)) + ν n`. The negligible-slack closure runs
   with the repaired quantifier order throughout —
   `saturated-respects[ Negligible ]` via `≈negl-respects`, allowance first,
   slack second.

5. **Real trajectory recovered — DONE.**
   `UC.Asymptotic.saturatedHitᴺ-from-monitor` turns a monitor bound into a
   trajectory bound through the implementation's truthful-audit connection,
   with the instrumentation and its allowance cost as explicit parameters.

6. **One public theorem — DONE.** `ChimericLedger.EndToEnd`;
   `UC.Asymptotic` and `UC.Asymptotic.Audit` are re-exported from `UC`.

## The obstruction: why the graded route stops short of a probability

`uc-audit-carry` ends at an `AuditBound` on the real side. Turning that back
into a layer-1 `Bounded` needs `UC.Seam.Audit.Bounded.auditIsBounded`, whose
extraction context must lie in the real-side event class. With the class taken
to be `absorb s cs (watched I bad)`, that asks: the extraction context with the
simulator in front of it, plugged into the IDEAL machine, observes exactly
(`≈ₚ`) an ideal monitored run. It does not. The simulator's own initialization
makes the observation ε-close and no more — that is precisely what
`UC.Seam.Grounded.subBlind` proves, and all an almost-sure totality can prove.
The same gap appears from the other side: `Absorbs s cs (watched R badR)
(watched I badI)` relates a REAL monitored run to an IDEAL one, which an
emulation gives only up to vanishing error while `watched` demands equality.

So the two routes do not compose, and the probability conclusion is obtained
instead through the trivial-grade collapse, where the simulator is provably
blind. One consequence is honest and should not be glossed: at the trivial
grade the simulator costs the ideal side nothing, so the main theorem's bound
is the birthday bound at the audit-adjusted allowance, not a `simCost`-adjusted
one. The `simCost`-adjusted statement is `ledger-audit-carry`'s, at the graded
end.

Closing the gap needs one of:

* an event class permitting contexts whose observation is `≈ₚ` only up to a
  prefix of almost-surely-total silent computation, with `boundedIsAudit` and
  `auditIsBounded` reproved at it (the `Prefixedᵒ`/`Massedᵒ` machinery of
  `UC.Seam.Grounding.Prefix` is the substrate); or
* an exactly-total simulator hypothesis, which is close to assuming `s ≈ id`
  and therefore not worth the statement.

## Continuation spec

In priority order.

1. **Family ingestion (requirement 2's remainder).** DONE.
   `UC.Model.Dominated.ContextDominatedᵒ` is `UC.Machine.Bridge`'s domination
   with its ancilla quantified over SEAL objects — the quantifier
   `UC.Family._≈ℰ[_]_` has — and `dominatedᵒ` proves it from `dominated` read
   at `UC.Model.Seal.objᵒ X`. What looked like a blocker was not one:
   `ifaceᵒ` IS onto, `retᴵ` inverting `⟦_⟧ᴵ` definitionally, and `objᵒ` now
   exports that section from inside the seal (`ifaceᵒ-onto`), so nothing is
   restricted to an image and nothing existing is weakened.
   `UC.Model.Family.Ingest` then spends it: `ingest` takes a per-level
   advantage bound at every budget (`_≈advᴹ[_]_`) to `_≈ℰ[ ε + δ ]_`, and
   `ingest-≈ℰ` / `ingest-≈ℰⁿ` / `ingest-≤UC` collapse it through
   `absorb-negl`, `_≈ℰⁿ_` and `UC.Emulation.≈ℰ⇒≤UC`, where `≤UC-trans` and
   `dummy-complete` apply. The `δ` is the domination's own arbitrary positive
   slack, absorbed by `UC.Approximate.GradedBound-+[_]`; any positive
   negligible `δ` will do (`Approximate.Decay.negligible-slack`).
   What is *not* reached is `UC-compose` on these families: it is a theorem of
   `ucSetup^ω`, stated in `_≈ᵁ_`, and the identification of that relation with
   the core's `_≈ℰ_` is proved at the model only (`UC.Model.Bridge`, over
   `UC.Model.Reading`). The argument is generic in the base — the one step with
   content is `μ Y X ∘ T₁ Y f ≈ α⇐ ∘ id ⊗₁ f` — but it is written at `𝔾ᵒ`, and
   factoring it out is a refactor of two perf-priced Model modules, plus a
   transport between `Grading^ω` and `gradingᵗ Famᴹ` (same underlying homs,
   different carried polynomial). That is the next piece of this item.

2. **The prefix-tolerant event class** (the obstruction above), after which
   `uc-audit-carry` reaches a probability and the main theorem can charge
   `simCost`.

3. **A concrete real system.** Everything here is generic in `R`; a worked
   instance (a ledger over a Merkle–Damgård hash rather than a random oracle,
   say — `Examples.MerkleDamgard` is ported) would exercise the premise instead
   of assuming it. That is a cryptographic-construction obligation, which the
   review explicitly places outside this scope.

4. **`≈ℰⁿ` as an `Observation`** — the redesign `UC.Family`'s closing comment
   prices. Not attempted; not needed by anything above, since the negligible
   tier consumers use lives at layer 1 (`UC.Saturated`).

## Modules added

| module | LOC | warm |
|---|---|---|
| `UC.Approximate.Decay` | 85 | 5 s |
| `Protocol.Live` | 139 | 7 s |
| `UC.Asymptotic` | 123 | 10 s |
| `UC.Asymptotic.Audit` | 56 | 10 s |
| `UC.Model.Family` | 45 | 10 s |
| `Examples.ChimericLedger.Total` | 47 | 9 s |
| `Examples.ChimericLedger.Schedule` | 127 | 10 s |
| `Examples.ChimericLedger.EndToEnd` | 147 | 17 s |

Additive edits to existing modules: `POV.asks≤-audited` (the instrumentation's
allowance cost, beside `audited`); `Carry.Emulᵁᶜ`/`emulᵁᶜ`/`pov-carryᵁᶜ` (the
UC-vocabulary premise, the first importer of `unitGrade`); `UC.Seam.Audit`
re-exports `≤UC[]⇒≤UC`; `UC` re-exports the two `UC.Asymptotic` modules.

A perf note worth keeping: the two carries in ONE module cost 127 s warm and
in two cost 10 + 10 s. Neither half is expensive; the collapse's seal-level
terms and the audit event's `TrivialGrade` instantiation are expensive
together.

## Two review-sweep items, resolved here

* **`unitGrade` was unreachable.** It now has two importers:
  `UC.Asymptotic.uc-agree` (the family) and `ChimericLedger.Carry.emulᵁᶜ` (the
  example), and `Carry` gained `Emulᵁᶜ` so its public premise is `≤UC` rather
  than a raw `Agreeˢ`.
* **`UC.QueryBound.QB` at open machines.** Not needed. The probability route
  spends no `QB` at all — its budgets are strategy `asks≤` — and the graded
  route spends only the already-proved `qb-∘`/`qb-T₁`/`qb-sub` inside
  `UC.Audit.audit-carry`. No new `QB` reasoning is introduced anywhere here, so
  the `behᵍ`-shaped `≈ᴹ`-transport lemma the sweep flagged stays owed by
  whoever first needs it.
