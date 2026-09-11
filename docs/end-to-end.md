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
| `TruthfulAudit a V R badR` | the real implementation's audit-to-trajectory connection, which the review's schematic lists as a hypothesis. UC identifies no internal state trajectory. For a ledger image it is `Trajectory.monitor-complete` (`Schedule.ideal-truthful`, `Real.real-truthful`) |

No other hypothesis appears, and none of the four stands in for work items 1–5.

### The corollary at a real ledger

`CategoricalCrypto.Examples.ChimericLedger.Real`, same parameter, at the real
family `Real n = ledger vr (genesis n) ∘ᵖ hash n` for a hash implementation
`hash n : Protocol unitᴵ HashIf` with `NoDeadStep (hash n)`:

```agda
ledger-pov : SerInj → Real ≤UC^ω Ideal a V → (p : ℕ → ℕ) → Poly p
           → Σ[ f ∈ (ℕ → ℚ) ] Negligible f
             × ((n : ℕ) (d : Strats n) → asks≤ (p n) d → PrHit (Real n) (badReal n) d ≤ f n)
```

Two substantive premises — the injective serialization and the emulation — and
one probability, which is `ledger-pov-negligible`'s. The three hypotheses the
generic theorem carries about `R` are discharged once and for all at this
family:

| hypothesis | discharged by |
|---|---|
| `Bad Real` | `badReal n = badTotal (genesis n)`: the POV event itself, which reads the ledger's state and not the hash's |
| `TotalRun … (morphism (Real n))` | `Total.totalRun-Sys`, generic in the hash: the ledger writes no `dead` and `_∘ᵖ_` creates none, so the real side owes only `NoDeadStep (hash n)` |
| `TruthfulAudit a V Real badReal` | `Trajectory.monitor-complete`, generic in the hash: an audit query is answered out of the LEDGER's state whatever it hashes with, so the ideal side's argument is the real side's verbatim |

Nothing else about the hash enters, which is the point: the corollary is the
slides' claim, with the emulation the only cryptographic premise left. It is
assumed at the LEDGER (`Real ≤UC^ω Ideal a V`) and not at the hash, because
getting it from a hash-level `hash n ≤UC oracle n` is `UC-compose` at the family
setup — continuation item 1 below.

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

1. **Family ingestion (requirement 2's remainder).** Build
   `layer-1 ≈adv family ⇒ UC.Model.Family._≈ℰ[ ε ]_`, then `absorb-negl` /
   `_≈ℰⁿ_`. The blocker is that `UC.Machine.Bridge.ContextDominated` quantifies
   its ancilla and context over `Iface`-images while `UC.Family._≈ℰ[_]_`
   quantifies over SEAL objects, and under the seal `ifaceᵒ` is not known to be
   onto (`UC.Seam.Grounding`'s header records the same asymmetry). So the work
   is `ContextDominated` restated and reproved at seal objects — a
   machine-layer sub-project, not an application-layer one. With it,
   `ucSetup^ω`'s inherited metatheory (`≤UC-trans`, `UC-compose`,
   `dummy-complete`) becomes usable on concrete families, which is what the
   review's §4 second and third bullets ask for.

2. **The prefix-tolerant event class** (the obstruction above), after which
   `uc-audit-carry` reaches a probability at the unit grade. Work plan:
   `docs/prefix-tolerant-audit-plan.md` — scope-narrowed per the follow-up
   review §3.1: accounting for an *interactive* simulator additionally needs
   the review's §3 (the current budgeted simulator is a scalar).

3. **A named hash construction.** The real family's shape is no longer generic:
   `ChimericLedger.Real` fixes it to `ledger vr s₀ ∘ᵖ hash` and discharges all
   three of the real-side hypotheses there for any dead-free `hash`, so what is
   left assumed at a concrete ledger is the emulation alone. Supplying THAT for
   a named construction is the remaining half, and it needs a construction whose
   interface matches: `Examples.MerkleDamgard`'s ideal oracle hashes
   FIXED-length messages (`RandomOracle 1 (Vec Bool (k * n)) n`) where the
   ledger hashes bitstrings, so the instance wants a padding adapter and then a
   `≤UC^ω` proof built off `MD.indistinguishable`. That is a
   cryptographic-construction obligation, which the review explicitly places
   outside this scope.

4. **`≈ℰⁿ` as an `Observation`** — the redesign `UC.Family`'s closing comment
   prices. Not attempted; not needed by anything above, since the negligible
   tier consumers use lives at layer 1 (`UC.Saturated`). Expanded proposal:
   `docs/graded-observation-redesign.md`.

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
| `Examples.ChimericLedger.Real` | 93 | 11 s |

Additive edits to existing modules: `POV.asks≤-audited` (the instrumentation's
allowance cost, beside `audited`); `Carry.Emulᵁᶜ`/`emulᵁᶜ`/`pov-carryᵁᶜ` (the
UC-vocabulary premise, the first importer of `unitGrade`); `UC.Seam.Audit`
re-exports `≤UC[]⇒≤UC`; `UC` re-exports the two `UC.Asymptotic` modules.

The hash-generalization `Real` rests on is likewise additive in content and free
in cost: `POV.Sysᴴ` beside `Sys`, and the `hash` parameter threaded through
`Trajectory` (8 s warm) and `Total` (9 s), whose proofs are unchanged.

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
