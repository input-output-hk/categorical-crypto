# The end-to-end asymptotic UC-to-POV theorem

The completion goal of [the implementation review](protocol-implementation-review.md),
as the tree stands at `587999b5`. Everything below is a checked term unless it
is marked otherwise; the escape-hatch grep over `src/` stands at its baseline of
16 hits, every one the words "postulate-free" in an inherited comment
(`docs/retirement.md` §10).

The chain:

```
hash ≤UC^ωⁿ oracle^ω  ──hash-liftⁿ, over ledger-factor──▶  Realᴴ hash ≤UC^ωⁿ Realᴴ oracle^ω
                      ──ledger-uc-to-pov-family────────▶  SaturatedHitᴺ, i.e. a POV bound
```

and the composite is `ledger-pov-from-hashⁿ`. The bound being carried across is
`Birthday.target`, the proved birthday theorem, read through the designated
monitor by `Trajectory.monitor-bounded` and packaged per level as
`Schedule.ideal-bounded`. Everything between is UC metatheory; the only
cryptographic premise left at the end of the chain is the hash's own emulation.

## 1. The premise shapes

Four relations compare a real family with an ideal one. Which one a theorem
takes decides what it may keep of the error and what it must spend.

| relation | where | what it says |
|---|---|---|
| `_≤UC^ω_` | `UC.Asymptotic:90` | POINTWISE and qualitative: at each level, the inherited `_≤UC_` between the trivially graded closed images `closedᵒ (morphism (R n))` and `closedᵒ (morphism (I n))` — a simulator per dummy adversary, never an `Agreeˢ` |
| `_≤UC^ω[_]_` | `UC.Asymptotic.Audit:63` | the same per level with the simulator carrying a query bound `cs n` (`UC.Seam.Audit._≤UC[_]_`), so a carry can charge for its queries |
| `_≤UC^ωⁿ_` | `UC.Asymptotic.Family:110` | `Σ[ ε ] NegligibleBound ε × R ≈ᶠ[ ε ] I`: allowance-uniform QUANTITATIVE evidence at the protocol images |
| `_≤UC^ωᵉ_` | `UC.Asymptotic.Contextual:271` | the witness form at arbitrary graded families: `Σ[ s ∈ Certified Y X ] Σ[ ε ] NegligibleBound ε × f ≈ctx[ ε ] subᶠ s g` |

`_≈ᶠ[_]_` (`Family:102`) is a definitional alias — `R ≈ᶠ[ ε ] I` *is*
`imgᶠ B R ≈ctxᴬ[ ε ] imgᶠ B I` — so the family premise has no relation of its
own left. `_≈ctx[_]_` (`Contextual:79`) is the canonical one: at each level, no
budgeted ancilla context separates the two graded homs by more than `ε` read at
the allowance the context's two legs CARRY (`ctxBudget c c′`). `_≈ctxᴬ[_]_` is
the same experiment at the operational bracket `W ⊗ (X ⊗ B)`; the two are
bridged by `≈ctx⇒≈ctxᴬ`/`≈ctxᴬ⇒≈ctx`, which transport the query certificate as
well as the observation, so the two carry the SAME `ε` rather than a rescaled
one.

What `_≈ctx[_]_` does not read is the compared homs' own query bounds — only the
context's. So a premise stated with it needs no certificate for the systems it
compares; only the corollaries that enter the family category
(`≤UC^ωⁿ⇒≈ℰⁿ` and its siblings) ask for one, as `Imageᶠ`.

### How they relate

* `uc-≤UC^ωⁿ` (`Family:318`): `_≤UC^ω_` plus the real side's totality implies
  `_≤UC^ωⁿ_`, at the schedule `2⁻ⁿ`. So the pointwise theorems below are
  literally the family theorems at a stronger premise.
* `≤UC^ωⁿ⇒≤UC^ωᵉ` (`:189`) is unconditional, at `idᶜ`;
  `≤UC^ωᵉ⇒≤UC^ωⁿ` (`:198`) runs back only under the explicit premise that the
  witness's simulator acts trivially on the ideal side
  (`(n : ℕ) → subᶠ s (imgᶠ B I) n ≈ imgᶠ B I n`, in `𝒞`'s own equality). That is
  available for a trivial simulator and only for it — see §5.
* A budgeted emulation IS an emulation (`≤UC[]⇒≤UC` then
  `UC.Model.Bridge.≤UCᶜ⇒≤UC`), so `_≤UC^ω_`'s theorems apply wherever
  `_≤UC^ω[ cs ]_`'s do and give the SHARPER number: at the trivial grade the
  simulator costs the ideal side nothing. What the budgeted statement adds is
  the accounting, not a better bound.
* The pointwise/family pair is therefore ORDERED and the pointwise/budgeted pair
  is not.

Two neighbours of these relations sit OFF the chain, and are named so that they
are not mistaken for parts of it: `UC.Model.Family.Ingest.ingest` takes a
per-level advantage bound into `UC.Model.Family._≈ℰ[_]_`, consuming
`UC.Model.Dominated.dominatedᵒ` (`ContextDominated` reproved at seal objects, on
the proved `ifaceᵒ-onto`), and `UC.Model.Family.Uniform.uc-compose-agree`
composes two family agreements through `UC.Core.Bridge`. Neither has an in-repo
caller; `docs/retirement.md` §7 records why they stand.

Two acceptance criteria pin the family premise's strength, both in `Family`:
`admits-inv-pow-2` (a one-shot `2⁻ⁿ` difference is admitted — exactly the
schedule the pointwise inclusion produces) and `rejects-inv-suc` (a one-shot
`1/(n+1)` difference is rejected, against `UC.Approximate.Separating`'s gap
instrument). `pointwise-exact`/`pointwise-rejects` say what the pointwise
premise asks instead: closeness at every positive error at a FIXED level.

## 2. The theorems

Seven in `Examples.ChimericLedger.EndToEnd`, parameterized by a per-level
serialization `ser : (n : ℕ) → Ledger.Tx n → List Bool`:

| theorem | premise | conclusion |
|---|---|---|
| `ledger-uc-to-pov` (`:118`) | `SerInj`, `TotalRun` on the real side, `R ≤UC^ω Ideal a V`, `TruthfulAudit` | `SaturatedHitᴺ R badR (λ n q → εᴸ n (q + q))` |
| `ledger-pov-negligible` (`:144`) | the same, plus `Poly p` | the same bound as one negligible number |
| `ledger-uc-to-pov-family` (`:182`) | `SerInj`, `R ≤UC^ωⁿ Ideal a V`, `TruthfulAudit` | the SAME bound, with no `TotalRun` |
| `ledger-pov-family-negligible` (`:204`) | the same, plus `Poly p` | its one-number reading |
| `ledger-audit-carryᵈ` (`:224`) | `SerInj`, `R ≤UC^ω[ cs ] Ideal a V` | at any test, closure, strategy and allowance: `Pr≤ k (obs …) ≤ εᴸ n q + ν n` |
| `ledger-uc-to-pov-simCost` (`:244`) | `SerInj`, `TotalRun`, `R ≤UC^ω[ cs ] Ideal a V`, `TruthfulAudit` | `SaturatedHitᴺ R badR (λ n q → εᴸ n (simCost (q + q) (cs n)) + ν n)` |
| `ledger-pov-simCost-negligible` (`:276`) | the same, plus `Poly cs` and `Poly p` | its one-number reading; the simulator's budget must be polynomial for the number to be negligible |

The public statement reads:

```agda
ledger-uc-to-pov :
    (a V : ℕ) → SerInj → (R : Systems LedgerIf^ω) (badR : Bad R)
  → ((n : ℕ) → TotalRun (LedgerIf^ω n) (morphism (R n)))
  → R ≤UC^ω Ideal a V
  → TruthfulAudit a V R badR
  → SaturatedHitᴺ R badR (λ n q → εᴸ n (q + q))
```

Unfolded: for every polynomial allowance `p` there is a negligible `νₚ` such
that no strategy of query budget `p n` moves the real system's total value away
from genesis with probability above `((2·p n)² + 2·p n)·2⁻ⁿ + νₚ n`. The
audit instrumentation's cost is why `p` is evaluated at `p + p`
(`POV.asks≤-audited`), and it is charged in the conclusion rather than assumed
away.

Four corollaries at concrete families:

| corollary | where | premise |
|---|---|---|
| `ledger-pov` | `ChimericLedger.Real:89` | `SerInj`, `Real ≤UC^ω Ideal a V` — the real side's three hypotheses discharged once (below) |
| `ledger-pov-from-hash` | `ChimericLedger.Factor:108` | `SerInj`, `hash ≤UC^ω oracle^ω` — the premise at the HASH, through `hash-lift` |
| `ledger-pov-from-hashⁿ` | `ChimericLedger.FactorEps:159` | `SerInj`, `hash ≤UC^ωⁿ oracle^ω` — the same, with the hash's error kept across the factoring |
| `ledger-pov-from-hash′` | `FactorEps:177` | `ledger-pov-from-hash`'s own statement proved the ε-retaining way; `migration-pin` forces the two types to unify |

## 3. Hypotheses, and why each is allowed

| hypothesis | status |
|---|---|
| `SerInj` | the birthday theorem's own injective-serialization assumption, per level (`Tx` depends on the hash width, so one `ser` cannot be typed) |
| the emulation | the cryptographic premise, in whichever of §1's shapes the theorem takes. Never `Agreeˢ` |
| `TotalRun … (morphism (R n))` | the real side's admissibility. Not decoration — with the real side divergent, a simulator that never starts emulates every ideal. Discharged for any dead-free protocol by `Protocol.Live` + `totalRun-morphism`; the ideal side's copy is proved (`ChimericLedger.Total`). Absent from the family theorems, which have nothing to collapse |
| `TruthfulAudit a V R badR` | the real implementation's audit-to-trajectory connection. UC identifies no internal state trajectory, so this is irreducibly about the implementation; for a ledger image it is `Trajectory.monitor-complete` (`Schedule.ideal-truthful`, `Real.real-truthful`) |

At `ChimericLedger.Real` — `Real n = ledger vr (genesis n) ∘ᵖ hash n` for a hash
implementation with `NoDeadStep (hash n)` — the three hypotheses about `R` are
discharged once and for all, generically in the hash:

| hypothesis | discharged by |
|---|---|
| `Bad Real` | `badReal n = badTotal (genesis n)`: the POV event itself, which reads the ledger's state and not the hash's |
| `TotalRun … (morphism (Real n))` | `Total.totalRun-Sys`: the ledger writes no `dead` and `_∘ᵖ_` creates none, so the real side owes only `NoDeadStep (hash n)` |
| `TruthfulAudit a V Real badReal` | `Trajectory.monitor-complete`: an audit query is answered out of the LEDGER's state whatever it hashes with, so the ideal side's argument is the real side's verbatim |

Nothing else about the hash enters, which is the point.

## 4. The two routes

Both start from the ideal side's `Bounded (Ideal n) (monitorᴸ n) (εᴸ n)` —
layer 1's own bound, `Schedule.ideal-bounded`, which is
`ChimericLedger.Audit.pov-target` levelwise and has no UC vocabulary in it.

### The probability route

It ends at `SaturatedHitᴺ`, i.e. at `PrHit` of the real system. Three entrances,
one tail.

* **The trivial-grade collapse.** `uc-agree` spends
  `UC.Seam.Grounded.unitGrade`: at a grade both ends are blind to, an emulation
  IS the direct agreement — the simulator collapses by `sub s ∘ g ≈ᵁ g`
  (`subBlind`, off the real process's own totality through `emSimTotal`) and the
  inflating wire by the ancilla quantifier. `uc-≈negl` reads the agreement as
  `UC.Saturated._≈negl_` at a positive negligible slack (`agreeToAdv`).
* **The family premise.** `≤UC^ωⁿ⇒≈negl` reaches the same `_≈negl_` with no
  exact agreement anywhere: `≈ᶠ-runs` evaluates the premise at
  `UC.Seam.Audit.Context`'s strategy-embedded context — its budget certificate
  `audit-qb`, its observation identified with layer 1's run by `audit-run` — and
  `adv-from-runs` (`UC.Seam.Carry`) turns the per-run bound into the graded
  relation at a FIXED slack.
* **The budgeted premise.** `uc-audit-boundedᵖ` produces layer 1's `Bounded` on
  the real side directly, through `UC.Seam.Audit.Prefix.uc-audit-bounded`. That
  route is `bounded-carry` = `Mass.dominate` + `sim-prefixed` +
  `UC.Seam.Audit.Bounded.supply` + `UC.Seam.Audit.Context.extract-obs`: the
  simulator's initialization is tolerated as a PREFIX, never seen to add mass
  (`sim-prefixed`, a one-sided `≼ₚ[ 0ℚ ]` off `prefix-absorbᵒ`), and its queries
  are charged at `simCost`. `bounded-carry` is the statement of which
  `uc-audit-bounded` is the `simCost` instance: the allowance inflation is a
  parameter, any `p` with `q ≤ p q`.

The tail is `saturatedHitᴺ-from-monitor` in all three: it turns a monitor bound
into a trajectory bound through `TruthfulAudit`, with the instrumentation and
its allowance cost as explicit parameters. What differs is how the real-side
`SaturatedBoundedᴺ` it consumes is reached. The first two entrances read the
IDEAL bound as its own saturated form at zero slack (`boundedᴺ`) and transport
it across the graded relation (`uc-preservesᴺ`, i.e. `≈negl-respects` and so
`saturated-respects[ Negligible ]` — allowance first, slack second, the repaired
quantifier order); the third already holds a real-side `Bounded` and reads it
with `boundedᴺ` directly.

No event class occurs on any of the three. On the budgeted entrance the
numerical half is `extract-obs`/`extract-bounded` and the rational arithmetic is
`UC.Seam.Audit.Bounded.supply`; [`docs/retirement.md`](retirement.md) records
the membership layer the plan's §5 gates retired against them, name by name.

### The graded route

`uc-audit-carryᵈ` states the crossing at the existing test, closure, monitor
transformation and budget witness, and stops at a `Pr≤` bound on the context's
own observation. Its generic half is `UC.Audit.carry-obs` — the emulation
evaluated at one context, the simulator slid onto the test by
`UC.Environment.tv₁-∘`, the `Mass` domination at the slack — hoisted out of
`audit-carry`, whose statement is unchanged. At the ledger this is
`ledger-audit-carryᵈ`, off `Schedule.ideal-bounded`.

Neither the simulator's query certificate `sim-qb` nor `ctxBudget` is consumed:
both exist to move an allowance across a quantifier over budgeted TESTS, and the
allowance moves here in the strategy `d`, which is `Bounded`'s own quantifier.

### Why they do not compose

The graded carry ends at a bound whose hypothesis is that the
simulator-fronted context observes an ideal monitored run EXACTLY (`≈ₚ`).
Turning that back into a real-side `Bounded` needs the extraction context — with
the simulator in front of it, plugged into the IDEAL machine — to satisfy that
hypothesis, and it does not: the simulator's own initialization makes the
observation ε-close and no more, which is all `UC.Seam.Grounded.subBlind` and an
almost-sure totality can give. The typed residual is
`docs/consumer-migration.md` §2's `auditIsBoundedʷ`, and it is FALSE as stated,
not merely unproved.

So the probability endpoint goes through the prefix rather than through the
graded carry's conclusion, and one consequence is worth not glossing: at the
trivial grade the simulator costs the ideal side nothing, so
`ledger-uc-to-pov`'s bound is the birthday bound at the audit-adjusted
allowance, not a `simCost`-adjusted one. The `simCost`-adjusted statement is
`ledger-uc-to-pov-simCost`'s. None of this accounts for an *interactive*
simulator: the budgeted simulator at these types is a scalar (review §3).

## 5. The premise at the hash

`Examples.ChimericLedger.Factor` factors the closed system on the nose —
`ledger-factor`, via `Seal.procᵒ-∘` and the retraction-conjugated `sub`
congruence `Abstract2.Factor.≤UC-sub` — so a premise about the hash lifts to the
system. Two lifts, both in `FactorEps`, inside
`module _ (vr : Variant) (s : (n : ℕ) → Ledger.LState n)`:

```agda
hash-liftⁿ : (hash : Systems HashIf^ω) → hash ≤UC^ωⁿ oracle^ω
           → Realᴴ hash vr s ≤UC^ωⁿ Realᴴ oracle^ω vr s

hash-liftᵉ : (hash : Systems HashIf^ω)
           → imgᶠ HashIf^ω hash ≤UC^ωᵉ imgᶠ HashIf^ω oracle^ω
           → imgᶠ LedgerIf^ω (Realᴴ hash vr s) ≤UC^ωᵉ imgᶠ LedgerIf^ω (Realᴴ oracle^ω vr s)
```

`hash-liftᵉ` runs through `UC.Asymptotic.Compose.UC-composeᵉ` at the shared
upper stage; `hash-liftⁿ` needs no simulator at all — `≈ctx-ext` absorbs the
ledger into the test at its own budget and `≈ctx-sub` the unit regrading the
Kleisli composition introduces — and having none is what lets the chain END,
since a general witness cannot be forgotten back into `_≤UC^ωⁿ_` (§1). The lift's
ε is the premise's own schedule read at `(q * 1) * 1`, one activation for the
ledger and one for the unit regrading, with both substitutions EXACT
(`ctxBudget-simCost`, `ctxBudget-absorb`) and negligibility proved after them.

Every certificate `UC-composeᵉ` demands is proved rather than carried:
`UC.QueryBound.qb-closed` for the hash (a closed process is 0-bounded),
`ChimericLedger.QueryBound.qb-ledger` for the ledger (an instance of
`UC.QueryBound.qb-oneCall`), and its `Allowance-mono` premise is discharged
because the two sides share their upper stage and are compared at the zero
schedule. `docs/ledger-lift-eps.md` has the substitutions and the residual.

`ledger-pov-from-hashⁿ` is `ledger-pov-family-negligible` behind `hash-liftⁿ`:
the same bound, the same `TruthfulAudit`, and neither `TotalRun` nor
`NoDeadStep`. The forgetting happens at the END and nowhere earlier — the error
crosses the factoring intact and only the family theorem's own carry folds it
into the saturated slack.

## 6. Hypothesis and theorem

Theorem, at `587999b5`: every statement named above, the layer it runs on
(`UC.Approximate`, `UC.Audit`, `UC.Saturated`, `UC.Asymptotic.*`, `UC.Seam.*`),
the ideal birthday bound under its serialization hypothesis, and the query
certificates the lifts consume.

Hypothesis, and nowhere hidden:

* the four premises of §3 — of which only the emulation is cryptographic;
* the *nontrivial-grade* line's UC-level statement (§7): `raw-emulation` for the
  RO commitment is not proved, and the gap is a quantifier gap rather than a
  proof gap (`docs/dp-transport.md` §5);
* the hiding half's `ε′`: `hiding-bound-defer` is a proved theorem whose missing
  deferred-sampling identification is one typed hypothesis, never a postulate
  (`docs/fcom-hiding.md` §"Not delivered" 1);
* `≤UC^ωᵉ⇒≤UC^ωⁿ-blind` (`docs/ledger-lift-eps.md` §5): forgetting a NON-trivial
  trivial-grade simulator after the composition, blocked on an `ASTotal` the
  quantitative relation cannot produce. Nothing at the ledger needs it.

## 7. Beyond the ledger

The ledger runs entirely at the trivial grade. The nontrivial-grade line is a
separate arc and this document only locates it.

* **`Examples.HashForward`** — the EXACT application at a nontrivial grade: an
  ideal functionality that leaks a message, a real protocol that leaks its
  digest, and a simulator whose oracle query is counted exactly
  (`UC.QueryBound.Exact`, `sim-hash-count`, `sim-round`).
  [`docs/hash-forward.md`](hash-forward.md).
* **The graded extraction bridge** — `plug-runᵍ`, `adequacyᵍ`, `extractᵍ` and
  with them `hf-pr-bound`, the `Pr` bound at a grade where the simulator is run
  in the ideal experiment rather than assumed silent.
  [`docs/graded-bridge.md`](graded-bridge.md).
* **`Examples.ROCommitment`**, extraction half — the first emulation in the
  repository carrying an ε that is not zero: `extraction-bound` at
  `(m²+m)·2⁻ᵏ + m·2⁻ᵏ`, `Certified 2 simulator`, `εᶜ-negligible`.
  [`docs/fcom-extraction.md`](fcom-extraction.md).
* **`Examples.ROCommitment.Hiding`** — the same commitment against a corrupted
  receiver, the simulator equivocating by programming one point:
  `hiding-bound` at `m·2⁻ᵏ`, `Certified 1`, and the general deferred-sampling
  engine `GamePlaying.Defer.runWith-avg`.
  [`docs/fcom-hiding.md`](fcom-hiding.md).
* **The `Dₚ`/`Dist-ℚ` transport** — `ProbabilisticLogic.Dp.Settle` and
  `Protocol.Machine.Raw` turn a raw machine's closed `Dₚ` run into a `Dist-ℚ`
  kernel run under one explicit settling hypothesis, inhabited at a resource
  that really samples (`ROCommitment.Transport.resource-settles`).
  [`docs/dp-transport.md`](dp-transport.md).
* **The consolidation plan** — the seven steps this arc executed, their
  acceptance checks and the retirement gates:
  [`docs/uc-presheaf-preservation-plan.md`](uc-presheaf-preservation-plan.md)
  §6, with the generic presheaf preservation in
  [`docs/presheaf-action.md`](presheaf-action.md).

## 8. Module costs

Warm single-`Checking`-line runs under
`pagda --useUntracked false check … -- +RTS -M8G -H1G -RTS`, quoted from the
branch that measured them; LOC is that branch's too. Rows with no measurement
since the arc began carry their LOC at `587999b5` and no warm figure.

| module | LOC | warm | measured in |
|---|---|---|---|
| `UC.Asymptotic` | 146 | 9 s | `docs/retirement.md` §9 |
| `UC.Asymptotic.Audit` | 111 | 9 s | `docs/retirement.md` §9 |
| `UC.Asymptotic.Family` | 342 | 23.7 s | `docs/ledger-lift-eps.md` §7 |
| `UC.Asymptotic.Contextual` | 313 | 10.7 s | `docs/ledger-lift-eps.md` §7 |
| `UC.Asymptotic.Compose` | 277 | 11.5 s | `docs/ledger-lift-eps.md` §7 |
| `UC.Audit` | 195 | 5 s | `docs/retirement.md` §9 |
| `UC.Environment` | 169 | 2.2 s | `docs/consumer-migration.md` §6 |
| `UC.Seam.Audit` | 26 | 9 s | `docs/retirement.md` §9 |
| `UC.Seam.Audit.Context` | 226 | 10 s | `docs/retirement.md` §9 |
| `UC.Seam.Audit.Bounded` | 49 | 9 s | `docs/retirement.md` §9 |
| `UC.Seam.Audit.Prefix` | 136 | 10 s | `docs/retirement.md` §9 |
| `UC.Seam.Slide` | 44 | 10 s | `docs/direct-extraction.md` §"Module costs" |
| `UC.Seam.Grounded` | 280 | 10 s | `docs/direct-extraction.md` §"Module costs" |
| `UC.QueryBound` | 647 | 15.8 s | `docs/consumer-migration.md` §6 |
| `UC.Budget` | 127 | 2.6 s | `docs/quantitative-family.md` §8 (`-M20G -H2G`) |
| `UC.Approximate` | 280 | 4.4 s | `docs/quantitative-family.md` §8 (`-M20G -H2G`) |
| `UC.Family` | 316 | 4.6 s | `docs/quantitative-family.md` §8 (`-M20G -H2G`) |
| `UC.Family.Negligible` | 85 | 5 s | `docs/retirement.md` §9 |
| `UC.Model.Family` | 31 | 8.7 s | `docs/quantitative-family.md` §8 (`-M20G -H2G`) |
| `UC.Saturated` | 211 | — | not re-measured |
| `UC.Approximate.Decay` | 85 | — | not re-measured |
| `UC.Seam.Carry` | 126 | — | not re-measured |
| `Protocol.Live` | 139 | — | not re-measured |
| `CategoricalCrypto.UC` | 229 | 10 s | `docs/retirement.md` §9 |
| `Examples.ChimericLedger.Audit` | 39 | 6 s | `docs/retirement.md` §9 |
| `Examples.ChimericLedger.EndToEnd` | 294 | 11 s | `docs/retirement.md` §9 |
| `Examples.ChimericLedger.Factor` | 116 | 12.7 s | `docs/ledger-lift-eps.md` §7 |
| `Examples.ChimericLedger.FactorEps` | 195 | 12.2 s | `docs/ledger-lift-eps.md` §7 |
| `Examples.ChimericLedger.QueryBound` | 42 | 8.8 s | `docs/consumer-migration.md` §6 |
| `Examples.ChimericLedger.Schedule` | 127 | — | not re-measured |
| `Examples.ChimericLedger.Total` | 54 | — | not re-measured |
| `Examples.ChimericLedger.Real` | 93 | — | not re-measured |

Every measured row is an order of magnitude inside its `60 s + LOC/4` budget,
and a large part of each figure is interface deserialization rather than
elaboration — which is why deleting 128 lines from `UC.Seam.Audit` left its
9 s untouched (`docs/retirement.md` §9).

One perf finding is worth keeping even though it was measured on the
`end-to-end` branch and not since: the two carries in ONE module cost 127 s warm
and in two cost 10 + 10 s. Neither half is expensive; the collapse's seal-level
terms and the carry's own instantiation are expensive together.

## 9. Not delivered

1. **A named hash construction.** The real family's shape is fixed to
   `ledger vr s₀ ∘ᵖ hash` and all three real-side hypotheses are discharged
   there, so what is left assumed at a concrete ledger is the emulation alone.
   Supplying it needs a construction whose interface matches:
   `Examples.MerkleDamgard`'s ideal oracle hashes FIXED-length messages where
   the ledger hashes bitstrings, so the instance wants a padding adapter and
   then a `≤UC^ω`/`≤UC^ωⁿ` proof off `MD.indistinguishable`. A
   cryptographic-construction obligation, which the review places outside this
   scope.
2. **A nontrivially graded hash port.** `hashPortᵒ` is an OBJECT boundary and
   both stages are pure, so every simulator there is a `𝟘ᴳ ⇒ 𝟘ᴳ` scalar and is
   provably blind. `hash-liftᵉ` is stated at an arbitrary certified simulator
   family and would carry a real one unchanged; the ledger cannot supply one
   (`docs/ledger-factoring.md`, closing section).
3. **`≈ℰⁿ` as an `Observation`.** Not attempted, and nothing above needs it: the
   negligible tier consumers use lives at layer 1 (`UC.Saturated`), the family
   premise keeps its witness as a Σ, and the ε-retaining composition law that
   paragraph once priced as a core redesign is `UC.Asymptotic.Compose.UC-composeᵉ`
   — enrichment lemmas over the existing action, not a redesign. Expanded
   proposal: `docs/graded-observation-redesign.md`.
4. **A monotone envelope for `ε`.** `≈ctx-pre` and hence `UC-composeᵉ` take
   `Allowance-mono` as a premise; the constructed envelope wants a finite
   `ℚ`-max over `0 … q` and its argmax and is not built
   (`docs/quantitative-family.md` §10).
