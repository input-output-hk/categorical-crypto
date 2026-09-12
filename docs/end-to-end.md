# The end-to-end asymptotic UC-to-POV theorem

Status of the completion goal of
[the implementation review](protocol-implementation-review.md), started on branch
`end-to-end` off `protocol-rewrite` and continued on `family-premise` (the
follow-up review's §1). Everything below is a checked term unless marked
otherwise; hatches stay at zero in `src/`.

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

### …and off the family premise

`R ≤UC^ω Ideal a V` is the POINTWISE, unit-grade specialization of
asymptotic-family emulation (review §1 step 1), which `UC.Asymptotic`'s own
header and `UC.Asymptotic.Family` now say in as many words. The family premise
is `UC.Asymptotic.Family._≤UC^ωⁿ_` and the second theorem consumes it:

```agda
ledger-uc-to-pov-family :
    (a V : ℕ) → SerInj → (R : Systems LedgerIf^ω) (badR : Bad R)
  → R ≤UC^ωⁿ Ideal a V
  → TruthfulAudit a V R badR
  → SaturatedHitᴺ R badR (λ n q → εᴸ n (q + q))
```

with `ledger-pov-family-negligible` its one-number reading. Three readings of
the statement:

* the **bound is unchanged** — `≈negl-respects` folds the premise's `ε` into the
  saturated slack rather than into `ε`, and the slack is quantified after the
  allowance, so the birthday term stays the audit-adjusted `εᴸ n (q + q)`;
* **`TotalRun` is gone** — the pointwise theorem spends it to collapse a
  per-level emulation into an agreement (a divergent real side is emulated by a
  simulator that never starts), and the family premise is already quantitative;
* **no exact agreement is passed through** — `uc-agree`/`Agreeˢ` appear nowhere
  in the proof, which is review §1's acceptance condition. The `ε` travels
  contextual → direct run (`Family.≈ᶠ-runs`, over `UC.Seam.Audit.Context`) →
  `UC.Saturated._≈negl_` → `SaturatedBoundedᴺ`.

The two are ORDERED, unlike the pointwise/budgeted pair below:
`Family.uc-≤UC^ωⁿ` proves `_≤UC^ω_` plus the real side's totality implies
`_≤UC^ωⁿ_` (at the schedule `2⁻ⁿ`), so `ledger-uc-to-pov` is literally
`ledger-uc-to-pov-family` at a stronger premise.

### Hypotheses, and why each is allowed

| hypothesis | status |
|---|---|
| `SerInj` | the birthday theorem's own injective-serialization assumption, per level (`Tx` depends on the hash width, so one `ser` cannot be typed) |
| `R ≤UC^ω Ideal a V` | the UC-emulation premise: the INHERITED `_≤UC_` at each level, a simulator per dummy adversary. Never `Agreeˢ`. Pointwise/unit-grade, hence STRONGER than asymptotic-family emulation — see the family theorem below |
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
slides' claim, with the emulation the only cryptographic premise left. And the
hash-level premise is delivered too: `Examples.ChimericLedger.Factor` factors
the closed system on the nose (`ledger-factor`, via the new `Seal.procᵒ-∘` and
the retraction-conjugated `sub` congruence `Abstract2.Factor.≤UC-sub`), lifts
`hash ≤UC^ω oracle^ω` to the system level (`hash-lift` — the ledger enters
only as `≤UC-refl`), and `ledger-pov-from-hash` is this corollary at that
premise: the slides' `H ≤UC RO ⟹ Ledger∘H ≤UC Ledger∘RO` step, literally.
See `docs/ledger-factoring.md`.

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

2. **Family UC setup + consuming adequacy — DONE.**
   `UC.Model.Family.ucSetup^ω` is a closed term: `UC.Family.Monoidal`
   instantiated at the sealed bundle, with `approximateᵒ` supplied (the
   approximation `observationᵒ`'s equivalence was induced from, so `induces` is
   the identity). The emulation premise is CONSUMED, not assumed: `uc-agree`
   spends `UC.Seam.Grounded.unitGrade`, which in turn spends `adequacy`,
   `prAgree` and `stratIsEnv` — the proved lift, never an assumed one.
   **The ingestion is now delivered** (`UC.Model.Family.Ingest`): a per-level
   advantage bound `_≈advᴹ[_]_` plus `QB` witnesses ingests to
   `_≈ℰ[ ε + δ ]_`, then `_≈ℰ_`/`_≈ℰⁿ_`/`_≤UC_` (core and inherited), consuming
   `UC.Model.Dominated.dominatedᵒ` — `ContextDominated` reproved at seal
   objects, on the proved `ifaceᵒ-onto` (continuation item 1). **And the family
   premise is now named and consumed**: `UC.Asymptotic.Family._≤UC^ωⁿ_`, with
   review §1's two acceptance criteria as theorems, the ε-adding composition
   law, the identification with the `_≈ℰⁿ_` tier, the inclusion of the
   pointwise premise, and `ledger-uc-to-pov-family` above. Review §1's
   labelling step is `UC.Asymptotic`'s header and the comment on `_≤UC^ω_`.

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

## The family premise

`UC.Asymptotic.Family`, on review §1's OPTION A: the public contract keeps
allowance-uniform saturation (`SaturatedHitᴺ`), so the premise has to carry
allowance-uniform quantitative evidence rather than per-context negligible
agreement.

```agda
R ≤UC^ωⁿ I = Σ[ ε ∈ (ℕ → ℕ → ℚ) ] NegligibleBound ε × R ≈ᶠ[ ε ] I
```

where `R ≈ᶠ[ ε ] I` says: at each level, no budgeted ancilla context separates
the two `ι`-inflated sealed images by more than `ε` read at the budget the
context's two legs CARRY. That is `UC.Model.Family._≈ℰ[_]_` at those images
with the Σ-packaging of a `Fam`-hom peeled off — the relation reads the
CONTEXT's carried budgets and never the compared homs' own, so the premise
needs no query bound for the systems it compares; only the corollaries that
enter the family category ask for one. Peeling it off also makes the premise
the *explicitly stronger uniform quantitative refinement* review §1 permits (a
per-level context need not come from a polynomially budgeted FAMILY of
contexts), and that is the direction the ledger consumer needs.

What is proved about it:

| statement | content |
|---|---|
| `admits-inv-pow-2` | §1 criterion 1: a one-shot `2⁻ⁿ` difference is admitted — and it is exactly the schedule the pointwise inclusion produces |
| `rejects-inv-suc` | §1 criterion 2: a one-shot `1/(n+1)` difference is rejected, against `UC.Approximate.Separating`'s gap instrument (`¬negligible-inv-suc`) and `Decay.Negligible-≤` |
| `≤UC^ωⁿ-trans` | the composition law: two family emulations compose and the εs ADD, the sum staying negligible by `Negligible-+` |
| `≤UC^ωⁿ⇒≈ℰⁿ` / `⇒≈ℰᶠ` / `⇒≤UCᶠ` / `⇒≤UCᵁ` | the premise IS the `_≈ℰⁿ_` tier of the family model, and its qualitative shadows land in the core and the INHERITED order, which is where `UC-compose` is |
| `uc-≈ᶠ[_]`, `uc-≤UC^ωⁿ` | pointwise ⇒ family, at any positive schedule and at `2⁻ⁿ` |
| `pointwise-exact`, `pointwise-rejects` | what the pointwise premise says instead: closeness at every positive error at a FIXED level, hence rejection of a pair separated by `2⁻ⁿ` |
| `≈ᶠ-runs`, `≤UC^ωⁿ⇒≈negl` | the premise read at the embedded-strategy contexts, then as layer 1's negligibly graded relation |

Both halves of the seam are reused, not reinvented: `UC.Model.Family.Ingest`
ingests a per-level advantage bound INTO the family relation, and
`UC.Seam.Audit.Context` reads one back OUT — the strategy context with its
budget certificate (`audit-qb`) and the identification of its observation with
layer 1's run (`audit-run`). The only new arithmetic is
`UC.Seam.Carry.adv-at`/`adv-from-runs`, which is `UC.Seam.Carry.agreeToAdv`'s
proof at a FIXED slack instead of at every positive one (they landed in a
`UC.Seam.Carry.Graded` of their own and were since merged back in, `agree-to-adv`
becoming `adv-from-runs` at a constant slack).

**What is not delivered: an ε-retaining `UC-compose`.** `≤UC^ωⁿ-trans` composes
two family emulations with the εs adding, but composing a family emulation with
a second protocol is `UC-compose`, the INHERITED metatheorem
(`Abstract2.UC-compose`, transported by `UC.Core.Bridge` and applied at the
family by `UC.Model.Family.Uniform.uc-compose-agree`), and it is stated in the
QUALITATIVE order — so that route goes through `≤UC^ωⁿ⇒≤UCᵁ` and SPENDS the
error witness. Retaining it needs a graded `_≤UC[ ε ]_` with graded `≈ℰ`
congruences and a graded `sub`/`T₁` interchange, i.e. `Abstract2.UC-compose`
re-proved over an ε-indexed relation: the observation-interface redesign
`UC.Family`'s closing comment and `docs/graded-observation-redesign.md` price.
The ledger consumer does not need it — the ideal bound is supplied at the
ledger, not composed from a hash-level one — so it is recorded rather than
attempted.

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

**Closed at the unit grade** by the first of the two remedies that stood here:
`UC.Seam.Audit.TrivialGrade.watchedᵖ` permits an almost-surely-total silent
prefix, the syntactic prefix is stable under `Absorbs`
(`UC.Seam.Audit.Prefix.absorb-watchedᵖ`, two prefixes fusing by `>>=ₚ-assoc`
on the nose), the extraction context's membership in the PULLBACK class is
proved (`ctx-absorb` — the inclusion the follow-up review's §2 demanded), and
`uc-audit-bounded` is the whole route: `Bounded I bad ε` crosses a budgeted
emulation to `Bounded R bad (λ q → ε (simCost q cs) + ν)`. The ledger consumer
is landed too: `EndToEnd.ledger-uc-to-pov-simCost` (and its negligible
packaging for polynomial `cs`) is `ledger-uc-to-pov` with the premise
`_≤UC^ω[ cs ]_` and the bound `εᴸ n (simCost (q + q) (cs n)) + ν n`; the
per-level `ASTotal` is derived from `TotalRun`, not assumed. One honesty note
(also in the module header): the pointwise and budgeted theorems are NOT
ordered — a
budgeted emulation is an emulation, so the pointwise theorem applies wherever
the budgeted one does and gives the sharper number (the trivial-grade
simulator costs nothing); what the budgeted statement adds is the accounting,
and the witness that the prefix extraction composes. (The pointwise/FAMILY
pair is ordered the other way and genuinely so — see *The family premise*.)
And, per the review's §3, none of this accounts for an *interactive* simulator:
the budgeted simulator at these types is a scalar.

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
   `UC-compose` is reached too, by a shorter route than `UC.Model.Bridge`'s.
   `UC.Core.Bridge` proves `f ≈ℰᶜ g → f ≈ᵁ g` at ANY monoidal base: the core's
   `grade-stable` is exactly what `Abstract2.bridge` asks for and cannot get
   from a bare kernel, and the last step is the unit ancilla, where the two
   unitor wires cancel. `UC.Model.Family.Uniform` applies it at `Famᴹ` —
   `Grading^ω` and `gradingᵗ Famᴹ` differ only in the polynomial a relayed hom
   carries, which an observation projects away, so the transport is the
   identity — and `uc-compose-agree` composes two family agreements. The one
   direction still proved only at the model is `≈ᵁ ⇒ ≈ℰᶜ`, which needs
   `UC.Model.Reading`'s rebracketing; nothing above spends it.

2. **The prefix-tolerant event class** — DONE, including the ledger consumer
   (`ledger-uc-to-pov-simCost`; see the closed obstruction above and
   `docs/prefix-tolerant-audit-plan.md`'s Outcome). The
   *interactive*-simulator accounting stays with the review's §3.

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

4. **`≈ℰⁿ` as an `Observation`, and with it an ε-retaining `UC-compose`** — the
   redesign `UC.Family`'s closing comment prices. Not attempted. Nothing above
   needs it: the negligible tier consumers use lives at layer 1
   (`UC.Saturated`), the family premise keeps its witness as a Σ rather than as
   an observation, and its own composition law (`≤UC^ωⁿ-trans`) adds εs without
   it. What it WOULD buy is the one thing *The family premise* records as
   missing — composing a family emulation with a second protocol while keeping
   the error, since `UC-compose` is inherited in the qualitative order only.
   Expanded proposal: `docs/graded-observation-redesign.md`.

## Modules added

| module | LOC | warm |
|---|---|---|
| `UC.Approximate.Decay` | 85 | 5 s |
| `Protocol.Live` | 139 | 7 s |
| `UC.Asymptotic` | 145 | 9 s |
| `UC.Asymptotic.Audit` | 56 | 10 s |
| `UC.Model.Family` | 45 | 10 s |
| `Examples.ChimericLedger.Total` | 47 | 9 s |
| `Examples.ChimericLedger.Schedule` | 127 | 10 s |
| `Examples.ChimericLedger.EndToEnd` | 284 | 11 s |
| `Examples.ChimericLedger.Real` | 93 | 11 s |
| `UC.Asymptotic.Family` | 276 | 15 s |
| `UC.Seam.Carry` (`adv-at`/`adv-from-runs`) | 126 | 9 s |

Additive edits to existing modules: `POV.asks≤-audited` (the instrumentation's
allowance cost, beside `audited`); `Carry.Emulᵁᶜ`/`emulᵁᶜ`/`pov-carryᵁᶜ` (the
UC-vocabulary premise, the first importer of `unitGrade`); `UC.Seam.Audit`
re-exports `≤UC[]⇒≤UC`; `UC` re-exports the two `UC.Asymptotic` modules — but
NOT `UC.Asymptotic.Family`, which reaches the checked closure through
`ChimericLedger.EndToEnd` instead. `UC.Seam.Grounded` gained four names
(`emSimTotal`, `subBlind⇒emul`, `simAstotal`, `emulAgreeᵁ`) by lifting the
`SimTotal` block out of `subBlind⇒unitGrade`'s `where`; that proof routes
through them and its statement is unchanged, and `EndToEnd`'s private copies
are gone (267 LOC, 10 s warm).

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
