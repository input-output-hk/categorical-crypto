# Retirement

Branch `retirement`, off `protocol-rewrite` at `ff2e2435`. This is
[`docs/uc-presheaf-preservation-plan.md`](uc-presheaf-preservation-plan.md) §6
step 7, and nothing else: every deletion below is a row of §5 whose gate is
shown satisfied by a replacement theorem steps 5 and 6 actually built, with the
replacement named. Nothing is retired for being off the main path, no statement
that stays is weakened, and no statement is deleted whose conclusion is not
recoverable through a direct statement.

Paths are relative to `src/CategoricalCrypto/` unless prefixed.

Hatches in `src/` stay at their baseline: the
`postulate|TERMINATING|primTrustMe|\{!` grep counts **16 hits before and 16
after**, all of them the words "postulate-free" in inherited comments.

One commit per candidate, each green on its own.

## 1. The prefix route's membership plumbing — RETIRED

§5 row `UC.Seam.Audit.Prefix`: "Retire `absorb-watchedᵖ`/membership plumbing
after the unchanged probability endpoint is recovered."

| name | in-repo importers (transitive through `open … public`) |
|---|---|
| `absorb-watchedᵖ` (`Prefix:99`) | `ctx-absorb`, same module. Nothing else in `src/` |
| `ctx-absorb` (`Prefix:129`) | `auditIsBoundedᴬ`, same module |
| `auditIsBoundedᴬ` (`Prefix:141`) | `uc-audit-bounded`'s class-route body, same module |
| `uc-audit-bounded` (`Prefix:154`) | `UC.Asymptotic.Audit:45` — but at `uc-audit-bounded′`, since step 6b; so the OLD PROOF had no consumer at all |

**Gate verdict: satisfied.** The endpoint is `uc-audit-bounded`, and
`uc-audit-bounded′` (`docs/direct-extraction.md` §4.3) has its type argument for
argument — `docs/consumer-migration.md` §1 moved the single consumer
(`uc-audit-boundedᵖ`) onto it with an unchanged argument list. The replacement
chain is `bounded-carry` = `Mass.dominate` + `sim-prefixed` +
`UC.Seam.Audit.Bounded.supply` + `UC.Seam.Audit.Context.extract-bounded`.

### The naming decision

§5's row retires the ROUTE, not the public name. So `uc-audit-bounded′` **is
renamed to `uc-audit-bounded`** and the prime disappears: the statement,
hypotheses and conclusion are byte-identical to `protocol-rewrite`'s
`uc-audit-bounded`, so every consumer's call site is unchanged and the public
API is stable. The only importer's `using` list is `UC.Asymptotic.Audit:45`, and
it does not break — it names one theorem and that theorem still exists under the
name it had before step 5 introduced the prime.

The alternative reading — delete `uc-audit-bounded` and keep `uc-audit-bounded′`
— would have kept a primed name as the public endpoint and left the conceptual
duplicate (two routes to one statement) resolved in the worse direction. §5's
closing paragraph ("Removing type aliases without removing a conceptual
duplication is not a worthwhile migration") argues for the direction taken.

**Net −101 LOC** (142 deleted, 41 added: the rewritten header and import list).
`prefix-absorbᵒ`, `sim-prefixed`, `bounded-carry` stay.

## 2. The prefix-tolerant event class — RETIRED

§5 row `UC.Seam.Audit`: "`watched`/`watchedᵖ` and `TrivialGrade` retire after
exact and prefix consumers migrate" — the prefix half.

| name | in-repo importers |
|---|---|
| `watchedᵖ` (`Audit:91`) | `Audit` (`AuditIsBoundedᵖ`, `BoundedIsAuditᵖ`), `Audit.Bounded` (`auditIsBoundedᵖ`, `boundedIsAuditᵖ`), `Audit.Prefix` (the three retired in §1) |
| `watched⇒watchedᵖ` (`Audit:100`) | `Bounded.auditIsBoundedᵖ`, `Prefix.ctx-absorb` |
| `AuditIsBoundedᵖ` / `auditIsBoundedᵖ` | none — `auditIsBoundedᵖ` had no consumer before this step either |
| `BoundedIsAuditᵖ` / `boundedIsAuditᵖ` | `Prefix.uc-audit-bounded`'s class-route body only |

**Gate verdict: satisfied.** After §1 nothing outside the `UC.Seam.Audit` cone
mentions `watchedᵖ`, and the one conclusion ever stated through it —
`uc-audit-bounded`'s — is now proved by `bounded-carry` off `sim-prefixed` and
`extract-bounded`. (`Examples/HashForward/Audit.agda` mentions `watchedᵖ` only
in a header sentence saying it spends no prefix tolerance; that sentence is
rewritten, not the code.)

**Net −64 LOC** (74 deleted, 10 added).

## 3. `uc-audit-carry` and its `AuditBound` bridge — RETIRED

§5 row `UC.Asymptotic.Audit`: "Retire `uc-audit-carry` returning only
`AuditBound`; keep existing probability results as proved specializations until
migrated."

| name | in-repo importers |
|---|---|
| `uc-audit-carry` (`Asymptotic/Audit:77`) | none. Its one consumer, `EndToEnd.ledger-audit-carry`, was re-routed onto `uc-audit-carryᵈ-bound` by step 6b |
| `uc-audit-carryᵈ-bound` (`Asymptotic/Audit:131`) | `EndToEnd.ledger-audit-carry:246` |
| `EndToEnd.ledger-audit-carry` | none (exported leaf); `docs/end-to-end.md` names it |

**Gate verdict: satisfied.** `uc-audit-carryᵈ` is the direct replacement — plan
§4.2's property-specific statement at the existing test, closure, monitor
transformation and budget witness. `docs/consumer-migration.md` §2 establishes
that at this instance the `AuditBound` conclusion is recovered **as the object
and not merely as the number**: the designated class is not opaque data there,
so `AuditBound f (absorb s cs (watched I bad)) (λ q → ε (simCost q cs) + ν)`
unfolds to `uc-audit-carryᵈ`'s own hypothesis list with the two `QB` arguments
dropped, which is exactly what `uc-audit-carryᵈ-bound`'s one-line body was.
`uc-audit-carryᵈ-bound` is that bridge, and step 6b already recorded that "it
retires with them".

`EndToEnd.ledger-audit-carry` is an exported theorem, so it is deleted only
because `ledger-audit-carryᵈ` carries its whole conclusion. Verified here, not
assumed: both are `uc-audit-carryᵈ{-bound}` at the SAME argument list —
`{ε = εᴸ} {ν = ν} em (monitorᴸ a V) (ideal-bounded a V si) 0<inv-pow-2` — and
`uc-audit-carryᵈ-bound`'s body is `uc-audit-carryᵈ` applied to the components of
one Σ-pattern. So `ledger-audit-carry W Et m _ _ (d , a , near)` is
`ledger-audit-carryᵈ … W Et m _ d a near`, with nothing left over.
`docs/end-to-end.md` is updated.

The probability endpoint `uc-audit-boundedᵖ` is untouched, as the row's second
clause requires.

**Net −63 LOC** (84 deleted, 21 added), across `UC.Asymptotic.Audit` and
`EndToEnd`.

## 4. The ledger's `auditEvent`/`AuditBound` exports — RETIRED

§5 row `Examples/ChimericLedger/Audit`: "Remove `auditEvent`/`AuditBound`
exports after the final consumers migrate; merge the module only if no distinct
proof content remains."

| name | in-repo importers |
|---|---|
| `auditEvent` (`:53`) | `audit-bound:57`, `audit-bounded:63`, `audit-target:82` (same module); `EndToEnd.ledger-audit-carry:250`, in its STATEMENT |
| `audit-bound`, `audit-bounded` | `audit-target` (same module) / none |
| `audit-target` (`:82`) | none — step 6b re-routed `ledger-audit-carry` off it |

**Gate verdict: satisfied.** The final consumer was
`EndToEnd.ledger-audit-carry`, retired in §3. `pov-target` (step 6b) is
`audit-target`'s own body with the class stripped off — the proved birthday
theorem read through the designated monitor, `Trajectory.monitor-bounded` at
`Birthday.target` — and `Schedule.ideal-bounded` is its family-level counterpart
and what the migrated carries consume.

**The module is NOT merged.** `pov-target` is distinct proof content: it is
strictly more general in `h₀` than `Schedule.ideal-bounded`, which fixes
`h₀ n = replicate n false`. It now has no in-repo importer and is checked as its
own leaf, joining `Carry` and `Pin` (so four `Examples/ChimericLedger/*` leaves
cover the fourteen modules, where `docs/consumer-migration.md` §5 recorded
three).

**Net −49 LOC** (60 deleted, 11 added), and the module sheds every `UC.*`
import it had.

## 5. `watched`, `TrivialGrade` and the membership extraction — RETIRED

§5 rows `UC.Seam.Audit` ("`watched` … and `TrivialGrade` retire after exact and
prefix consumers migrate") and `UC.Seam.Audit.Context`/`Bounded` ("Old
membership-based supply/extraction lemmas retire only after equivalent direct
statements serve all consumers").

| name | in-repo importers |
|---|---|
| `watched` (`Audit:77`) | `Bounded` (`ctx-watched`, `auditIsBounded`, `boundedIsAudit`); `Prefix.ctx-absorb` (§1); `Asymptotic.Audit` (`uc-audit-carry`, `uc-audit-carryᵈ-bound`, §3); `ChimericLedger.Audit.auditEvent` (§4) |
| `AuditIsBounded` / `auditIsBounded` | `ChimericLedger.Audit.audit-bounded` (§4), `Bounded.auditIsBoundedᵖ` (§2) |
| `BoundedIsAudit` / `boundedIsAudit` | `ChimericLedger.Audit.audit-bound` (§4) |
| `ctx-watched` (`Bounded:47`) | `auditIsBounded`, `Prefix.ctx-absorb` (§1) |
| `extract` (`Context:238`) | `Bounded.auditIsBounded`, `Prefix.auditIsBoundedᴬ` (§1) |

**Gate verdict: satisfied.** The two exported statements that stood *at*
`watched` — `ChimericLedger.Audit.auditEvent` and `uc-audit-carry` — retired in
§§3–4, each against the direct sibling step 6b built (`pov-target`,
`uc-audit-carryᵈ`). `AuditIsBounded`/`BoundedIsAudit` and their discharges are
statements *about* `watched` and cannot outlive it; they are precisely §5's
"application-facing pullback-membership detour". `extract` is the
membership-based extraction lemma, and its equivalent direct statements
`extract-obs`/`extract-bounded` (step 5, `docs/direct-extraction.md` §4.1) serve
the only route that stands.

What §5 keeps, and this step keeps: `Bounded.supply` (load-bearing for
`bounded-carry`); `Context.auditTest`, `audit-qb`, `audit-run`, `ctxObs`,
`extract-obs`, `extract-bounded` and the entire nontrivial-grade half
(`auditTestᵍ`, `audit-qbᵍ`, `closedᵍ`, `plug-runᵍ`, `audit-runᵍ`, `extractᵍ`,
`absorb-plugᵍ`) — the row's "context interpretation, cost, and probability
extraction".

### `UC.Seam.Audit` is kept, and why it is not forwarding-only

§5's row offers "remove if it becomes forwarding-only" (rule 19). It does not
become that. What is left is

```agda
private module A = Aud ucBaseᵒ budgetᵒ massᵒ
open A public using (…)
```

— a **parameterized module application**, not a re-export layer. `UC.Audit`
takes three arguments (`UCBase`, `Budget`, `Mass`) and this module supplies the
sealed model's, once, for five consumers (`UC.Seam.Audit.Context`, `.Bounded`
via `Prefix`, `.Prefix`, `UC.Asymptotic.Audit`, `Examples.HashForward.Audit`,
and `ChimericLedger.EndToEnd`). Rule 19's remedy — "open the source directly" —
is not available: the source is parameterized, so deleting this module means
writing the same three-argument application in each consumer, which duplicates
the instantiation rather than removing a duplication, and which the repository
has measured to be a real cost (`QUALITY-REVIEW.md`, `quantitative-family` item
3: a single `Abstract2.Action StdSetup` application is +22 s). It is also the
parent of `UC.Seam.Audit.{Context,Bounded,Prefix}`, which keep their namespace.
The `using` re-export list is unchanged: every name in it still exists, and
narrowing it is not a §5 row.

`UC.Seam.Audit.Bounded` keeps only `supply` and no longer imports the seam at
all. §4.1's instruction ("keep the rational-order arguments in `Bounded`") pins
it there; relocating it is a rule-27 question this step does not own.

**Net −142 LOC** (173 deleted, 31 added) across the three modules.

## 6. The negligible tier's metatheorem reexports — RETIRED

§5 row `UC.Family.Negligible` / `UC.Model.Family.Negligible` /
`UC.Approximate.Local`: "expose inherited UC rather than a parallel renamed
`UC.Emulation` API" | "Retire redundant metatheorem reexports, not the distinct
negligible semantics."

`UC/Family/Negligible.agda:68-74` re-exported seventeen names from
`Em UCBaseᴺ` under ᴺ-suffixed renamings. Three are consumed —
`_≈ℰᴺ_` (`:83,84`), `_≤UCᴺ_` (`:87`), `≈ℰᴺ⇒≤UCᴺ` (`:88`), all inside this module
and its bridges. **Fourteen have no consumer anywhere in `src/`**: `ℰᴺ`,
`≈ℰᴺ-refl`, `≈ℰᴺ-sym`, `≈ℰᴺ-trans`, `≈ℰᴺ-setoid`, `≈⇒≈ℰᴺ`, `≈ℰᴺ-congˡ`,
`≈ℰᴺ-congʳ`, `grade-stableᴺ`, `_≤UCᴺ⁺_`, `≤UCᴺ-refl`, `≤UCᴺ-trans`,
`dummy-completeᴺ`.

**Gate verdict: satisfied, and this is the only place the row's own words point.**
The fourteen are verbatim renamings of `UC.Emulation`'s metatheorems — literally
"a parallel renamed `UC.Emulation` API". **No proof is deleted**: every one is
still `CategoricalCrypto.UC.Emulation UCBaseᴺ`'s, reached by applying that
module, which is what the row means by "expose inherited UC".

The negligible semantics are untouched: `_∼ᴺ_`, `∼ᴺ-isEquivalence`, `∼ᴺ-gap`
(`UC.Approximate.Local`), `Observationᴺ`, `UCBaseᴺ`, `_≤UCᴺ_`, both one-way
bridges `≈ℰⁿ⇒≈ℰᴺ`/`≈ℰⁿ⇒≤UCᴺ`, and `UC.Approximate.LocalTests` (re-run green).

**Net −3 LOC** (11 deleted, 8 added): seven lines of renamings for two, plus a
rewritten comment.

## 7. What §5 leaves standing, and why

Everything below was audited for consumers and gate satisfaction and is
**kept**. Each line says which.

### Gates explicitly not met

* **`UC.Audit`** — the row requires "a direct quantitative theorem at the same
  `UCBase`/`Budget`/`Mass` scope, with arbitrary joint test-closure-budget
  predicates and two-class transfer". `carry-obs` is not that: it is
  `audit-carry`'s structural half at ONE class-free conclusion, with no event
  predicate and no `Absorbs`. And `Examples.HashForward.Audit` consumes
  `AuditBound`, `absorb`, `absorb-absorbs`, `pinned`, `pinned-bound` and
  `audit-carry` at a NONTRIVIAL grade, through `extractᵍ`. `AuditEvent`,
  `AuditBound`, `Absorbs`, `absorb`, `absorb-absorbs`, `pinned`,
  `pinned-bound`, `audit-carry`, `carry-obs` all stay.
* **`UC.Robust.Observation`** — the row says delete the independently scoped
  `UCBase` theorem "only if its whole original scope is recovered, not merely
  the machine instance". It is not: `robust-sub` is stated at an arbitrary
  `UCBase`, where there is no graded Kleisli triple and so no `run`/`run-sub`
  (`QUALITY-REVIEW.md`, `direct-extraction`). Kept.
* **`UC.Asymptotic.Family`** — the row says "Retire duplicate relation algebra
  after replacing its proof content". **Nothing there is a duplicate**, and the
  check is worth recording. `docs/quantitative-family.md` §3 already performed
  the retirement the row is about: `_≈ᶠ[_]_` is now a definitional alias of
  `imgᶠ B R ≈ctxᴬ[ ε ] imgᶠ B I`, so the relation no longer has an independent
  definition. What is left, `≤UC^ωⁿ-refl`/`-sym`/`-trans`, is NOT a duplicate of
  `Contextual`'s `≈ctx-refl`/`-sym`/`-trans`: those are stated at
  `_≈ctx[_]_`, a **different relation** from `_≈ctxᴬ[_]_` (the test's domain is
  bracketed the other way — `Contextual:85-93`), and bridging them costs
  `≈ctx⇒≈ctxᴬ`'s `subst` and two `shuffle⇒`s. Nor are they the same statement:
  `_≤UC^ωⁿ_` is a Σ over the schedule with a `NegligibleBound`, where the
  `≈ctx` algebra is at a fixed one. The shared text is three one-line bodies
  (`≈ₚ[]-refl`, `≈ₚ[]-sym`, `≈ₚ[]-trans`), which is one primitive used twice,
  not duplicated proof content. Per the brief and §5's closing paragraph the
  alias itself is not deleted for being an alias; the acceptance tests
  (`admits-inv-pow-2`, `rejects-inv-suc`, `pointwise-exact`,
  `pointwise-rejects`) and `≈ᶠ-runs` are kept as the row directs.

### Zero-consumer wrappers whose gate is vacuous, not met

§5's opening is explicit: "Retirement is conditional on replacement proofs and
importer migration, not on the absence of a compiler error in a smaller
statement. Do not delete proofs merely because they are no longer on the main
path." The names below have no in-repo consumer, but none of them **became**
consumerless through anything steps 1–6 built — they were already unreached
before the plan started, so no gate reading "after callers migrate" is
satisfied by this arc. They are listed so the maintainer can rule; this step
does not.

| module | zero-consumer name | what would replace it |
|---|---|---|
| `UC.Model.Family.Uniform` | `uc-compose-agree` — RULED since, and deleted with the whole module, whose surviving content is `UC.Family.Vanishing` instantiated at the machine ingredients in `UC.Model.Family` | inherited `UC-compose` (via `UC.Core.Bridge:51`) at two `≈ℰ^ω⇒≤UC` calls — which was its body |
| `UC.Model.Family.Ingest` | `ingest-≈ℰ`, `ingest-≤UCᵁ`, `ingest-≤UCᴺ` (`:108-130`) — `ingest-≈ℰⁿ` is no longer zero-consumer: `ingest-≤UCᴺ` spends it into `Canonicalᴺ._≤UC_` | `Model.Family.absorb-negl` / `carried-negligible` / `≈ℰ^ω⇒≤UC`. The row's clause is "Redundant qualitative projections may retire **after callers migrate**", and the module has never had a caller: its sole importer is `UC/Model.agda:55`, a bare `import` for the build closure. `ingest` and `dominatedᵒ` are the row's "not the domination proof". **`ingest-≤UC` is no longer among them: it has been RETIRED** with the rest of the homegrown order, its gate now met — `ingest-≤UCᵁ` is its conclusion at the inherited order, off the same `ingest-≈ℰ` and the same premises, so nothing it concluded is lost |
| `UC.Model.Bridge` | `≈ℰᶜ⇔≈ᵁ`, `≈ᴳ⇔≈ℰᶜ`, `≈ᵁ⇔≈ᴬ` (`Reading:76`), `≈ℰᶜ⇒≈ℰ`, `≈ᴳ-refl`, `≈ᴳ-sym`, `≈ᴳ-congʳ`, `≈ᴳ⇒≈ᵁ`, `≤UCᶜ⇒≤UC`, `_≤UCᶜ_` | six of these are already one standing entry in `QUALITY-REVIEW.md:438` ("Rule 32 makes every one of these your call"). §5's row for these modules says they "still have independent work" |

`UC.Model.Dominated` and `UC.Core.Bridge` have **no** zero-consumer export:
`unqb-testᵒ`, `unqb-closᵒ` and `ctxRunᵒ` are consumed inside `dominatedᵒ`, and
the first two could not be replaced by `qb-from-image` anyway — that is not
callable outside the `opaque unfolding 𝔾ᵒ sealᵒ` block, which is why they exist.
`UC.Model.Family.Negligible`'s whole body is two parameterized applications at
the model — the tier and its `ucSetupᴺ` — the same shape as `UC.Seam.Audit`'s
and kept for the same reason.

### One duplication noticed and not acted on

`ifaceᶠ` is defined twice with identical bodies —
`UC/Asymptotic/Family.agda:85` and `UC/Model/Family/Ingest.agda:64`, both
`ifaceᶠ n = ifaceᵒ (B n)`. Only the first has an external consumer
(`FactorEps:55,90`). Merging them would make a `Model`-layer module import an
`Asymptotic`-layer one; no §5 row covers it. Flagged.

## 8. The parked maintainer calls — untouched

One line each, per the brief.

* **Reroute `ledger-uc-to-pov` through the family theorem?** — unchanged.
  Nothing here touches `ledger-uc-to-pov` or `UC.Asymptotic.uc-agree`.
* **Shed `uc-audit-bounded`'s unused premises (`ASTotal`, the `bad`-budget
  law)?** — unchanged in kind; after §1 there is one exported statement carrying
  them rather than two (`uc-audit-bounded`, `uc-audit-boundedᵖ`), and
  `ledger-uc-to-pov-simCost` still derives the `ASTotal` from `TotalRun` to
  supply it, so shedding them is still a statement change and still your call.
* **A fifth `Allowance-mono` component of `_≤UC^ωᵉ_`?** — unchanged; no
  statement here mentions `_≤UC^ωᵉ_`.
* **Retire `≤UC⇒≤UCᶜ`?** — left standing, as instructed. It still has no in-repo
  consumer (`docs/presheaf-action.md`), and neither does `≤UCᶜ⇔≤UC`.
* **The Track-A stack** — untouched; nothing in this step reaches it.

## 9. LOC and cost

Warm figures are single-`Checking`-line runs under
`pagda --useUntracked false check … -- +RTS -M8G -H1G -RTS` in plain `timeout`,
rc=0 and an empty
`ModuleDoesntExport|UselessPublic|UselessPrivate|DuplicateUsing|error:|Failed to solve|Heap exhausted`
gate on every run. Both columns are forced warm by appending a comment line,
running, and reverting it (agda 2.8 keys staleness on content, so deleting the
`.agdai` alone hits pagda's own content-hash cache). "Before" is measured on
this machine in a detached worktree at `ff2e2435`, not quoted from an earlier
branch's table; that worktree is removed again.

| module | LOC | warm before | warm after | rule-5 budget |
|---|---|---|---|---|
| `UC.Seam.Audit` | 154 → 26 | 9 s | 9 s | 66 s |
| `UC.Seam.Audit.Bounded` | 104 → 49 | 9 s | 9 s | 72 s |
| `UC.Seam.Audit.Context` | 249 → 226 | 10 s | 10 s | 116 s |
| `UC.Seam.Audit.Prefix` | 237 → 136 | 9 s | 10 s | 94 s |
| `UC.Asymptotic.Audit` | 155 → 111 | 10 s | 9 s | 87 s |
| `UC.Audit` (comment only) | 196 → 195 | 4 s | 5 s | 108 s |
| `UC.Asymptotic` (comment only) | 144 → 146 | 10 s | 9 s | 96 s |
| `UC.Family.Negligible` | 88 → 85 | 4 s | 5 s | 81 s |
| `Examples.ChimericLedger.Audit` | 88 → 39 | 10 s | 6 s | 69 s |
| `Examples.ChimericLedger.EndToEnd` | 314 → 294 | 10 s | 11 s | 133 s |
| `Examples.HashForward.Audit` (comment only) | 137 → 137 | 10 s | 9 s | 94 s |
| `CategoricalCrypto.UC` | 228 → 229 | 9 s | 10 s | 117 s |

Nothing moves by more than a second in either direction, and nothing is within
an order of magnitude of its rule-5 budget or the 20 % regression bar. The
figures are dominated by interface deserialization, which is why deleting 128
lines from `UC.Seam.Audit` costs the same 9 s: what is gone was cheap. The one
visible win is `Examples.ChimericLedger.Audit`, 10 s → 6 s, which is the module
dropping its whole `UC.*` import list along with `auditEvent`.

Net over `src/`: **167 insertions, 593 deletions, −426 lines**, across 14 files.

## 10. Closure

Every run `pagda --useUntracked false check … -- +RTS -M8G -H1G -RTS` under
plain `timeout`, rc=0 with an empty
`ModuleDoesntExport|UselessPublic|UselessPrivate|DuplicateUsing|error:|Failed to solve|Heap exhausted|No space left`
gate.

* Roots: `src/CategoricalCrypto.agda` (11 modules re-elaborated, 28 s),
  `UC.agda`, `UC/Model.agda`, `UC/Factor.agda`,
  `UC/Approximate/LocalTests.agda`.
* `Examples/ChimericLedger/`: the three leaves `Carry`, `Pin`, `FactorEps`,
  plus `EndToEnd`, `Real`, `Factor`, `QueryBound`, and `Audit` — now a fourth
  leaf, since §4 removed its only importer.
* `Examples/HashForward/{Audit,Resource,UC}`.
* `Examples/MerkleDamgard{,/Core,/Pin,/QueryBound}`.
* `Examples/ROCommitment{,/Asymptotic,/Extraction,/Game,/Oracle,/Resource,/Test,/Transport,/UC}`
  and `Examples/ROCommitment/Hiding{,/Asymptotic,/Game,/Test,/UC}`.

Escape hatches: `grep -rnE 'postulate|TERMINATING|primTrustMe|\{!' src/` is **16
before and 16 after**, every hit a comment (fifteen of them the words
"postulate-free", one "no postulate left").
