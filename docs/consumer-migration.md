# Consumer migration

Branch `consumer-migration`, off `protocol-rewrite` at `82b967b1`. This is
[`docs/uc-presheaf-preservation-plan.md`](uc-presheaf-preservation-plan.md) §6
step 6, the half that `docs/ledger-lift-eps.md` left (it did §4.5, the
ε-retaining hash lift), plus the rule-27 relocations recorded in
`QUALITY-REVIEW.md`. Nothing is retired here — that is step 7 — and every
existing exported statement is unchanged; only proofs re-route and consumers
change which theorem they call.

Everything below is a checked term unless it is in "Not delivered, precisely".
Paths are relative to `src/CategoricalCrypto/` unless prefixed.

Hatches in `src/` stay at their baseline: the
`postulate|TERMINATING|primTrustMe|\{!` grep counts **16 hits before and 16
after**, all of them the words "postulate-free" in inherited comments.

## 1. `uc-audit-boundedᵖ` onto the direct route

`UC/Asymptotic/Audit.agda:148`. The statement is byte-identical; the body is the
drop-in `docs/direct-extraction.md` §"Not delivered, precisely" spelled out —
the import moves from `uc-audit-bounded` to `uc-audit-bounded′` and the call
site's argument list is unchanged, the two theorems having the same Agda type
argument for argument.

What leaves the family route with it: `boundedIsAuditᵖ`, `audit-carry` at
`watchedᵖ`, `absorb-absorbs`, `auditIsBoundedᴬ`, `ctx-absorb` and
`absorb-watchedᵖ`. What it now spends instead: `bounded-carry` = `dominate` +
`sim-prefixed` + `supply` + `extract-obs`.

`EndToEnd.ledger-uc-to-pov-simCost` (`:264`) and
`ledger-pov-simCost-negligible` (`:296`) are **byte-identical** to
`protocol-rewrite`'s (`git diff 82b967b1` touches neither) and green: the bound
`εᴸ n (simCost (q + q) (cs n)) + ν n` and the `TotalRun` premise the per-level
`ASTotal` is derived from both stand.

## 2. A direct form of `uc-audit-carry`'s conclusion

### The generic half — `UC/Audit.agda:156`

```agda
carry-obs : (f : A ⇒ X ⊛ B′) (g : A ⇒ Y ⊛ B′) (s : Y ⇒ X) → f ≈ℰ (sub s ∘ g)
          → (W : Obj) (Et : Test (W ⊛ (X ⊛ B′))) (m : Closure (W ⊛ A))
            (δ : ℚ) → 0ℚ ℚ.< δ → (n : ℕ)
          → Σ[ k ∈ ℕ ] at n (obs (tv₁ W f Et) m)
                       ℚ.≤ at k (obs (tv₁ W g (tv₁ W (sub s) Et)) m) ℚ.+ δ
```

`audit-carry`'s whole structural content, hoisted out of its `where` block and
generic over `UCBase`/`Budget`/`Mass`: the emulation evaluated at one context,
the simulator slid onto the test by `UC.Environment.tv₁-∘` (item 4b), the
`Mass` domination at the slack. `audit-carry`'s proof now calls it, its
statement untouched — so this is a decomposition, not a second copy.

### The property-specific half — `UC/Asymptotic/Audit.agda:105`

```agda
uc-audit-carryᵈ : (em : R ≤UC^ω[ cs ] I) (bad : Watch B)
                → ((n : ℕ) → Bounded (I n) (bad n) (ε n))
                → ((n : ℕ) → 0ℚ ℚ.< ν n)
                → (n : ℕ) (W : Channel)
                  (Et : Test (W ⊛ (𝟘ᴳ ⊛ ifaceᵒ (B n)))) (m : Closure (W ⊛ 𝟘ᵒ))
                  (q : ℕ) (d : Strat (Neg (B n)) (Pos (B n))) → asks≤ q d
                → obs (tv₁ W (closedᵒ (morphism (I n)))
                           (tv₁ W (subᵉ (sim (em n))) Et)) m
                  ≈ₚ runᴹ (morphism (I n)) (bad n d)
                → (k : ℕ) → Pr≤ k (obs (tv₁ W (closedᵒ (morphism (R n))) Et) m)
                            ℚ.≤ ε n q ℚ.+ ν n
```

This is plan §4.2's "property-specific statement … stated directly at the
existing test, closure, monitor transformation and budget witnesses":
`AuditEvent`, `AuditBound`, `watched` and `absorb` occur nowhere in it, the
ideal supply is layer 1's own `Bounded`, and the only thing the hypothesis
names beyond the context is the monitored run the transformed test observes.
The proof is `carry-obs` then `UC.Seam.Audit.Bounded.supply`.

Two premises the class route spends are **not** spent: the simulator's query
certificate `sim-qb`, and `ctxBudget`. Both exist to move an allowance across a
quantifier over budgeted TESTS; here the allowance moves in the strategy `d`,
which is `Bounded`'s own quantifier.

### Tests versus strategies — the verdict

The blocker `docs/direct-extraction.md` recorded ("an `AuditBound` is a
statement about every budgeted *test*, a `Bounded` about every budgeted
*strategy*, and `StratIsEnv` goes one way only") is **real but narrower than
stated**, and the split is worth naming exactly.

* **Recoverable, in full, as the object and not merely the number.**
  `uc-audit-carry`'s `AuditBound`-shaped conclusion is `uc-audit-carryᵈ` past
  one Σ-pattern: `UC/Asymptotic/Audit.agda:131`,

  ```agda
  uc-audit-carryᵈ-bound : (em : R ≤UC^ω[ cs ] I) (bad : Watch B)
                        → ((n : ℕ) → Bounded (I n) (bad n) (ε n))
                        → ((n : ℕ) → 0ℚ ℚ.< ν n) → (n : ℕ)
                        → AuditBound (closedᵒ (morphism (R n)))
                            (absorb (sim (em n)) (cs n) (watched (I n) (bad n)))
                            (λ q → ε n (simCost q (cs n)) ℚ.+ ν n)
  uc-audit-carryᵈ-bound em bad bi pos n W Et m _ _ (d , a , near) =
    uc-audit-carryᵈ em bad bi pos n W Et m _ d a near
  ```

  The reason is that at this instance the event class is not opaque data: the
  hypothesis of `AuditBound f (absorb s cs (watched I bad)) (λ q → ε (simCost q cs) + ν)`
  unfolds to `Σ[ d ] asks≤ (simCost (ctxBudget c c′) cs) d × (the transformed test
  observes the ideal monitored run)` — which IS `uc-audit-carryᵈ`'s hypothesis
  list, with the two `QB` arguments dropped on the floor. The ideal premise
  changes shape (`Bounded I bad ε` where `uc-audit-carry` takes
  `AuditBound … (watched I bad) ε`) and that is not a weakening: at the trivial
  grade the two imply each other, by `boundedIsAudit` and by `auditIsBounded`
  (which additionally wants the monitor's budget law, and `QueryPreserving` is
  what every consumer already supplies).

  This is verified mechanically at the ledger rather than by eye: after this
  step `EndToEnd.ledger-audit-carry` (`:246`) is proved by
  `uc-audit-carryᵈ-bound` at a statement that still mentions
  `Ad.auditEvent n inputConsuming (gen a V n)`, so Agda unifies the two.

* **NOT recoverable: a probability over every budgeted strategy at `watched`.**
  What the recorded blocker really guards is the step `extract` takes, and it
  does not become available: turning an `AuditBound` at `watched` into layer 1's
  `Bounded R bad ε` needs the extraction context — *with the simulator in front
  of it* — to be a member of the real-side class, i.e. to observe an ideal
  monitored run **exactly** (`≈ₚ`). It does not: the simulator's initialization
  prefixes the observation, and an almost-surely-total initialization is all
  `subBlind` can give. That is why `ctx-absorb` is stated at the widened
  `watchedᵖ` and not at `watched`, and it is why the probability endpoint is
  `uc-audit-bounded′`/`bounded-carry` (item 1) rather than a corollary of
  `uc-audit-carry`. The two carries reach the same kind of conclusion by routes
  that do not compose, exactly as `docs/end-to-end.md`'s "Obstruction" section
  says.

  Typed, that missing statement is
  ```agda
  auditIsBoundedʷ : (B : Iface) (R I : Protocol unitᴵ B) (bad : …) (s : 𝟘ᴳ ⇒ 𝟘ᴳ) (cs : ℕ)
                  → ((q : ℕ) (d : Strat (Neg B) (Pos B)) → asks≤ q d → asks≤ q (bad d))
                  → AuditBound (closedᵒ (morphism R)) (absorb s cs (TG.watched I bad)) ε
                  → Bounded R bad ε
  ```
  and it is false as stated for want of the exact identification, not merely
  unproved.

So the honest summary for the retirement gate: `uc-audit-carry`'s conclusion has
a direct replacement (`uc-audit-carryᵈ`, with `uc-audit-carryᵈ-bound` the object
itself); what has no direct replacement, and needed none, is the extraction from
`watched` to a probability, which no consumer ever used.

### The mechanical pin is a measured perf defect, not an omission

`uc-audit-carryᵈ-bound`'s signature is `uc-audit-carry`'s conclusion spelled
again. The obvious guard against drift — an
`at : {A : Set ℓ} → A → A → A` pin applying both theorems at shared arguments,
the idiom `FactorEps.migration-pin` uses — makes Agda unify two applied
`AuditBound`s at `absorb … (watched …)`, and that does not come back: killed at
**690 s wall / 8.75 GiB RSS** with `+RTS -M8G -H1G` (the module's own warm cost
is 9.3 s), the `UC.Seam.Grounding` record-eta cliff at the machine composite
under `watched`. Per house rule 31 the pin is dropped rather than paid for. The
ledger's own re-route (`ledger-audit-carry` above) is the same check at the one
instance that matters and costs nothing.

## 3. The ledger consumers

### The ideal bound, stated directly

`Examples/ChimericLedger/Audit.agda:74`

```agda
pov-target : (h₀ : Hash) (ser-inj : {t u : Tx} → ser t ≡ ser u → t ≡ u) (a : Addr) (V : ℕ)
           → let s₀ = genesis h₀ a V in
             POVmonitor inputConsuming s₀ (AtBirthday.εbirthday h₀ ser-inj)
```

the proved birthday theorem read through the designated monitor
(`Trajectory.monitor-bounded` at `Birthday.target`), with no UC vocabulary in
it at all. It is `audit-target`'s old body: `audit-target` (`:82`, statement
verbatim) is now `audit-bound … pov-target`, so the class is visibly a wrapper
around it. The family-level counterpart, `Schedule.ideal-bounded`, already had
this shape and is what the migrated proofs consume.

### The real side

> **Superseded 2026-09-21:** `ledger-audit-carryᵈ` and the two `simCost`
> theorems below are deleted with the rest of the budgeted route
> (`docs/end-to-end.md` §4); the four surviving `EndToEnd` theorems are
> `ledger-uc-to-pov-family`, `ledger-pov-family-negligible`,
> `ledger-uc-to-pov` and `ledger-pov-negligible`.

`Examples/ChimericLedger/EndToEnd.agda:231`

```agda
ledger-audit-carryᵈ : (a V : ℕ) → SerInj → (R : Systems LedgerIf^ω) (cs : ℕ → ℕ)
                      (em : R ≤UC^ω[ cs ] Ideal a V) (n : ℕ) (W : Channel)
                      (Et : Test (W ⊛ (𝟘ᴳ ⊛ ifaceᵒ (LedgerIf^ω n)))) (m : Closure (W ⊛ 𝟘ᵒ))
                      (q : ℕ) (d : Strats n) → asks≤ q d
                    → obs (tv₁ W (closedᵒ (morphism (Ideal a V n)))
                               (tv₁ W (subᵉ (sim (em n))) Et)) m
                      ≈ₚ runᴹ (morphism (Ideal a V n)) (monitorᴸ a V n d)
                    → (k : ℕ) → Pr≤ k (obs (tv₁ W (closedᵒ (morphism (R n))) Et) m)
                                ℚ.≤ εᴸ n q ℚ.+ ν n
```

`uc-audit-carryᵈ` at the ledger, off `Schedule.ideal-bounded`.

### Which of the `EndToEnd` theorems changed, and which did not

| theorem | line | statement | proof |
|---|---|---|---|
| `ledger-uc-to-pov` | `:125` | verbatim | unchanged — never mentioned the class |
| `ledger-pov-negligible` | `:151` | verbatim | unchanged |
| `ledger-uc-to-pov-family` | `:189` | verbatim | unchanged |
| `ledger-pov-family-negligible` | `:211` | verbatim | unchanged |
| `ledger-audit-carry` | `:246` | verbatim | **re-routed** onto `uc-audit-carryᵈ-bound` + `Schedule.ideal-bounded`, off `Aud.audit-target` |
| `ledger-uc-to-pov-simCost` | `:264` | verbatim | unchanged here; re-routed by item 1, one layer up |
| `ledger-pov-simCost-negligible` | `:296` | verbatim | unchanged |

`Factor.ledger-pov-from-hash`, `FactorEps.*` and `Real.ledger-pov` are
untouched and green.

### Remaining consumers — step 7's input

By name, after this step. (`UC.Seam.Grounded`'s `module TG = TrivialGrade 𝟘ᴳ ιᴳ`
is the **Grounding** `TrivialGrade`, a different module of the same name, and is
not on this list — `docs/direct-extraction.md` records the trap.)

| name | remaining in-repo consumers |
|---|---|
| `TrivialGrade.watched` (`UC/Seam/Audit.agda:77`) | `UC.Seam.Audit.AuditIsBounded`/`BoundedIsAudit` (its own module); `UC.Seam.Audit.Bounded` — `ctx-watched:47`, `auditIsBounded:55`, `auditIsBoundedᵖ:61` (via `watched⇒watchedᵖ`), `boundedIsAudit:94`; `UC.Seam.Audit.Prefix.ctx-absorb:135` (via `watched⇒watchedᵖ`); `UC.Asymptotic.Audit` — `uc-audit-carry:77` and `uc-audit-carryᵈ-bound:131`, both in their conclusions; `Examples.ChimericLedger.Audit.auditEvent:53` |
| `watched⇒watchedᵖ` (`Audit.agda:100`) | `Bounded.auditIsBoundedᵖ`, `Prefix.ctx-absorb` |
| `module TrivialGrade` (audit) | `UC.Seam.Audit.Bounded:42`, `UC.Seam.Audit.Prefix:81`, `UC.Asymptotic.Audit:58`, `Examples.ChimericLedger.Audit:49` |
| `Examples.ChimericLedger.Audit.auditEvent` | `audit-bound:57`, `audit-bounded:63`, `audit-target:82` (same module); `EndToEnd.ledger-audit-carry:250` — in its STATEMENT, no longer in any proof |
| `AuditBound` | `UC.Audit` (its own), `UC.Seam.Audit` (re-export + the four `TrivialGrade` statements), `UC.Seam.Audit.Context` (`extract`, `extractᵍ`), `UC.Seam.Audit.Prefix` (`auditIsBoundedᴬ`, `uc-audit-bounded`), `UC.Asymptotic.Audit` (`uc-audit-carry`, `uc-audit-carryᵈ-bound`), `Examples.ChimericLedger.Audit`, `EndToEnd.ledger-audit-carry`, **and `Examples.HashForward.Audit`** — which uses `AuditBound`/`absorb`/`pinned`/`audit-carry` at a NONTRIVIAL grade and never mentions `watched`, so it gates on §5's `UC.Audit` row alone |

The shape of what is left: `watched` and its module now have exactly two
exported statements standing at them — `ChimericLedger.Audit.auditEvent` (with
its three wrappers) and `uc-audit-carry` — and both now have a direct sibling
(`pov-target`, `uc-audit-carryᵈ`) with the same content and no class in it.
`uc-audit-carryᵈ-bound` deliberately stands at `watched` too: it is the bridge
that makes the retirement a deletion rather than a restatement, and it retires
with them.

## 4. The rule-27 relocations

One commit each, statements verbatim, importers updated.

| # | what | from | to | note |
|---|---|---|---|---|
| a | `qb-oneCall` | `Examples/ChimericLedger/QueryBound.agda:169` | `UC/QueryBound.agda:423` (`open OneCall public`, `:426`) | `qb-ledger` stays as its instance (`Examples/ChimericLedger/QueryBound.agda:37`), 195 → 42 LOC |
| b | the `UCBase`-level slide | `UC/Audit.agda:177` + `UC/Robust/Observation.agda:99` | `UC/Environment.agda:88` as `tv₁-∘` | see below |
| c | `0≤drift` | `ROCommitment/Game.agda:503` + `Hiding/Game.agda:390` | `ProbabilisticLogic/Distribution/Uniform.agda:139` | the level `k` becomes an argument |
| d | `lookup-here` | `ROCommitment/Oracle.agda:37` | `ROCommitment/Extraction.agda:54` | done — no cycle: `Oracle` **already** imported `Extraction` |
| e | the three ℚ helpers of `ℚ-metric` | inlined in `UC/Approximate/Separating.agda:48` | `Data/Rational/Properties/Ext.agda:81,84,87` | done — rebuild measured, see below |

### (a) `qb-oneCall`

Stated over an arbitrary `Protocol A B` and nothing about it is the ledger's.
`UC.QueryBound` gains `Protocol`, `Protocol.Machine`, `OracleCall`,
`Machines.Pointwise` and the two `Kleisli.Discrete` modules; there is no cycle
(`Protocol.Machine` imports no `UC.*`) and the module's warm cost moves
15.5 s → 15.8 s against a rule-5 budget of 60 + 647/4 ≈ 222 s. It sits beside
`qb-closed`, the other hom-level inhabitation. `Dp.Reasoning`'s `bindˣ`/`≈sym`
are imported with a `using` list because `UC.QueryBound` has its own private
`_⟨≈⟩_`/`bindᶠ` with the same definitions.

### (b) the slide

```agda
tv₁-∘ : (Y : Obj) {A B′ C′ : Obj} (k : B′ ⇒ C′) (g : A ⇒ B′) (E : Test (Y ⊛ C′))
      → tv₁ Y (k ∘ g) E ≈ tv₁ Y g (tv₁ Y k E)
tv₁-∘ Y k g E = ∘-resp-≈ʳ T₁-∘ ○ sym-assoc
```

**`UC.Environment` rather than `UC.Emulation`, and the reason is placement, not
reachability.** Both consumers import `UC.Emulation base`, which re-exports
`UC.Environment base` publicly, so either module is visible to both. What
decides it is rule 28: the statement mentions `tv₁`, `Test` and `∘` and nothing
else — no `_≤UC_`, no simulator, no emulation — and `tv₁`/`tv₁-cong` are
defined in `UC.Environment`. Putting it in `UC.Emulation` would separate a
lemma from the definition it is about in order to sit next to a relation it
does not mention. (`UC.Seam.Slide` cannot serve either way: `UC.Robust.Observation`
must not import the seam, which `docs/direct-extraction.md` already recorded.)

Both sites call it: `UC/Audit.agda:184` (inside `audit-carry`, now through
`carry-obs`) and `UC/Robust/Observation.agda:96`, where the single-use `where`
block is inlined (rule 18) and the second argument is written `tv₁ W (sub s) Et`
rather than `Et ∘ T₁ W (sub s)`.

### (e) the `Dp`-rebuild measurement

The recorded objection was "placing them there would have rebuilt the whole `Dp`
closure for three one-liners". Measured once, on this machine, with the tree
otherwise at its final state:

> `pagda --useUntracked false check src/CategoricalCrypto.agda -- +RTS -M8G -H1G -RTS`
> after editing `Data/Rational/Properties/Ext.agda`:
> **rc=0, 208 s, 141 modules re-elaborated**, warning gate empty.

That is 12 % of the 1800 s rebuild ceiling, so the hoist is done.
`Separating.agda` loses five names from its `Data.Rational.Properties` import
list and `ℚ-metric`'s three record fields become one call each; the module is
90 → 86 LOC and 5.3 s warm either way.

## 5. Root wiring — none owed, and why

`docs/ledger-lift-eps.md` §8 asked for `Examples.ChimericLedger.FactorEps` and
`.QueryBound` to be wired into a root. **They already are, in the only sense the
other twelve are**, and there is no root to edit:

* `Examples/ChimericLedger.agda` is the ledger's *definition* module — `Ledger`,
  `Replay`, `Step` — and is imported BY the other thirteen. It imports none of
  them, so it is not a root of the cone.
* There is no `*Tests` module for the cone, and `src/CategoricalCrypto.agda`
  imports nothing under `Examples.ChimericLedger`; its header says so
  ("Outside still, each with its own root: the protocol-layer examples").
* So the fourteen modules are checked **per file**, reachable through exactly
  three leaves — `Carry`, `Pin` and `FactorEps` — whose import closures cover
  all fourteen (`FactorEps` covers twelve; `Carry` and `Pin` are the other two).
* `QueryBound` is not unreached: `FactorEps.agda:43` imports it. And `FactorEps`
  is a leaf in precisely the position `Carry` and `Pin` have always occupied.

So: **checked per-file with no root; the root is left alone**, per the brief's
instruction. The closure verification below checks all three leaves.

`UC.Asymptotic.Compose`, which `docs/quantitative-family.md` §9 also owed, is
already imported by `src/CategoricalCrypto/UC.agda:194` with an inventory row at
`:159`; nothing further is owed there.

`src/CategoricalCrypto/UC.agda`'s inventory gained four rows for names this step
moved or added: `tv₁-∘` (the `UC.Environment` row), `qb-oneCall` (the
`UC.QueryBound` row), `carry-obs` (the `UC.Audit` row) and `uc-audit-carryᵈ`
(the `UC.Asymptotic` row). No import changed — all four already reach the
closure through rows that were there.

## 6. Module costs

Canonical check, `pagda --useUntracked false check … -- +RTS -M8G -H1G -RTS`
under plain `timeout`, rc=0 and an empty
`ModuleDoesntExport|UselessPublic|UselessPrivate|DuplicateUsing|error:|Failed to solve|Heap exhausted`
gate on every run. Warm figures are single-`Checking`-line runs, forced by
deleting the module's `.agdai` under `_build/`.

| module | LOC | warm before | warm after | rule-5 budget |
|---|---|---|---|---|
| `UC.Environment` | 162 → 169 | 2.3 s | 2.2 s | 102 s |
| `UC.Robust.Observation` | 120 → 118 | 2.0 s | 2.0 s | 89 s |
| `UC.Audit` | 188 → 196 | 4.5 s | 4.3 s | 109 s |
| `UC.Seam.Audit` | 153 → 154 | —† | 9.0 s | 99 s |
| `UC.Asymptotic.Audit` | 81 → 155 | 9.6 s | 9.3 s | 99 s |
| `UC.QueryBound` | 509 → 647 | 15.5 s | 15.8 s | 222 s |
| `UC.Approximate.Separating` | 90 → 86 | 5.3 s | 5.3 s | 82 s |
| `Data.Rational.Properties.Ext` | 137 → 150 | 4.3 s | 4.1 s | 98 s |
| `ProbabilisticLogic.Distribution.Uniform` | 248 → 255 | 5.7 s | 5.4 s | 124 s |
| `Examples.ChimericLedger.Audit` | 77 → 88 | 10.0 s | 9.9 s | 82 s |
| `Examples.ChimericLedger.EndToEnd` | 283 → 314 | 10.6 s | 10.5 s | 139 s |
| `Examples.ChimericLedger.QueryBound` | 195 → 42 | 9.5 s | 8.8 s | 71 s |
| `Examples.ROCommitment.Game` | 586 → 582 | 7.2 s | 7.1 s | 205 s |
| `Examples.ROCommitment.Hiding.Game` | 578 → 574 | 6.3 s | 6.2 s | 203 s |
| `Examples.ROCommitment.Oracle` | 40 → 28 | 5.5 s | 5.5 s | 67 s |
| `Examples.ROCommitment.Extraction` | 120 → 127 | 5.7 s | 5.6 s | 92 s |
| `CategoricalCrypto.UC` | 215 → 228 | —† | 9.7 s | 116 s |

† comment-only edit; no before was measured and none is claimed.

Nothing moves by more than 0.5 s, and nothing is within an order of magnitude of
its budget or the 20 % regression bar. A large part of each figure is interface
deserialization, which is why +138 lines in `UC.QueryBound` cost 0.3 s.

Closure, all green with an empty warning gate: `src/CategoricalCrypto.agda`,
`UC.agda`, `UC/Model.agda`, `UC/Approximate/LocalTests.agda`, the three
`Examples/ChimericLedger/*` leaves (`FactorEps`, `Carry`, `Pin`), both
`Examples/HashForward/*`, `Examples/MerkleDamgard{,/Core,/Pin,/QueryBound}`,
`Examples/ROCommitment{,/Asymptotic,/Extraction,/Game,/Oracle,/Resource,/Test,/Transport,/UC}`
and `Examples/ROCommitment/Hiding{,/Asymptotic,/Game,/Test,/UC}`.

## 7. Not delivered, precisely

Typed residuals — signatures, never holes or postulates in `src/`.

1. **`auditIsBoundedʷ`** (§2 above): extraction from `watched` — as opposed to
   `watchedᵖ` — to layer 1's `Bounded`. Not a gap in this step's work: it is
   false at the exact `≈ₚ` `watched` demands, because a simulator's
   initialization prefixes the extraction context's observation.
2. **The `at`-style pin on `uc-audit-carryᵈ-bound`** (§2): a measured perf
   defect at 690 s / 8.75 GiB, declined per rule 31. The ledger's own re-route
   is the check that matters and is free.
3. **Nothing here touches the nontrivial grade.** `uc-audit-carryᵈ` is stated at
   `𝟘ᴳ`, as `uc-audit-carry` is; plan §4.4 remains where
   `docs/direct-extraction.md` left it.
4. **`≤UC^ωᵉ⇒≤UC^ωⁿ-blind`** (`docs/ledger-lift-eps.md` §5) is untouched, and
   nothing here changes what it is blocked on.

## 8. The parked maintainer calls

One line each on whether this step changes their calculus.

* **Reroute `ledger-uc-to-pov` through the family theorem?** — unchanged.
  `ledger-uc-to-pov`'s proof is untouched, so `UC.Asymptotic.uc-agree` keeps
  exactly the importer the parked note is about.
* **Shed `uc-audit-bounded`'s unused premises (`ASTotal`, the `bad`-budget
  law)?** — **the case is now stronger on one side and unchanged on the other.**
  After item 1 the whole family route consumes neither: `uc-audit-boundedᵖ`
  passes both to `uc-audit-bounded′`, which discards them. But the premises are
  part of `uc-audit-bounded`'s interface *and of `uc-audit-boundedᵖ`'s*, and
  `ledger-uc-to-pov-simCost` derives the `ASTotal` from `TotalRun` in order to
  supply it; dropping them would change three exported statements, which this
  step may not do. Nothing here forces the call either way.
* **A fifth `Allowance-mono` component of `_≤UC^ωᵉ_`?** — unchanged. No
  statement here mentions `_≤UC^ωᵉ_`. (Resolved 2026-09-21 by deleting
  `Allowance-mono`; see `docs/quantitative-family.md` §10.)
* **Retire `≤UC⇒≤UCᶜ`?** — unchanged in kind, but one consumer fewer is now in
  sight: `UC.Robust.Model.uc-preservesᵒ`'s detour is what the plan §5 row is
  about, and `robust-sub` — the proof that detour ends in — is now a call to
  `tv₁-∘` rather than an inline slide. The detour itself is untouched.
