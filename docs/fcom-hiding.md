# RO-model commitment: the hiding / equivocation half

Branch `fcom-hiding`, off `protocol-rewrite` at `96946499`.

The same hash-based commitment — `c = H(b ∷ r)` to commit, `(b , r)` to open —
against a **corrupted receiver**. The committer is honest and takes its bit
from the environment; the receiver's view (the commitment, the opening, its
oracle queries) is the adversary interface. The simulator must publish a
commitment **before** it knows the bit and open it to whatever `F_com` later
releases: equivocation, by PROGRAMMING one point of the oracle.

Everything below is a checked term unless it is in "Not delivered"; hatches in
`src/` stay at their baseline of zero (16 grep hits, all of them the words
"postulate-free" in inherited comments, before and after).

## The correction this branch owes the brief

The brief asks for two hops — (i) real ≈ lazy-real by a deferred-sampling
bisimulation, **exact**, then (ii) lazy-real ≈ simulated-ideal off a flag
bounded by `rare-cert`. Hop (ii) is delivered in full. **Hop (i) is not exact,
and cannot be.** The counterexample is two queries and three lines:

> Let the adversary commit to `b` and then query two DISTINCT points
> `b ∷ ρ₁ ≠ b ∷ ρ₂`. In the real game a single `r` is drawn, so at most one of
> the two queries can name the committed point: the event "both queries were
> answered with the published digest" has probability `0`. In a lazy game whose
> per-query test is a FRESH uniform draw — the only shape `Potential.rare-cert`
> can bound, because `RareRaise` asks for a per-query drift and a secret already
> in the state is hit with probability 1 (`docs/ro-game-hop.md`) — the two tests
> are independent and that event has probability `2⁻²ᵏ`. The adversary sees the
> digest, so it can test for exactly this.

So the two games are *identical-until-bad*, not equal: deferring a secret is
exact only while the secret is **unread**, and this one is read — by the very
comparisons the flag is made of. `docs/ro-game-hop.md`'s own sentence is the
accurate one: a fixed secret must "either re-derive the bound by averaging over
`r` at the top (a different lemma, not a `SuperCert`) **or** hop first to the
lazy game" — and the second horn is unavailable here, because the hop to the
lazy game is itself an ε-hop with the same fixed-secret flag.

What the branch therefore delivers is: the ε-hop that IS in reach
(`hiding-bound`), the general deferred-sampling engine that the averaging route
needs (`GamePlaying.Defer.runWith-avg`), and `hiding-bound-defer` — a proved
theorem turning the missing identification into the full statement, with the
gap stated as one typed hypothesis rather than as a postulate.

## Where `F_com`'s memory lives — the same cell, the other side of it

**Decision: unchanged.** The ideal functionality is again a `wireᴹ` over
`Examples.ROCommitment`'s `Resᴵ` — the same lazily sampled oracle and the same
one-shot cell, not redefined. Only the relabelling changes, because the honest
party changed sides:

| `Resᴵ` | extraction half | hiding half |
|---|---|---|
| `putᴿ b` | the simulator commits the extracted bit | the ENVIRONMENT's `commitᴱ b`, through the honest committer's port |
| `rcptᴿ` | up to the honest receiver | up to the SIMULATOR (`rcptᶠ`): the receipt a corrupt receiver gets |
| `getᴿ` / `outᴿ b` | the simulator releases; up to the receiver | the environment's `openᴱ`; the bit goes up to the SIMULATOR (`bitᶠ b`) |
| `hashᴿ` / `digᴿ` | the receiver's relay of adversary queries | the simulator's relay of receiver queries |
| `rejᴿ` | the simulator's refusal (`nakᴿ`) | up to the environment (`nakᴱ`) |

`Examples/ROCommitment/Hiding.agda:downᶠʰ`/`upᶠʰ` are total functions and
`idealʰ = wireᴹ upᶠʰ downᶠʰ`, so **yes, the placement allows the ideal
functionality to be a wire** and `UC.Machine.Wire.∘-wireᴹ` is available for
`subᴵ simulatorʰ ∘ idealʰ` exactly as `docs/hash-forward.md` §"The one
structural fact that makes it affordable" requires. The asymmetry the decision
costs is the mirror image of the extraction half's: there the real protocol
emitted its own receipt, here the real committer emits its own refusal.

## The programming decision

**Programming is an INTERCEPTION, not a second oracle.** The simulator relays
every adversary oracle query down to `Resᴵ`'s oracle — the one oracle in either
world — *except* the single point it has programmed, which it answers from its
own three-field record (`Progʰ`: blank, the published digest, the published
digest with its point). Concretely `Hiding.agda:serveʰ` / `pinnedʰ`.

Why not the alternative — the simulator keeping its own lazily sampled table
and never relaying:

* It would move the oracle into the simulator, so the ideal world would have a
  second, disjoint oracle while the resource's own sat unused. The wire
  placement is then a lie about where the randomness is.
* It would make the simulator's state unbounded in the adversary's query count,
  which is exactly what the query certificate is supposed to rule out.
* It buys nothing: a relayed point and a freshly sampled point have the same
  distribution, and the two worlds' tables stay identical step for step — which
  is what keeps both `StepBisim` instances one case analysis each, the same
  reason the extraction half queries at the opening
  (`docs/fcom-extraction.md` §"Exact query accounting").

The simulator's own state therefore suffices, and it is finite: `c*`, the
programmed point `b ∷ r`, and whether a relay is in flight. Stateful simulators
were already accepted in the extraction half; this one is smaller.

## The two hops

The three kernels are in `Examples/ROCommitment/Hiding/Game.agda`.

| kernel | state | the opening randomness |
|---|---|---|
| `respRʰ` | `Maybe Dig × Tbl × Maybe (Dig × Bool × Dig × Bool)` | drawn at the commitment (or already planted — see `defer-commit`), kept |
| `respLʰ` | `Tbl × Maybe (Dig × Bool × Bool)` | deferred: drawn afresh at each query as a TEST, and once at the opening |
| `respIʰ` | the same | drawn at the opening only, where the point is programmed |

`respLʰ` and `respIʰ` agree everywhere except at one clause: an oracle query,
while a commitment is outstanding, whose point the fresh draw says is the
committed one. `respLʰ` then answers the published digest (what the real
committer's own table entry answers); `respIʰ` answers the table. The
commitment step and the opening step are literally shared between them.

Two things about `respLʰ` a reader will ask, both confined to the bad event and
both deliberate. (1) On a hit it answers the published digest but does **not**
file `(x , c)` in the table, so a *repeated* query at that point redraws and
probably misses — `respLʰ` is a consistent oracle only off its own flag, which
is all `FLGP` uses. (2) At the opening both games PREPEND `(b ∷ r , c)`, so if
that point had already been queried the new entry shadows the old one: the
programming conflict, and the flag that pays for it is already up.

* **Hop (ii) — `hiding-bound`.** The coupling `respBʰ` emits both answers, the
  flag is `f ∨ hitAt m x ρ`, `agree-off` is not needed (the two answers
  coincide as soon as the flag is down, by `cond`), and both marginals are
  identified by `Hop.runWith-bisim` with the relation "erase the flag" — **no
  invariant**, unlike the extraction half. `Potential.rare-cert` at
  `ε ≡ 2⁻ᵏ`, its hypothesis discharged by `Potential.guess-drift`, gives
  `m·2⁻ᵏ`; `Hop.hop-bound` assembles. One flag, so no `∨-cert`.
* **Hop (i) — the residual.** `respLʰ` against `respRʰ`; see the correction
  above.

## The bound proved

`Examples/ROCommitment/Hiding/Game.agda:hiding-bound`:

```agda
hiding-bound : (m : ℕ) (d : Strat Qʰ Rʰ) → asks≤ m d
             → ∣ Pr₁ (runWith respIʰ sI₀ d) -ℚ Pr₁ (runWith respLʰ sL₀ d) ∣ℚ ≤ℚ εᴸ m
  where εᴸ m = fromℕ m *ℚ inv-pow-2 k
```

i.e. **`m·2⁻ᵏ`** for every adaptive adversary of at most `m` activations, at
either world's own initial state — `(m² + m)·2⁻ᵏ` cheaper than the extraction
half, because hiding has no birthday flag: the simulator never has to read a
preimage out of a table, so a collision in the answer log costs it nothing.

`Hiding/Asymptotic.agda:εʰ-negligible` proves `NegligibleBound εʰ` for
`εʰ n q = q·2⁻ⁿ` at the identity schedule, and `hiding-boundⁿ` quantifies the
bound over `n`.

`Examples/ROCommitment/Hiding/Game.agda:hiding-bound-defer` is the assembled
statement:

```agda
hiding-bound-defer : {ε′ : ℕ → ℚ}
  → ((m : ℕ) (d : Strat Qʰ Rʰ) → asks≤ m d
     → ∣ Pr₁ (runWith respLʰ sL₀ d) -ℚ Pr₁ (runWith respRʰ sR₀ d) ∣ℚ ≤ℚ ε′ m)
  → (m : ℕ) (d : Strat Qʰ Rʰ) → asks≤ m d
  → ∣ Pr₁ (runWith respIʰ sI₀ d) -ℚ Pr₁ (runWith respRʰ sR₀ d) ∣ℚ ≤ℚ εᴸ m +ℚ ε′ m
```

`Examples/ROCommitment/Hiding/Test.agda:bounded` instantiates `hiding-bound` at
`k = 3` against a live adaptive three-activation attack — commit, query the
oracle at a guessed opening point *before* the opening, report whether that
query came back with the published digest — which is precisely the observation
the two games disagree on.

## The deferred-sampling lemma: the exact generality reached

`CategoricalCrypto/GamePlaying/Defer.agda`:

```agda
module _ {Q R V StE StL : Type} (μ : Dist-ℚ V)
         (resp : StE → Q → Dist-ℚ (StE × R)) (resp′ : StL → Q → Dist-ℚ (StL × R))
         (_≋_ : (V → StE) → StL → Type) where

  AvgBisim : Type
  AvgBisim = ∀ f s → f ≋ s → ∀ q (F : StE × R → ℚ) (F′ : StL × R → ℚ)
           → (∀ (g : V → StE × R) t → (λ v → proj₁ (g v)) ≋ proj₁ t
              → (∀ v → proj₂ (g v) ≡ proj₂ t) → E μ (λ v → F (g v)) ≡ F′ t)
           → E μ (λ v → E (resp (f v) q) F) ≡ E (resp′ s q) F′

  runWith-avg : AvgBisim → ∀ d f s → f ≋ s
              → E μ (λ v → Pr₁ (runWith resp (f v) d)) ≡ Pr₁ (runWith resp′ s d)
```

**Exact generality.** It is `Hop.runWith-bisim` with an average in front of one
side: the planted kernel runs at a FAMILY of states indexed by the secret, the
deferring kernel at a single state, and one query's agreement propagates to
every adaptive distinguisher. The consumer owes one query's statement; the
lemma carries the induction. The `coin` case is Fubini and nothing else, which
is why the branch adds `Expectation.E-swap` (`lookupᴰℚ-swap`, which already
existed, read at `Dist-ℚ`).

**What it does NOT assume.** No shape on the state, no `plant`, no
"designated step" predicate, no monotone flag. The relation `_≋_` carries all
of that, exactly as `runWith-bisim`'s carries a ghost table. Taking `V ≡ ⊤`,
`μ` the point mass and the family constant recovers `runWith-bisim` verbatim,
so **`MerkleDamgard.Core.ideal-marginal` is an instance of `runWith-avg`'s
`V ≡ ⊤` case** — it was written against `runWith-bisim` and stays written
against it; it is NOT an instance where the average does any work, because MD's
ghost argument moves an entry between two tables at the same step rather than
moving a draw in time. Nothing in `Examples/MerkleDamgard` was edited or
re-derived.

**What it is for.** The statement `docs/fcom-extraction.md` item 2 calls
`defer` — "an unread lazily sampled entry is invisible" — is the instance where
`_≋_` says the family is `λ v → plant v s` before the designated step and
constant after it; the designated step's case is discharged with a CONSTANT
family, where `E-const` collapses the average the draw has just created. Two
instances are delivered: `GamePlaying/Test.agda:DeferMachine.defer`, the
smallest kernel the statement is about (a secret point, queries that do not
look at it, one designated query that does), and
`Hiding/Game.agda:defer-commit`, the real commitment game's own draw moved to
the start of the run.

## Reused verbatim, generalized, new

| piece | status |
|---|---|
| `Examples.ROCommitment`'s `Resᴵ`, `ResQ`, `ResA` | **verbatim, not redefined** (imported) |
| `Examples.ROCommitment.Extraction`'s `Pt`, `Dig`, `Tbl`, `lookupPt` | verbatim |
| `GamePlaying.Coupling.FLGP`, `badProb-bounded` | verbatim, through `hop-bound` |
| `GamePlaying.Hop.runWith-bisim`, `hop-bound` | verbatim, two `StepBisim` instances |
| `Potential.rare-cert`, `RareRaise`, `guess-drift` | verbatim |
| `Approximate.Decay.negligibleBound-inv-pow-2` | verbatim |
| `UC.QueryBound.Certified`, `certified⇒QB` | verbatim |
| `UC.Model.Seal.gradedᵒ`/`procᵒ` | verbatim |
| `ProbabilisticLogic.Dp.Coin.coinₚ` | verbatim (read-only) |
| **`Expectation.E-swap`** | **new, generic, beside `E-bind`** — Fubini at `Dist-ℚ`, one line over the existing `lookupᴰℚ-swap` |
| **`GamePlaying.Defer`** | **new, generic** — the averaged-run induction |
| **`GamePlaying.Test.DeferMachine`** | new: its acceptance instance |
| `Examples.ROCommitment.Hiding` | new: the interfaces and the three machines |
| `Examples.ROCommitment.Hiding.Game` | new: the three games, the coupling, the bound |
| `Examples.ROCommitment.Hiding.UC` | new: the images, `Certified 1`, `QB 1` |
| `Examples.ROCommitment.Hiding.Asymptotic` | new: `εʰ` and its negligibility |
| `Examples.ROCommitment.Hiding.Test` | new: the acceptance instance |

No pre-existing statement was edited or weakened. `Expectation.agda` gains
`E-swap` beside `Pr₁-bind`; `GamePlaying/Test.agda` gains a third machine
beside its two; nothing else outside `Examples/ROCommitment/Hiding/**` and
`GamePlaying/Defer.agda` was touched.

## Query accounting

`Examples/ROCommitment/Hiding/UC.agda`:

| statement | content |
|---|---|
| `simCertʰ : Certified 1 simulatorʰ` | potential constantly `0`: one downward message per activation from above, none at all from below |
| `simQBʰ : QB 1 simulatorʰ` | the same, crossed to the model |

**The exact ledger does not fit, and the reason is the programming.**
`UC.QueryBound.Exact` weighs an activation by a function of the LETTER alone
(`points`, `perMessage` in the extraction half). Here whether an adversary
query costs a downward relay depends on whether its point is the programmed
one — a fact about the STATE, not about the letter. The exact count is
`#queries − #(queries at the programmed point)` and no `Exact` weighting
expresses it, so `Certified 1` is the sharpest statement of this shape. The
extraction half's `simExactHash`/`simExactAll` have no analogue here; that is
a genuine difference between an extracting and a programming simulator, not an
omission.

## Modules

All checked with `pagda --useUntracked false check … -- +RTS -M8G -H1G -RTS`,
rc=0 and an empty
`ModuleDoesntExport|UselessPublic|UselessPrivate|DuplicateUsing|error:|Failed to solve|Heap exhausted`
gate.

| module | LOC | warm | rule-5 budget |
|---|---|---|---|
| `GamePlaying.Defer` | 67 | 8 s | 76 s |
| `…RationalDist.Expectation` (+7) | 163 | 7 s | 100 s |
| `GamePlaying.Test` (+75) | 175 | 8 s | 103 s |
| `Examples.ROCommitment.Hiding` | 218 | 9 s | 114 s |
| `Examples.ROCommitment.Hiding.Game` | 581 | 9 s | 205 s |
| `Examples.ROCommitment.Hiding.UC` | 130 | 10 s | 93 s |
| `Examples.ROCommitment.Hiding.Asymptotic` | 41 | 9 s | 70 s |
| `Examples.ROCommitment.Hiding.Test` | 48 | 10 s | 72 s |

The warm column is CPU, not wall: the box ran several 20 GiB checks from other
branches throughout, so wall time here is dominated by the shared memory gate
and says nothing about a module — one 9 s check waited 527 s for a slot. The
five `Hiding*` figures are runs whose log carries the module's own `Checking`
line; the three lower ones are the same modules read at their sharpest
available measurement. Every figure is far inside its rule-5 budget, the
largest being the 581-line `Game` at 9 s against 205 s, so nothing here is a
rule-31 defect.

## Not delivered, precisely

### 1. The deferred-sampling step for THIS game — the ε′ of `hiding-bound-defer`

```agda
defer-hiding : (m : ℕ) (d : Strat Qʰ Rʰ) → asks≤ m d
             → ∣ Pr₁ (runWith respLʰ sL₀ d) -ℚ Pr₁ (runWith respRʰ sR₀ d) ∣ℚ
               ≤ℚ fromℕ (m + m) *ℚ inv-pow-2 k
```

`2m·2⁻ᵏ` because the two games part in two places, not one: a query that names
the committed point (`m` of them, `2⁻ᵏ` each) and the COMMITMENT itself, where
`respRʰ` reads `H(b ∷ r)` out of the table if the adversary pre-queried it while
`respLʰ` always draws fresh (one event, mass `|t|·2⁻ᵏ ≤ m·2⁻ᵏ`). Feeding it to
`hiding-bound-defer` gives `3m·2⁻ᵏ` for the whole statement — still `q·2⁻ᵏ` in
shape, so `Hiding.Asymptotic.εʰ-negligible` covers it after one `fromℕ-+`.

Not a bisimulation (see the correction at the top), so `runWith-avg` alone does
not close it. What closes it is the averaging route, in three pieces, none of
which exists yet:

```agda
-- (a) DELIVERED — `Hiding/Game.agda:defer-commit`.  The real game with the
--     secret planted at the start, averaged over the plant, IS the real game
--     drawing at the commitment.  An instance of `runWith-avg` at the relation
--     "pre-commitment: the family is `λ r → (just r , t , nothing)` and the
--     state is `(nothing , t , nothing)`; post-commitment: the family is
--     constant".
defer-commit : (d : Strat Qʰ Rʰ)
             → E (uniform-Vec k) (λ r → Pr₁ (runWith respRʰ (just r , [] , nothing) d))
               ≡ Pr₁ (runWith respRʰ sR₀ d)

-- (b) the AVERAGED supermartingale: a flag that reads a planted secret is not
--     a `SuperCert` at any single plant, but its μ-average is bounded.  This is
--     the "different lemma, not a `SuperCert`" of `docs/ro-game-hop.md`.
badProb-avg : (μ : Dist-ℚ V) (resp : V → St → Q → Dist-ℚ (St × R)) (bad : V → St → Bool)
              (φ : ℕ → St → ℚ) → …
            → ∀ m d s → asks≤ m d → E μ (λ v → badProb (resp v) (bad v) s d) ≤ℚ φ m s

-- (c) the averaged FLGP: `E-abs-diff` over `μ` in front of `Coupling.FLGP`.
```

With (a) in hand the remaining work is (b) and (c) only. (b) is the
substantive one and it is not a one-liner: `badProb-super`'s
induction is stated at a single state, and averaging makes the post-state a
FAMILY, so the potential has to be a functional of the family rather than of a
state. The shape that works is the one `runWith-avg` already uses (`E μ` in
front, a family on the planted side); the obstruction is that `badProb`'s own
recursion branches on `bad v s`, which differs across `v`, so the split has to
be done inside the integral. A cheaper route worth spiking first: show
`badProb` of a MONOTONE flag equals the probability that the flag is up at the
END of the run (a new `runSt` and one induction), after which (b) is an
ordinary `E`-linear supermartingale on the rational potential `E μ (1[bad v ·])`
and needs no family at all.

### 2. The UC-level ε-statement

The same four obstructions as the extraction half — `docs/fcom-extraction.md`
§"Not delivered" 1(a)–(d) — verbatim, since they are about the layer and not
about which party is corrupt. The `graded-bridge` sibling is building
`plug-runᵍ`, `adequacyᵍ` and `closed-kernel` for the extraction side; this
side's statement instantiates the SAME three at `Advᴵʰ`/`Honᴵʰ`/`Lkᴵʰ` and
needs nothing further of them:

```agda
raw-emulationʰ :
    (W : Channel)
    (Et : T₀ W (T₀ (ifaceᵒ Advᴵʰ) (ifaceᵒ Honᴵʰ)) ⇒ Ωᵒ)
    (m  : 𝟘ᵒ ⇒ T₀ W (ifaceᵒ Resᴵ))
    {c c′ : ℕ} → QB c Et → QB c′ m
  → Obs ((Et ∘ T₁ᵒ W realʰᵒ) ∘ m)
    ≈ₚ[ εʰ k (ctxBudget c c′) ]
    Obs ((Et ∘ T₁ᵒ W (sub simʰᵒ ∘ idealʰᵒ)) ∘ m)
```

with `simQBʰ : QB 1 simulatorʰ` and `εʰ-negligible : NegligibleBound εʰ` as the
other two components of the consolidation plan's §3.3 witness form. Both of
those ARE delivered; the relation is not. Note the grade here is a ONE-query
interface (`AdvQʰ` has a single constructor), so `ctxBudget` enters at `c′ ⊔ 1`
rather than the extraction half's `2`.

### 3. No `≤UC[ c ]`, no `≤UC`

Unchanged from the extraction half: `UC.Seam.Graded.≤UC[]ᵍ` and
`UC.Graded.≤UCᵍ` consume a `Factors`, an exact machine equality, which an
approximate emulation does not have. `simQBʰ` is produced and is the input
`≤UC[]ᵍ` would take.

### 4. No `realʰ ≈ᴹ subᴵ simulatorʰ ∘ idealʰ` — and there must not be

Deliberately absent: the emulation is approximate. `∘-wireᴹ` is *available*
(the ideal functionality is a wire), so the composite reduces to a concrete
machine with a readable state, which is what the closed game models; but the
two are not `≈ᴹ` and the branch claims no such thing.

### 5. No family over `k`

`Hiding.Asymptotic.hiding-boundⁿ` quantifies over the security parameter, so
the levelwise statement is there. The FAMILY packaging (`UC.Asymptotic.Family`)
is the `quantitative-family` sibling's and is untouched.

## Against the consolidation plan's architectural decisions

* **Decision 1** — no new relation on top of `_≈ᵁ_`/`_≤UC_`; the ε lives in
  `GamePlaying`.
* **Decision 2** — the only absorption is `sub simʰᵒ ∘ idealʰᵒ`, the presheaf's
  own action.
* **Decision 3** — no `Simulator`, `ClosingContext`, `MonitoredExperiment` or
  `Monitor` record and no new category. The simulator is a plain
  `Proc Lkᴵʰ Advᴵʰ`; the only new record inhabited is `GamePlaying`'s existing
  `SuperCert`, via `rare-cert`.
* **Decision 4** — `Strat` untouched; `Test`'s attack is ordinary finite syntax.
* **Decision 5** — the query certificate stays standalone and the quantitative
  witness (`εʰ-negligible`) is kept beside it rather than folded in.
* **Decision 6** — no observation was added or changed.
