# RO-model commitment: the hiding / equivocation half

Branch `fcom-hiding`, off `protocol-rewrite` at `96946499`; continued on
`hiding-defer`, off `protocol-rewrite` at `5aaf0a77`, which closes the
deferred-sampling hop this document used to state as a residual.

The same hash-based commitment — `c = H(b ∷ r)` to commit, `(b , r)` to open —
against a **corrupted receiver**. The committer is honest and takes its bit
from the environment; the receiver's view (the commitment, the opening, its
oracle queries) is the adversary interface. The simulator must publish a
commitment **before** it knows the bit and open it to whatever `F_com` later
releases: equivocation, by PROGRAMMING one point of the oracle.

Everything below is a checked term unless it is in "Not delivered"; hatches in
`src/` stay at their baseline of zero (16 grep hits, all of them the words
"postulate-free" in inherited comments, before and after).

## The correction this document owes the brief

The brief asks for two hops — (i) real ≈ lazy-real by a deferred-sampling
bisimulation, **exact**, then (ii) lazy-real ≈ simulated-ideal off a flag
bounded by `rare-cert`. Hop (ii) is delivered in full. **Hop (i) is not exact,
and cannot be** — it is an ε-hop of its own, and that is what
`Hiding/Defer.agda` proves. The counterexample is two queries and three lines:

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
comparisons the flag is made of. `docs/ro-game-hop.md`'s own sentence names the
route taken: a fixed secret must "either re-derive the bound by averaging over
`r` at the top (a different lemma, not a `SuperCert`) **or** hop first to the
lazy game", and the second horn is unavailable here, because the hop to the
lazy game is itself an ε-hop with the same fixed-secret flag. So it is the
FIRST horn that `Hiding/Defer.agda` walks, and the "different lemma" is
`GamePlaying.Average.badProb-avg`.

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

The three kernels are in `Examples/ROCommitment/Hiding/Game.agda`; the fourth,
`respPʰ` — the deferred game with the opening randomness PLANTED and a flag —
is in `Examples/ROCommitment/Hiding/Defer.agda`.

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
* **Hop (i) — `defer-hiding`.** `respLʰ` against `respRʰ`, at `2m·2⁻ᵏ`.
  Neither a bisimulation (see the correction above) nor a `SuperCert` (the
  flag reads the plant); the three moves it is made of are in
  "The deferred-sampling hop" below.

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

`Examples/ROCommitment/Hiding/Defer.agda:defer-hiding` is the other hop, and
`Game.agda:hiding-bound-defer` — the assembled statement, which used to take
its `ε′` as a hypothesis — is now applied to it:

```agda
defer-hiding : (m : ℕ) (d : Strat Qʰ Rʰ) → asks≤ m d
             → ∣ Pr₁ (runWith respLʰ sL₀ d) -ℚ Pr₁ (runWith respRʰ sR₀ d) ∣ℚ
               ≤ℚ fromℕ (m + m) *ℚ inv-pow-2 k

hiding-bound-total : (m : ℕ) (d : Strat Qʰ Rʰ) → asks≤ m d
                   → ∣ Pr₁ (runWith respIʰ sI₀ d) -ℚ Pr₁ (runWith respRʰ sR₀ d) ∣ℚ
                     ≤ℚ εᴸ m +ℚ fromℕ (m + m) *ℚ inv-pow-2 k
hiding-bound-total = hiding-bound-defer defer-hiding
```

i.e. **`3m·2⁻ᵏ`** end to end, against the protocol that draws its opening
randomness at the commitment: `m` guesses at the programming point, `m`
guesses at the plant, `m` fresh tests. `hiding-bound-defer` itself is
unchanged — it is still the general assembly, now with an argument.

`Hiding/Asymptotic.agda:εᵗ-negligible` proves `NegligibleBound εᵗ` for
`εᵗ n q = (q + (q + q))·2⁻ⁿ` (one `fromℕ-+`, one `poly-+`), and
`hiding-boundᵗ` is `hiding-bound-total` at every `n`.

`Examples/ROCommitment/Hiding/Test.agda` instantiates all three at `k = 3`
against live attacks: `bounded`/`bounded-total` at the three-activation attack
— commit, query the oracle at a guessed opening point *before* the opening,
report whether that query came back with the published digest — and
`bounded-preq` at a second, two-activation one that queries the point the
committer is about to hash BEFORE it commits and compares the published digest
with the answer it already holds. That is the commitment-time divergence, the
one event of the two that the first attack does not reach.

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
family, where `E-const` collapses the average the draw has just created. Three
instances are delivered: `GamePlaying/Test.agda:DeferMachine.defer`, the
smallest kernel the statement is about (a secret point, queries that do not
look at it, one designated query that does), `Hiding/Game.agda:defer-commit`,
the real commitment game's own draw moved to the start of the run, and
`Hiding/Defer.agda:defer-hop`, the deferred game's opening draw moved the same
way.

## The deferred-sampling hop: how hop (i) closes

Three moves, in `Examples/ROCommitment/Hiding/Defer.agda`.

**(a) Plant on both sides.** `Game.defer-commit` and `Defer.defer-hop` are two
`runWith-avg` instances saying that each game, averaged over a secret planted
at the start, is that game drawing the secret where it does. The deferred
game's relation has the extra freedom the real one's does not need: the flag
the coupling hangs on the state is allowed to depend on the plant, so the
family is "one deferring state with an arbitrary flag family on it", and only
past the OPENING — the first answer that depends on the plant, and the point
where the two averages merge — does it have to be constant.

**(b) One coupling per plant, up to the flag.** `join-J` is a
`GamePlaying.Hop.JoinStep`: at each related pair of states it exhibits a joint
draw whose two marginals are the planted deferred kernel and the planted real
kernel, and whose every outcome has either stayed related with the same answer
or raised the flag. `Hop.runWith-join` — the new general lemma — turns that
into `|Pr − Pr| ≤ badProb`. It is `Coupling.FLGP` **without the coupled
state**: the two games' tables part company at the commitment (the real game
files `H(b ∷ r)` there, the deferred game only at the opening), and after the
flag is up they part arbitrarily, so a single coupled state would have to
carry both. The relation carries the correspondence instead — `TblAt` says the
real table is the deferred one patched at the commitment's own point, `recOf`
says the records agree, `Fresh` says no tabulated point names the plant — and
carries nothing at all once the flag is up.

**(c) The flag bounded in its AVERAGE.** `GamePlaying.Average.badProb-avg`.
At any single plant the next query hits it with probability 1, so
`Potential.rare-cert` does not apply; over the plant it hits with probability
`2⁻ᵏ`. Two things make that induction go through. `endProb` — the probability
the flag is up at the END of the run, equal to `badProb` for a monotone flag
(`badProb≡endProb`) — has no per-step case split on the flag, so the average
never has to be split inside the integral, which is the obstruction this
document used to record. And `Frozen`: after the opening the plant is public,
the adversary's queries depend on it and the one strategy the induction chases
at every plant at once no longer exists — but nothing can rise there either,
so `endProb-frozen` reads off the flag whatever the adversary does. The
consumer owes `AvgDrift`, one query's averaged drift in continuation-passing
form — the same shape `Defer.AvgBisim` states an averaged bisimulation in.

**The two divergences, as verified against the kernels.** (i) An oracle query
naming the committed point while a commitment is outstanding: `respRʰ` answers
it from its table with the published digest, `respLʰ` draws. (ii) The
COMMITMENT step when the adversary pre-queried `H(b ∷ r)`: `respRʰ` publishes
the tabulated digest, `respLʰ` a fresh one. The flag as built covers both with
ONE `2⁻ᵏ`, not two: it rises at every pre-opening query whose tail is the
plant, which is exactly what (ii) needs to have happened earlier — that is
`Fresh`, and it is why the constant is 2 and not 3. The second `2⁻ᵏ` pays for
the deferred game's own spurious hit (`hitAt` firing at a point that is not
the committed one), which is a divergence in the other direction. There is no
third: after the opening the two tables answer alike at every point and
`hitAt` is dead, which is what `Opened` records.

## Reused verbatim, generalized, new

| piece | status |
|---|---|
| `Examples.ROCommitment`'s `Resᴵ`, `ResQ`, `ResA` | **verbatim, not redefined** (imported) |
| `Examples.ROCommitment.Extraction`'s `Pt`, `Dig`, `Tbl`, `lookupPt` | verbatim, `+ lookup-there` beside `lookup-here` |
| `Examples.ROCommitment.Oracle`'s `fetchT` | verbatim, `+ fetchT-hit`/`fetchT-miss`/`fetchT-sup` |
| `GamePlaying.Coupling.FLGP`, `badProb-bounded` | verbatim, through `hop-bound` |
| `GamePlaying.Hop.runWith-bisim`, `hop-bound` | verbatim, two `StepBisim` instances |
| `Potential.rare-cert`, `RareRaise`, `guess-drift` | verbatim |
| `Approximate.Decay.negligibleBound-inv-pow-2` | verbatim |
| `UC.QueryBound.Certified`, `certified⇒QB` | verbatim |
| `UC.Model.Seal.gradedᵒ`/`procᵒ` | verbatim |
| `ProbabilisticLogic.Dp.Coin.coinₚ` | verbatim (read-only) |
| **`Expectation.E-swap`** | **new, generic, beside `E-bind`** — Fubini at `Dist-ℚ`, one line over the existing `lookupᴰℚ-swap` |
| **`Expectation.E-cong-on`, `E-bind₂`** | **new, generic** — on-support congruence, and the two-draw step every kernel was expanding by hand |
| **`GamePlaying.Defer`** | **new, generic** — the averaged-run induction |
| **`GamePlaying.Hop.runWith-join`** | **new, generic** — a step-coupling up to the flag, on separate state spaces |
| **`GamePlaying.Average`** | **new, generic** — `endProb`, `badProb≡endProb`, `endProb-frozen`, `badProb-avg` |
| **`GamePlaying.Test.DeferMachine`** | new: `runWith-avg`'s acceptance instance |
| `Examples.ROCommitment.Hiding` | new: the interfaces and the three machines |
| `Examples.ROCommitment.Hiding.Game` | new: the three games, the coupling, the bound |
| `Examples.ROCommitment.Hiding.Defer` | new: the planted deferred game, the per-plant coupling, `defer-hiding`, `hiding-bound-total` |
| `Examples.ROCommitment.Hiding.UC` | new: the images, `Certified 1`, `QB 1` |
| `Examples.ROCommitment.Hiding.Asymptotic` | new: `εʰ`, `εᵗ` and their negligibility |
| `Examples.ROCommitment.Hiding.Test` | new: the acceptance instances |

No pre-existing statement was edited or weakened. `Expectation.agda` gains
three lemmas beside `Pr₁-bind`; `GamePlaying/Test.agda` gains a third machine
beside its two; `Hop.agda` gains `runWith-join` beside `hop-bound`;
`Hiding/Game.agda`'s `ask-redᴸ`/`ask-redᴿ` left its `private` blocks (the hop
importing it reduces the same two kernels) and its four query expansions
collapsed onto `E-bind₂`/`lookupᴰℚ-Dmap`; `Extraction.agda` and `Oracle.agda`
gain the four table/oracle facts the hop needed, each beside the definition it
is about rather than in the hop. Nothing else outside
`Examples/ROCommitment/**` and `GamePlaying/**` was touched.

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
| `…RationalDist.Expectation` (222 → 236) | 236 | 6 s → 5 s | 119 s |
| `GamePlaying.Test` (+75) | 175 | 8 s | 103 s |
| `GamePlaying.Hop` (84 → 175) | 175 | 7 s → 8 s | 103 s |
| **`GamePlaying.Average`** | 172 | 7 s | 103 s |
| `Examples.ROCommitment.Hiding` | 218 | 9 s | 114 s |
| `Examples.ROCommitment.Hiding.Game` (574 → 557) | 557 | 8 s → 6 s | 199 s |
| **`Examples.ROCommitment.Hiding.Defer`** | 788 | 8 s | 257 s |
| `Examples.ROCommitment.Extraction` (128 → 134) | 134 | 6 s | 94 s |
| `Examples.ROCommitment.Oracle` (29 → 59) | 59 | 7 s | 75 s |
| `Examples.ROCommitment.Hiding.UC` | 130 | 10 s | 93 s |
| `Examples.ROCommitment.Hiding.Asymptotic` (41 → 68) | 68 | 7 s → 6 s | 77 s |
| `Examples.ROCommitment.Hiding.Test` (48 → 76) | 76 | 6 s → 7 s | 79 s |

Every `hiding-defer` figure — the last four rows' "after" columns and the two
new modules — is a run whose own log carries exactly one `Checking` line,
forced by deleting the module's `.agdai`; the before/after pairs are on that
same basis, except that reverting `Expectation` for its "before" pulled one
dependency along with `Hop`, `Game` and `Asymptotic` (two `Checking` lines
each, so those three "before" figures are upper bounds). The older rows are
the `fcom-hiding` measurements, whose warm column is CPU rather than wall
because the box was running 20 GiB checks from other branches at the time.
Every figure is far inside its rule-5 budget — the largest, the 788-line
`Defer`, at 8 s against 257 s — so nothing here is a rule-31 defect and
`Defer` does not want splitting.

## Not delivered, precisely

### 1. The UC-level ε-statement

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

with `simQBʰ : QB 1 simulatorʰ` and `εᵗ-negligible : NegligibleBound εᵗ` as the
other two components of the consolidation plan's §3.3 witness form — `εᵗ`
rather than `εʰ` now that the closed statement reaches the protocol itself.
Both of those ARE delivered; the relation is not. Note the grade here is a ONE-query
interface (`AdvQʰ` has a single constructor), so `ctxBudget` enters at `c′ ⊔ 1`
rather than the extraction half's `2`.

### 2. No `≤UC[ c ]`, no `≤UC`

Unchanged from the extraction half: `UC.Seam.Graded.≤UC[]ᵍ` and
`UC.Graded.≤UCᵍ` consume a `Factors`, an exact machine equality, which an
approximate emulation does not have. `simQBʰ` is produced and is the input
`≤UC[]ᵍ` would take.

### 3. No `realʰ ≈ᴹ subᴵ simulatorʰ ∘ idealʰ` — and there must not be

Deliberately absent: the emulation is approximate. `∘-wireᴹ` is *available*
(the ideal functionality is a wire), so the composite reduces to a concrete
machine with a readable state, which is what the closed game models; but the
two are not `≈ᴹ` and the branch claims no such thing.

### 4. No family over `k`

`Hiding.Asymptotic.hiding-boundⁿ`/`hiding-boundᵗ` quantify over the security
parameter, so the levelwise statement is there. The FAMILY packaging (`UC.Asymptotic.Family`)
is the `quantitative-family` sibling's and is untouched.

## Against the consolidation plan's architectural decisions

* **Decision 1** — no new relation on top of `_≈ᵁ_`/`_≤UC_`; the ε lives in
  `GamePlaying`.
* **Decision 2** — the only absorption is `sub simʰᵒ ∘ idealʰᵒ`, the presheaf's
  own action.
* **Decision 3** — no `Simulator`, `ClosingContext`, `MonitoredExperiment` or
  `Monitor` record and no new category. The simulator is a plain
  `Proc Lkᴵʰ Advᴵʰ`; the only record inhabited is `GamePlaying`'s existing
  `SuperCert`, via `rare-cert`, and the hop's own obligations (`JoinStep`,
  `AvgDrift`) are plain Σ- and Π-types in `GamePlaying`.
* **Decision 4** — `Strat` untouched; `Test`'s attack is ordinary finite syntax.
* **Decision 5** — the query certificate stays standalone and the quantitative
  witness (`εʰ-negligible`) is kept beside it rather than folded in.
* **Decision 6** — no observation was added or changed.
