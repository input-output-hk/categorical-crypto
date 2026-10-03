# RO-model commitment: the hiding / equivocation half

The same hash-based commitment — `c = H(b ∷ r)` to commit, `(b , r)` to open —
against a **corrupted receiver**. The committer is honest and takes its bit
from the environment; the receiver's view (the commitment, the opening, its
oracle queries) is the adversary interface. The simulator must publish a
commitment **before** it knows the bit and open it to whatever `F_com` later
releases: equivocation, by PROGRAMMING one point of the oracle. Modules:
`Examples.ROCommitment.Hiding` (interfaces and machines), `.Hiding.Game`,
`.Hiding.Defer`, `.Hiding.UC`, `.Hiding.Asymptotic`, `.Hiding.Test`, over the
generic `GamePlaying.Defer`, `GamePlaying.Average` and `GamePlaying.Hop`.

## Why hop (i) is an ε-hop, not a bisimulation

The obvious plan is two hops — (i) real ≈ lazy-real by a deferred-sampling
bisimulation, **exact**, then (ii) lazy-real ≈ simulated-ideal off a flag
bounded by `rare-cert`. **Hop (i) is not exact, and cannot be.** The
counterexample is two queries:

> Let the adversary commit to `b` and then query two DISTINCT points
> `b ∷ ρ₁ ≠ b ∷ ρ₂`. In the real game a single `r` is drawn, so at most one of
> the two queries can name the committed point: the event "both queries were
> answered with the published digest" has probability `0`. In a lazy game whose
> per-query test is a FRESH uniform draw — the only shape `Potential.rare-cert`
> can bound, because `RareRaise` asks for a per-query drift and a secret already
> in the state is hit with probability 1 — the two tests are independent and
> that event has probability `2⁻²ᵏ`. The adversary sees the digest, so it can
> test for exactly this.

So the two games are *identical-until-bad*, not equal: deferring a secret is
exact only while the secret is **unread**, and this one is read — by the very
comparisons the flag is made of. A fixed secret leaves two routes: hop first to
a lazy game, or re-derive the bound by averaging over `r` at the top (a
different lemma, not a `SuperCert`). The first is unavailable here, because the
hop to the lazy game is itself an ε-hop with the same fixed-secret flag, so
`Hiding.Defer` takes the second, and the different lemma is
`GamePlaying.Average.badProb-avg`.

## Where `F_com`'s memory lives — the same cell, the other side of it

The ideal functionality is again a `wireᴹ` over `Examples.ROCommitment`'s
`Resᴵ` — the same lazily sampled oracle and the same one-shot cell, not
redefined ([`docs/fcom-extraction.md`](fcom-extraction.md) §"Where `F_com`'s
memory lives"). Only the relabelling changes, because the honest party changed
sides:

| `Resᴵ` | extraction half | hiding half |
|---|---|---|
| `putᴿ b` | the simulator commits the extracted bit | the ENVIRONMENT's `commitᴱ b`, through the honest committer's port |
| `rcptᴿ` | up to the honest receiver | up to the SIMULATOR (`rcptᶠ`): the receipt a corrupt receiver gets |
| `getᴿ` / `outᴿ b` | the simulator releases; up to the receiver | the environment's `openᴱ`; the bit goes up to the SIMULATOR (`bitᶠ b`) |
| `hashᴿ` / `digᴿ` | the receiver's relay of adversary queries | the simulator's relay of receiver queries |
| `rejᴿ` | the simulator's refusal (`nakᴿ`) | up to the environment (`nakᴱ`) |

`Hiding.downᶠʰ`/`upᶠʰ` are total and `idealʰ = wireᴹ upᶠʰ downᶠʰ`, so
`UC.Machine.Wire.∘-wireᴹ` is available for `subᴵ simulatorʰ ∘ idealʰ` exactly
as [`docs/hash-forward.md`](hash-forward.md) §"The one structural fact that
makes it affordable" requires. The asymmetry is the mirror image of the
extraction half's: there the real protocol emitted its own receipt, here the
real committer emits its own refusal.

## The programming decision

**Programming is an INTERCEPTION, not a second oracle.** The simulator relays
every adversary oracle query down to `Resᴵ`'s oracle — the one oracle in either
world — *except* the single point it has programmed, which it answers from its
own record (`Progʰ`: blank, the published digest, the published digest with
its point; `Hiding.serveʰ`/`pinnedʰ`).

Why not a simulator keeping its own lazily sampled table and never relaying:

* the ideal world would have a second, disjoint oracle while the resource's
  own sat unused — the wire placement would then lie about where the
  randomness is;
* the simulator's state would be unbounded in the adversary's query count,
  which is what the query certificate is supposed to rule out;
* it buys nothing: a relayed point and a freshly sampled point have the same
  distribution, and with relaying the two worlds' tables stay identical step
  for step, which keeps both `StepBisim` instances one case analysis each (the
  extraction half queries at the opening for the same reason).

The simulator's state is finite: the published digest, the programmed point
`b ∷ r`, and whether a relay is in flight.

## The kernels and the two hops

| kernel | module | the opening randomness |
|---|---|---|
| `respRʰ` | `Hiding.Game` | drawn at the commitment, kept |
| `respLʰ` | `Hiding.Game` | deferred: drawn afresh at each query as a TEST, and once at the opening |
| `respIʰ` | `Hiding.Game` | drawn at the opening only, where the point is programmed |
| `respPʰ` | `Hiding.Defer` | planted at the start, with a flag |

`respLʰ` and `respIʰ` agree everywhere except at one clause: an oracle query,
while a commitment is outstanding, whose point the fresh draw says is the
committed one. `respLʰ` then answers the published digest (what the real
committer's own table entry answers); `respIʰ` answers the table. The
commitment and opening steps are shared.

Two things about `respLʰ`, both confined to the bad event and both deliberate.
(1) On a hit it answers the published digest but does **not** file `(x , c)` in
the table, so a *repeated* query at that point redraws and probably misses —
`respLʰ` is a consistent oracle only off its own flag, which is all `FLGP`
uses. (2) At the opening both games PREPEND `(b ∷ r , c)`, so if that point had
already been queried the new entry shadows the old one: the programming
conflict, and the flag that pays for it is already up.

* **Hop (ii) — `Hiding.Game.hiding-bound`.** The coupling `respBʰ` emits both
  answers, the flag is `f ∨ hitAt m x ρ`, and both marginals are identified by
  `Hop.runWith-bisim` with the relation "erase the flag" — **no invariant**,
  unlike the extraction half. `Potential.rare-cert` at `ε ≡ 2⁻ᵏ`, discharged by
  `Potential.guess-drift`, gives `m·2⁻ᵏ`. One flag, so no `∨-cert`.
* **Hop (i) — `Hiding.Defer.defer-hiding`.** `respLʰ` against `respRʰ`, at
  `2m·2⁻ᵏ`: neither a bisimulation (above) nor a `SuperCert` (the flag reads
  the plant); see "The deferred-sampling hop".

## The bounds

```agda
hiding-bound : (m : ℕ) (d : Strat Qʰ Rʰ) → asks≤ m d          -- Hiding.Game
             → ∣ Pr₁ (runWith respIʰ sI₀ d) -ℚ Pr₁ (runWith respLʰ sL₀ d) ∣ℚ ≤ℚ εᴸ m
  -- εᴸ m = fromℕ m *ℚ inv-pow-2 k

defer-hiding : (m : ℕ) (d : Strat Qʰ Rʰ) → asks≤ m d          -- Hiding.Defer
             → ∣ Pr₁ (runWith respLʰ sL₀ d) -ℚ Pr₁ (runWith respRʰ sR₀ d) ∣ℚ
               ≤ℚ fromℕ (m + m) *ℚ inv-pow-2 k

hiding-bound-total : (m : ℕ) (d : Strat Qʰ Rʰ) → asks≤ m d    -- Hiding.Defer
                   → ∣ Pr₁ (runWith respIʰ sI₀ d) -ℚ Pr₁ (runWith respRʰ sR₀ d) ∣ℚ
                     ≤ℚ εᴸ m +ℚ fromℕ (m + m) *ℚ inv-pow-2 k
```

`hiding-bound` is **`m·2⁻ᵏ`**, `(m² + m)·2⁻ᵏ` cheaper than the extraction half
because hiding has no birthday flag: the simulator never reads a preimage out
of a table, so a collision in the answer log costs it nothing.
`hiding-bound-total` is the triangle inequality, **`3m·2⁻ᵏ`** end to end
against the protocol that draws its randomness at the commitment: `m` guesses
at the programming point, `m` at the plant, `m` fresh tests.

`Hiding.Asymptotic`: `εᵗ n q = (q + (q + q))·2⁻ⁿ`, with `εᵗ-negligible` and
the levelwise `hiding-boundᵗ`. `Hiding.Test` instantiates
`hiding-boundᵗ` at `k = 5` against live
attacks: `bounded-total` at the three-activation attack — commit,
query a guessed opening point *before* the opening, report whether it came back
with the published digest — and `bounded-preq` at a two-activation one that
queries the point the committer is about to hash BEFORE it commits and compares
the published digest with the answer it holds: the commitment-time divergence,
which the first attack does not reach.

## The deferred-sampling lemma

```agda
-- GamePlaying.Defer
module _ {Q R V StE StL : Type} (μ : Dist-ℚ V)
         (resp : StE → Q → Dist-ℚ (StE × R)) (resp′ : StL → Q → Dist-ℚ (StL × R))
         (_≋_ : (V → StE) → StL → Type) where

  AvgPoint : (StE × R → ℚ) → (StL × R → ℚ) → Type
  AvgPoint F F′ = ∀ (g : V → StE × R) t → (λ v → proj₁ (g v)) ≋ proj₁ t
                → (∀ v → proj₂ (g v) ≡ proj₂ t) → E μ (λ v → F (g v)) ≡ F′ t

  AvgBisim : Type
  AvgBisim = ∀ f s → f ≋ s → ∀ q (F : StE × R → ℚ) (F′ : StL × R → ℚ)
           → AvgPoint F F′ → E μ (λ v → E (resp (f v) q) F) ≡ E (resp′ s q) F′

  runWith-avg : AvgBisim → ∀ d f s → f ≋ s
              → E μ (λ v → Pr₁ (runWith resp (f v) d)) ≡ Pr₁ (runWith resp′ s d)
```

It is `Hop.runWith-bisim` with an average in front of one side: the planted
kernel runs at a FAMILY of states indexed by the secret, the deferring kernel at
one state, and one query's agreement propagates to every adaptive
distinguisher. The `coin` case is Fubini (`Expectation.E-swap`). It assumes no
shape on the state, no `plant`, no designated step and no monotone flag — the
relation `_≋_` carries all of that, as `runWith-bisim`'s carries a ghost table.
At `V ≡ ⊤` it is `runWith-bisim`; `MerkleDamgard.Core.ideal-marginal` is only
an instance of that degenerate case, because MD's ghost argument moves an entry
between two tables at the same step rather than moving a draw in time.

"An unread lazily sampled entry is invisible" is the instance where `_≋_` says
the family is `λ v → plant v s` before the designated step and constant after;
the designated step's case is discharged with a CONSTANT family, where
`E-const` collapses the average the draw has just created. Instances:
`GamePlaying.Test.DeferMachine.defer` (the smallest kernel the statement is
about), `Hiding.Defer.defer-commit` (the real game's draw moved to the start of
the run) and `Hiding.Defer.defer-hop` (the deferred game's opening draw moved
the same way).

## The deferred-sampling hop

Three moves, in `Examples.ROCommitment.Hiding.Defer`.

**(a) Plant on both sides.** `defer-commit` and `defer-hop` are two
`runWith-avg` instances: each game, averaged over a secret planted at the
start, is that game drawing the secret where it does. The deferred game's
relation lets the flag hung on the state depend on the plant, so the family is
"one deferring state with an arbitrary flag family on it", constant only past
the OPENING — the first answer that depends on the plant, where the two
averages merge.

**(b) One coupling per plant, up to the flag.** `join-J` is a
`Hop.JoinStep`: at each related pair of states with the flag down a joint draw whose marginals are
the planted deferred kernel and the planted real kernel, and whose every outcome
either stays related with the same answer or raises the flag.
`Hop.runWith-join` turns that into `|Pr − Pr| ≤ badProb`. It is `FLGP`
**without the coupled state**: the two games' tables part company at the
commitment (the real game files `H(b ∷ r)` there, the deferred game only at the
opening), and after the flag is up they part arbitrarily, so one coupled state
would have to carry both. The relation carries the correspondence instead —
`TblAt` (the real table is the deferred one patched at the commitment's own
point), `recOf` (the records agree), `Fresh` (no tabulated point names the
plant) — and nothing once the flag is up.

**(c) The flag bounded in its AVERAGE — `Average.badProb-avg`.** At any single
plant the next query hits it with probability 1, so `rare-cert` does not apply;
over the plant it hits with probability `2⁻ᵏ`. Two things make the induction go
through. `endProb`, the probability the flag is up at the END of the run (equal
to `badProb` for a monotone flag, `badProb≡endProb`), has no per-step case split
on the flag, so the average never has to be split inside the integral. And
`Frozen`: after the opening the plant is public and the adversary's queries
depend on it, so no single strategy is chased at every plant at once — but
nothing can rise there either, and `endProb-frozen` reads the flag off whatever
the adversary does. The consumer owes `AvgDrift`, one query's averaged drift in
continuation-passing form.

**The two divergences.** (i) An oracle query naming the committed point while a
commitment is outstanding: `respRʰ` answers from its table with the published
digest, `respLʰ` draws. (ii) The COMMITMENT step when the adversary pre-queried
`H(b ∷ r)`: `respRʰ` publishes the tabulated digest, `respLʰ` a fresh one. The
flag covers both with ONE `2⁻ᵏ`: it rises at every pre-opening query whose tail
is the plant, which is exactly what (ii) needs to have happened earlier
(`Fresh`) — that is why the constant is 2 and not 3. The second `2⁻ᵏ` pays for
the deferred game's own spurious hit (`hitAt` firing at a point that is not the
committed one). There is no third: after the opening the two tables answer
alike at every point and `hitAt` is dead (`Opened`).

## Query accounting

`Hiding.UC`: `simCertʰ : Certified 1 simulatorʰ` (potential constantly `0`: one
downward message per activation from above, none from below) and
`simQBʰ : QB 1 simulatorʰ`.

**The exact ledger does not fit, because of the programming.**
`UC.QueryBound.Exact` weighs an activation by a function of the LETTER alone.
Here whether an adversary query costs a relay depends on whether its point is
the programmed one — a fact about the STATE. The exact count is
`#queries − #(queries at the programmed point)` and no `Exact` weighting
expresses it, so `Certified 1` is the sharpest statement of this shape: a
genuine difference between an extracting and a programming simulator.

## Not delivered

**The UC-level ε-statement.** `respRʰ` and `respIʰ` are hand transcriptions of
`realʰ` over the resource and of `F_com` behind `simulatorʰ`; no theorem
connects them to the machines — there is no hiding counterpart of
`Examples.ROCommitment.Realization.{Machine,Bisim,Bound}`. The theorem aimed at
is the resource-installed
`Examples.ROCommitment.Realization.Assembly.Realizationʰ` at `εᵗ`
([`docs/rcom-icom-b1.md`](rcom-icom-b1.md)); `simQBʰ` and `εᵗ-negligible` are
its other two witness components. One difference from the extraction side
matters for that route: `Honᴵʰ = HonAʰ ⇿ HonQʰ` with `HonQʰ` inhabited
(`commitᴱ b`, `openᴱ`), so an environment strategy at `Honᴵʰ` really drives the
system ([`docs/dp-transport.md`](dp-transport.md) §"Route T, and why not Route A").

**No `realʰ ≈ᴹ subᴵ simulatorʰ ∘ idealʰ` — and there must not be.** The
emulation is approximate, so the exact relations that consume a machine
equality (`UC.Graded.≤UCᵍ`'s `Factors`) do not apply.
