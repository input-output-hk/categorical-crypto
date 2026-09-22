# The chimeric ledger, end to end

This is the library's worked example: a small piece of real-world code whose
correctness *depends on a cryptographic primitive*, with that dependence made
into a theorem rather than an assumption. The property proved is preservation
of value; the primitive is a hash function; the bridge between the idealized
hash and a real one is UC emulation.

Everything named below is a checked term in `src/CategoricalCrypto/Examples/`
unless it is marked otherwise. The escape-hatch grep over `src/` stands at its
baseline of 16 hits, every one the words "postulate-free" or "no postulate
left" in an inherited comment (`docs/retirement.md` §10).

Reading order — six modules, plus three support modules a reader never has to
open (`Value`, `Observable`, `QueryBound`):

| # | module | what it adds |
|---|---|---|
| 1 | `Examples.ChimericLedger` | the ledger itself: `LState`, `total`, `applyTx`, `Variant` |
| 2 | `…ChimericLedger.Replay` | the broken variant loses value, computed |
| 3 | `…ChimericLedger.System` | the ledger plugged onto a random oracle |
| 4 | `…ChimericLedger.Property` | `PreservesValue`, the one statement |
| 5 | `…ChimericLedger.Birthday` | the ideal side, proved |
| 6 | `…ChimericLedger.Transfer` | the UC transfer, and the corollary at a real hash |

The two covering leaves are `Transfer` and `Replay`: their import closures
cover the directory. `src/CategoricalCrypto.agda` deliberately imports none of
it (`docs/consumer-migration.md` §5), so the directory is checked per file
through those two.

## 1. The ledger

`Examples.ChimericLedger` is plain Agda: `LState` is a UTxO map keyed by
`(txid , index)` together with an account table, `total` adds the two up, and
`applyTx` is the step rule. A transaction consumes UTxO entries and account
balances and creates UTxO entries keyed by `(hash tx , i)`; that hash is the
ledger's one oracle call, and it is explicit in `applyTx`'s `Call` result
rather than hidden in a model.

`Variant` is the whole difference between the two ledgers of the talk:
`chimeric` accepts a transaction with no inputs, `inputConsuming` does not.

## 2. Why the chimeric variant is broken

`…Replay` computes the attack at 1-bit hashes; every statement holds by `refl`,
oracle sampling and ℚ arithmetic included. A transaction with no inputs can be
resubmitted verbatim. Its output key collides with the one it created the first
time, and since the map union keeps the entry already present, the withdrawal is
charged twice while only one output exists:

```agda
initial-total : total s₀ ≡ 2
preserved     : total once ≡ 2
destroyed     : total twice ≡ 1
rejected      : proj₂ (runCall (λ _ → h) (applyTx inputConsuming s₀ txᵃ)) ≡ false
```

No hash collision is needed — only the determinism of `hash tx`. Read through
the same predicate the headline theorem uses, with `replay` submitting twice and
then auditing:

```agda
replay-asks               : asks≤ 3 replay
chimeric-loses-value      : Pr (Sys chimeric       s₀) (auditWatch s₀ replay) ≡ 1ℚ
consuming-preserves-value : Pr (Sys inputConsuming s₀) (auditWatch s₀ replay) ≡ 0ℚ
```

The module also pins that the state the birthday bound is proved at is *live*
and not vacuously safe (`genesis-live`, `genesis-moves`, `genesis-preserves`):
a probability of 0 means nothing if the ledger is deadlocked.

These are at `ℓ = 1`, which is what makes them `refl`. The argument does not
depend on the width — the attack never needs a collision — but at an abstract
`ℓ` the run branches over `2^ℓ` hashes and the statement stops being a
computation.

## 3. The system

`…System` plugs the ledger onto a hash functionality, exactly as the slides
draw it:

```agda
oracle : Protocol unitᴵ HashIf            -- the lazily sampled random oracle
ledger : Variant → LState → Protocol HashIf LedgerIf
Sysᴴ hash vr s₀ = ledger vr s₀ ∘ᵖ hash    -- over an arbitrary hash
Sys             = Sysᴴ oracle             -- the closed ideal system
```

An environment drives `Sys` through `LedgerIf` alone: it submits transactions
and asks for audits (`Query`), and reads acknowledgements and totals
(`Answer`). It never sees the oracle. `genesis`/`spendGenesis`/`accepted` fix
where the experiment starts.

## 4. The property

`…Property` states it once, for a family of systems indexed by the security
parameter:

```agda
PreservesValue : Systems LedgerIf^ω → Set
PreservesValue R = SaturatedBoundedᴺ R auditWatch εᴸ
```

Unfolded: *no polynomially query-bounded environment ever gets the ledger to
answer an audit with a total different from the one it started with, except
with negligible probability.* Precisely — for every polynomial allowance `p`
there is a negligible `ν` such that every strategy asking at most `p n`
queries makes the watch report a violation with probability at most
`εᴸ n (p n) + ν n`, where `εᴸ n q = (q² + q)·2⁻ⁿ` (`εᴸ-negligible`).

Two design points are worth the reader's attention.

* **The event is interface-observable.** `auditWatch s₀` plays a strategy
  unchanged and accumulates `true` the first time an *audit answer* reports a
  total other than `total s₀`. That is something an environment can see, which
  is exactly the class a UC emulation preserves (`UC.Audit`). A bound on the
  system's internal state trajectory is not, and is demoted to the appendix of
  §6.
* **The slack comes after the allowance.** `SaturatedBoundedᴺ` quantifies the
  allowance first and the negligible slack second. The other order does not
  follow from control at polynomial allowances: a system that answers
  truthfully until query `2^n` is negligibly far from one that never does
  (`UC.Saturated`'s header).

The schedule is the canonical one — hash width `n` at security parameter `n` —
and `SerInj` is the one thing assumed about serialization, per level, because
`Tx` depends on the width and a single `ser` cannot be typed.

## 5. The ideal side, proved

`…Birthday` proves the bound for the *repaired* ledger over the random oracle:

```agda
target : TrajectoryLossBounded inputConsuming (genesis h₀ a₀ V) εbirthday
```

`Protocol.Safety.hit-bounded` carries the adaptivity, so what is owed is a
non-adaptive per-step certificate, built from a potential
(`Uniform.Duplicate.Φ` over the hashes in the oracle table) and an invariant.
The crux is the invariant's `Stale` field: every hash already in the table
belongs to a transaction one of whose inputs is already spent, so with
`SerInj` a table *hit* at an accepted transaction is impossible — which is what
rules out §2's replay. The witness for a freshly hashed transaction is its
first input, and that input exists only because `inputConsuming` demands one.
**That is the single place the slides' repair is spent**; with `chimeric` in
its place the invariant is false.

`…Property.ideal-preserves-value` reads this at the schedule and through the
watch, which is where the trajectory statement becomes the interface one:

```agda
ideal-preserves-value : SerInj → PreservesValue Ideal
```

The step from `target` to the watch is `Observable.auditWatch-bounded`, on
`auditWatch-sound`: the watch reports nothing the trajectory did not have.
No hypothesis is added.

### …and what in it is not probabilistic

The certificate decomposes: *rules + freshness → conservation*, *sampling →
freshness fails with probability ≤ birthday*, *audit soundness → the
observable bound*. Only the middle step is probabilistic, and the first is
factored out and named, in `…ChimericLedger.Value`:

```agda
conservation : ∀ vr s tx hs h → (∀ k → k ∈ keysU (proj₁ s) → proj₁ k ∈ hs)
             → ¬ (h ∈ hs) → total (after vr s tx h) ≡ total s
```

Its conclusion mentions no oracle and no probability, and its two premises are
the whole of what the rules need: `hs` names the hashes the state's live UTxO
keys may carry — the only well-formedness conservation asks for — and `h ∉ hs`
is the step's noncollision condition. A *rejected* transaction is conserved
for free, because it leaves the state alone; an accepted one is conserved by
the balance equation `checkIns` and `checkWdrls` enforce. The certificate
supplies `hs = Hs tbl` and uses this for its `intact` field instead of
carrying a second conservation proof.

So what is left to the probability is exactly the failure of `h ∉ hs`, and the
four exceptional cases sort as follows.

| case | decided by |
|---|---|
| the same transaction resubmitted | the ledger rules: this is a table *hit*, not a collision between distinct inputs. `Stale` + `no-replay`, whose witness is the transaction's first input and so exists only under `inputConsuming` |
| distinct transactions with equal serialization | `SerInj`, spent once, in `stale-not-accepted` |
| distinct oracle inputs with equal digests | remains in the bad event: `flag`, paid for by `Φ` |
| a generated output identifier `(h , i)` coinciding with an existing one, genesis identifiers included | also the bad event: the invariant keeps every live key's hash inside `Hs`, whose base case is `h₀ ∷ []`, so the coincidence shows up as a duplicate there. That extra slot is `εbirthday`'s `+ q` |

## 6. The transfer

```agda
preserves-value-transfer : (a V : ℕ) (R : Systems LedgerIf^ω) → SerInj
                         → R ≤UC^ωⁿ Ideal a V → PreservesValue a V R
```

This is the point of the example. `R ≤UC^ωⁿ I` is an allowance-uniform
emulation with negligible error (`UC.Asymptotic.Family`); the proof is
`uc-preservesᴺ` on `≤UC^ωⁿ⇒≈negl`, and nothing else is assumed. In particular
there is no exact agreement anywhere, no totality hypothesis and no allowance
doubling: the premise's ε is folded into the saturated slack, which is
quantified after the allowance, so the conclusion's number is the ideal one.

### …off a premise about the hash alone

The talk's last slide. The closed system factors through a hash port —
`ledger-factor`, on `UC.Factor.factorᵖ` — and `hash-liftⁿ` pushes an emulation
across that factoring: `≈ctx-ext` absorbs the ledger into the test at its own
query bound (`QueryBound.qb-ledger`, an instance of `UC.QueryBound.qb-oneCall`),
`≈ctx-sub` absorbs the unit regrading, and `ledger-factor` reads both sides
back as the closed systems `_≤UC^ωⁿ_` compares. With one upper stage there is
no simulator to compose and hence none to forget afterwards, which is what lets
the chain end.

```agda
ledger-preserves-value-from-hash :
    (a V : ℕ) (hash : Systems HashIf^ω) → SerInj → hash ≤UC^ωⁿ oracle^ω
  → PreservesValue a V (Realᴴ hash inputConsuming (genesisAt a V))
```

Assume only that the hash function emulates the random oracle, and the ledger
built on it preserves value. That is the whole claim the slides make.

### Appendix: the real system's own states

`Transfer`'s last section restates the conclusion over `PrHit` — the real
system's internal state trajectory — and it is *not* free. UC identifies no
internal state, so the bound comes back only under `TruthfulAudit`: the
implementation's audit answers report its own state. For a ledger image that is
`Observable.auditWatch-complete` (`ideal-truthful`); for anything else it is
part of the statement. The instrumentation `withAudits` that makes the watch see
every boundary the trajectory inspects doubles the allowance, and the cost is
charged in the conclusion:

```agda
ledger-uc-to-pov-family :
    SerInj → (R : Systems LedgerIf^ω) (badR : Bad R)
  → R ≤UC^ωⁿ Ideal a V → TruthfulAudit R badR
  → SaturatedHitᴺ R badR (λ n q → εᴸ n (q ℕ.+ q))
```

`ledger-pov-family-negligible` reads the same conclusion as one number.

## 7. What is assumed, and what is not delivered

Assumed, and nowhere hidden:

* `SerInj` — the birthday theorem's own injective-serialization hypothesis;
* the emulation — the one cryptographic premise, in §6's shape;
* `TruthfulAudit` — appendix only, never for the headline property.

Not delivered:

1. **A named hash construction.** What is left assumed at a concrete ledger is
   the emulation alone. Supplying it needs a construction whose interface
   matches: `Examples.MerkleDamgard`'s ideal oracle hashes fixed-length
   messages where the ledger hashes bitstrings, so the instance wants a padding
   adapter and then a `_≤UC^ωⁿ_` proof off `MD.indistinguishable`.
2. **A nontrivially graded hash port.** The port is an object boundary and both
   stages are pure, so every simulator there is a scalar and is provably blind
   (`docs/ledger-factoring.md`, closing section).
3. **§2 at an arbitrary hash width.** The replay statements are `refl` at
   `ℓ = 1` only.

The route this arc took to get here, including the premise shapes and the
carries that were tried and retired, is route history:
[`ledger-factoring.md`](ledger-factoring.md),
[`ledger-lift-eps.md`](ledger-lift-eps.md),
[`consumer-migration.md`](consumer-migration.md),
[`retirement.md`](retirement.md).
