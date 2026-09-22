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

Reading order — seven modules, plus three support modules a reader never has to
open (`Value`, `Observable`, `QueryBound`):

| # | module | what it adds |
|---|---|---|
| 1 | `Examples.ChimericLedger` | the ledger itself: `LState`, `total`, `applyTx`, `Variant` |
| 2 | `…ChimericLedger.Replay` | the broken variant loses value, at every hash width |
| 3 | `…ChimericLedger.System` | the ledger plugged onto a random oracle |
| 4 | `…ChimericLedger.Property` | `PreservesValue`, the one statement |
| 5 | `…ChimericLedger.Birthday` | the ideal side, proved |
| 6 | `…ChimericLedger.Transfer` | the three public claims, and the corollary at a real hash |
| 7 | `…ChimericLedger.ReplayFamily` | §2's attack against §4's property |

The two covering leaves are `Transfer` and `ReplayFamily`: their import
closures cover the directory (`Transfer` now reaches `Replay`, for §6's
positive-behaviour claim). `src/CategoricalCrypto.agda` deliberately imports
none of it (`docs/consumer-migration.md` §5), so the directory is checked per
file through those two.

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

A transaction with no inputs can be resubmitted verbatim. Its output key
collides with the one it created the first time, and since the map union keeps
the entry already present, the withdrawal is charged twice while only one output
exists. No hash collision is needed — only the determinism of `hash tx`.

`…Replay.Attack ℓ ser V` proves this at **every hash width and every
serialization**, at a funded account holding `2 + V`:

```agda
preserved   : (h : Hash) → total (once h)  ≡ total s₀
destroyed   : (h : Hash) → total (twice h) ≡ suc (V + 0)   -- one unit gone
rejected    : (h : Hash) → proj₂ (runCall (λ _ → h) (applyTx inputConsuming s₀ txᵃ)) ≡ false
replay-asks : asks≤ 3 replay
```

The same transaction is submitted twice, so the argument never needs two
transactions to share an encoding: it is compatible with `SerInj`. What carries
it at abstract `ℓ` is `System.oracle-repeat` — a point already in the lazy
table is answered *from* the table, with no sampling — so only the **first**
submission branches, over `uniformVec ℓ`, and every branch reports the same
loss. The verdict is therefore constant and the probability exact:

```agda
chimeric-loses-value : (r : LState) → total r ≡ total s₀
                     → Pr (Sys chimeric s₀) (auditWatch r replay) ≡ 1ℚ
```

The state `r` the watch measures against is a *parameter*, distinct from the
state the system starts in. That is what lets the very watch §4's property uses
— which reads against `total (genesisAt a V n)` — be read at the attack.

The module also pins that the state the birthday bound is proved at is *live*
and not vacuously safe: a probability of 0 means nothing if the ledger is
deadlocked. `…Replay.Genesis ℓ ser h₀ a V` proves that at every width too
(`genesis-live`, `genesis-moves`); `genesis-preserves` stays a `ℓ = 1` pin.

The original `ℓ = 1` statements (`initial-total`, `preserved`, `destroyed`,
`rejected`, `chimeric-loses-value`, `consuming-preserves-value`, `genesis-*`)
remain at the bottom of the module as regression checks, still `refl`, oracle
sampling and ℚ arithmetic included.

### The attack against the family property

`…ReplayFamily` reads the attack at the schedule. `Chimericᶠ V` is the chimeric
variant at the funded initialization, level by level; `funded-total` is the
equal-total side condition that lets §4's watch be read on it; and

```agda
chimeric-loses-value^ω  : (n : ℕ) → Pr (Chimericᶠ V n) (auditWatch a (2 + V) n (replay n)) ≡ 1ℚ
chimeric-not-preserving : ¬ PreservesValue a (2 + V) (Chimericᶠ V)
```

hold for every genesis address `a` and every funded value `2 + V`. The negation
is asymptotic, not a single numerical instance: the allowance is quantified
first (at the constant `3`, the attack's certificate), the slack second, and
then negligibility of the birthday term and of the slack puts `εᴸ n 3 + ν n`
eventually below `½` — which cannot dominate probability one.

**The initialization gap, stated.** The attack needs a funded *account*, and
nothing credits one. `System.checkWdrls-[]` and `System.ledger-keeps-accts-[]`
are the exact clause, checked: `applyTx`'s only effect on the account table is
`checkWdrls a wds`, whose every branch either fails or recurses under `subOne`,
which adds no key and raises no balance, so **an activation started at an empty
account table leaves it empty and every accepted withdrawal there is zero**.
`System.genesis` has an empty table, so **no prefix reaches the attack's
initialization**. (The per-activation statement is what is checked; the
induction chaining it along a whole run is not a theorem here, since no result
needs it.) `Chimericᶠ` therefore starts account-funded while `Ideal` starts at
the UTxO genesis; only the watch and the allowance are shared, and those are
shared exactly. Whether the chimeric variant preserves value *at* the UTxO
genesis is a different question and is left open — with an empty account table
the replay charges nothing.

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

## 6. The transfer, and the three claims

`…Transfer` carries three separately named public claims. They are kept apart
on purpose: an upper bound on a *reported* failure is neither a statement about
internal state nor a statement that the implementation answers at all.

| claim | assumes | concludes |
|---|---|---|
| `preserves-value-transfer` | `SerInj`, an emulation | a discrepant audit **answer** is rarely accumulated and reported |
| `ledger-uc-to-pov-family` | the above **+ `TruthfulAudit`**, at a doubled allowance | the real system's own **state trajectory** is rarely bad |
| `ideal-spends-genesis` | nothing | the genesis output **is spent**, and the state moves |

### Claim 1: observable audit safety

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

### Claim 2: from the audit to the state trajectory

`Transfer`'s appendix restates the conclusion over `PrHit` — the real system's
internal state trajectory — and it is *not* free. UC identifies no internal
state, so the bound comes back only under `TruthfulAudit`: the implementation's
audit answers report its own state. For a ledger image that is
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

That doubling is the price of the **honest interface** — of asking the
implementation at every boundary the trajectory inspects. It is a different
cost from the flag-reading a monitor compiler pays
([`event-bounds-in-setup.md`](event-bounds-in-setup.md)), and the two are never
netted against each other. `ledger-pov-family-negligible` reads the same
conclusion as one number.

### Claim 3: positive behaviour

```agda
ideal-spends-genesis : (a V n : ℕ)
  → Pr (Ideal a V n) (Live.spend a V n) ≡ 1ℚ
  × ((h : Ledger.Hash n) → Live.moved a V n h ≡ (((h , 0) , (a , V)) ∷ [] , []))
```

Assumes nothing, at every level: the genesis output is accepted with
probability one *through the oracle*, and the state moves — its value reappears
under the transaction's own hash. This is the acceptance and its state effect,
not global liveness: one accepted transaction says nothing about the rest, and
neither safety claim is strengthened with a totality premise.

### What claims 1 and 2 do not say

Two checked counterexamples, both `Systems LedgerIf^ω`:

* `Mute` diverges at every query. `mute-preserves-value` gives it claim 1 with
  **zero slack**, and `mute-never-accepts` says it accepts nothing. So the
  observable bound does not imply responsiveness — that is claim 3's separate
  job, and it is not a premise of claim 1.
* `Liar`'s state is always bad (`always-bad`) while its answers never report a
  loss. `liar-preserves-value` gives it claim 1 too, its trajectory event
  weighs one, and `liar-not-truthful` shows `TruthfulAudit` fails of it. So a
  trajectory conclusion genuinely needs the audit connection claim 2 assumes;
  claim 1 alone does not supply it.

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
3. **A reachability result joining §2 to §4.** The replay attack is now proved
   at every hash width and serialization, and it refutes the family property at
   its own initialization — but that initialization is an account-funded state,
   and `System.ledger-keeps-accts-[]` shows the UTxO genesis never reaches one.
   What is missing is either a genesis from which a funded account *is*
   reachable, or the separate verdict on the chimeric variant at the UTxO
   genesis itself.

The route this arc took to get here, including the premise shapes and the
carries that were tried and retired, is route history:
[`ledger-factoring.md`](ledger-factoring.md),
[`ledger-lift-eps.md`](ledger-lift-eps.md),
[`consumer-migration.md`](consumer-migration.md),
[`retirement.md`](retirement.md).
