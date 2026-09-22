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
| 4 | `…ChimericLedger.Property` | `PreservesValue`, the one statement, on the compiled monitor |
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
is asymptotic, not a single numerical instance: `preservesValue⇒saturated`
hands the attack's own strategy back a bound out of the contextual property,
the allowance is quantified first (at the constant `3`, the attack's
certificate), the slack second, and then negligibility of the birthday term
and of the slack puts `εᴹ n 3 + ν n` eventually below `½` — which cannot
dominate probability one.

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
auditMonitorᶠ : (n : ℕ) → Proc (LedgerIf^ω n) (LedgerIf^ω n ⊗ᴵ Flagᴵ)

PreservesValue : Systems LedgerIf^ω → Set₁
PreservesValue R = Hitsᴺ (λ n → morphism (R n)) auditMonitorᶠ εᴹ
```

Unfolded: *no admitted query-bounded environment, however it interacts with the
closed system, ever sees an audit answer whose total differs from the one the
ledger started with, except with negligible probability.* Precisely — for every
polynomial allowance `p` there is a negligible `ν` such that **every certified
machine context** of allowance at most `p n` observes the flag with probability
at most `εᴹ n (p n) + ν n`, where `εᴹ n q = εᴸ n (q + 1)` and
`εᴸ n q = (q² + q)·2⁻ⁿ` (`εᴹ-negligible`).

Three design points are worth the reader's attention.

* **The event is interface-observable, and it is read off the run.**
  `auditMonitorᶠ n` is a process on the ledger interface that relays every
  query and answer and raises a private flag the first time an *audit answer*
  reports a total other than the genesis one — nothing about the system's
  internal state is read, which is why a UC emulation can carry it (a
  trajectory bound cannot, and is demoted to the appendix of §6).
  `UC.Machine.Monitor.compileᴹ` wraps the environment's own test in it, so the
  compiled experiment's **verdict is the flag**: the bound is a probability of
  that event, not of an arbitrary Boolean the test might return. And the
  environment is an arbitrary certified context of the machine model
  (`UC.Model.EventBounds.BoundedAt`), not a strategy.
* **The slack comes after the allowance.** `Hitsᴺ` quantifies the allowance
  first and the negligible slack second, and the slack is uniform over every
  context that allowance admits. The other order does not follow from control
  at polynomial allowances: a system that answers truthfully until query `2^n`
  is negligibly far from one that never does.
* **`+ 1` is the whole price of monitoring.** The compiled context leaves an
  extracted strategy one query less than it has, because the monitor's
  accumulator needs potential of its own
  (`UC.Quantitative.EventLift.Cov.covCtx`); that is the `q + 1` in `εᴹ`, and
  nothing else about the compilation reaches the number. In particular the
  coarse certificate `κμ c = 2·(c ⊔ 1)` of the compiled *test* is not charged
  here: the flag channel is internal to the compiled context, so what a
  strategy extracted from it can spend on the **ledger** is the honest
  allowance alone.

`preservesValue⇒saturated` reads the same bound back at the contexts an
ordinary strategy embeds to, on `UC.Machine.Monitor.Agree.agree` — the compiled
experiment there *is* layer 1's run of that strategy under `auditWatch`. That
is what lets §7's counterexamples and §6's appendix keep speaking about
strategies with no change of meaning, and nothing is spent coming back.

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
The step from the watch to every certified context is
`UC.Quantitative.EventLift.ledger-hitsᵘ`, which is `eventSkeleton`'s
event-sensitive decomposition at the compiled monitor. No hypothesis is added
by either.

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
emulation with negligible error (`UC.Asymptotic.Family`), and nothing else is
assumed. In particular there is no exact agreement anywhere, no totality
hypothesis and no allowance doubling: the premise's ε is folded into the
saturated slack, which is quantified after the allowance, so the conclusion's
number is the ideal one.

Both allowances are **exact**, and they are the same one. The comparison is
read at `p n + 1` — the context's cap plus the monitor's accumulator — through
`Asymptotic.Family.≈ᶠ-runs`, which lands the premise's schedule on the direct
runs at a strategy's own ask-depth; the ideal bound `ideal-bounded` is read
there too; and `Property.hitsᴸ` lifts the sum back to every certified context.
No schedule monotonicity is spent anywhere, which matters because an arbitrary
`NegligibleBound` has none.

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
cost from the monitor's extra query
([`event-bounds-in-setup.md`](event-bounds-in-setup.md)), and the two are never
netted against each other: the appendix reads the transfer at the embedded
strategies (`watched-transfer`, the same emulation premise carried by
`uc-preservesᴺ` on `≤UC^ωⁿ⇒≈negl`), where the watch costs the allowance
nothing, so no flag query is charged to it on top.
`ledger-pov-family-negligible` reads the same conclusion as one number.

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

## 8. The serializer, concretely

`…Serialize` supplies one `ser` and proves `SerInj` for it, so the ideal
headline is available with nothing assumed about encoding:

```agda
ser    : (n : ℕ) → Ledger.Tx n → List Bool
serInj : SerInj
ideal-preserves-value′ : (a V : ℕ) → PreservesValue a V (Ideal a V)
```

It is built from `Data.Bits.Codec`, whose `Codec A` bundles an encoder with a
decoder that consumes a *prefix* and returns the unread remainder, subject to
`decode (encode x ++ r) ≡ just (x , r)`. That law is what makes concatenation
unambiguous — the first decoder finds the boundary — so `×-codec` needs no
separator and injectivity is one `cong` away. Lists carry a length prefix
(which is also what makes the decoder structurally recursive); `ℕ` is unary,
since the example needs injectivity rather than compactness; a hash is written
as its `n` bits with no prefix, its width being known to both sides.
`txCodec n` is these combinators read at `Tx`'s shape, and `ser n` is its
`encode`. The generic theorems stay parameterized by `ser`: this is an
instance, not a narrowing.

`SerInj` is literal transaction equality, and the encoding is faithful to
that: permuting a transaction's inputs changes its bits. A canonical encoding
of some quotient of `Tx` would be a different, unstated semantic choice.
