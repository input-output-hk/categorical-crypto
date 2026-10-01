# The chimeric ledger, end to end

This is the library's worked example: a small piece of real-world code whose
correctness *depends on a cryptographic primitive*, with that dependence made
into a theorem rather than an assumption. The property proved is preservation
of value; the primitive is a hash function; the bridge between the idealized
hash and a real one is UC emulation.

Everything named below is a checked term in `src/CategoricalCrypto/Examples/`
unless it is marked otherwise. The escape-hatch grep over `src/` stands at its
baseline of 16 hits, every one the words "postulate-free" or "no postulate
left" in an inherited comment (`docs/history/retirement.md` §10).

Reading order — seven modules, plus two support modules a reader never has to
open (`Value`, `Observable`):

| # | module | what it adds |
|---|---|---|
| 1 | `Examples.ChimericLedger` | the ledger itself: `LState`, `total`, `applyTx`, `Variant` |
| 2 | `…ChimericLedger.Replay` | the broken variant loses value, at every hash width |
| 3 | `…ChimericLedger.System` | the ledger plugged onto a random oracle |
| 4 | `…ChimericLedger.Property` | `PreservesValue`, the one statement, on the compiled monitor |
| 5 | `…ChimericLedger.Birthday` | the ideal side, proved |
| 6 | `…ChimericLedger.Transfer` | the three public claims, the corollary at a real hash, and §2's attack against §4's property |
| 7 | `…ChimericLedger.Serialize` | one concrete `ser`, `SerInj` for it, and the ideal headline with nothing assumed |

The two covering leaves are `Transfer` and `Serialize`:
their import closures cover the directory (`Transfer` reaches `Replay`, for
§6's positive-behaviour claim, and through `Property` reaches `Birthday`,
`Observable`, `System` and `Value`). `src/CategoricalCrypto.agda` deliberately
imports none of it (`docs/history/consumer-migration.md` §5), so the directory is
checked per file through those two.

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
chimeric-loses-value : (t : ℕ) → t ≡ total s₀
                     → Pr (Sys chimeric s₀) (auditWatch t replay) ≡ 1ℚ
```

The total `t` the watch measures against is a *parameter*, not read off the
state the system starts in. That is what lets the very watch §4's property uses
— which reads against `genesisTotal V`, the UTxO genesis's total — be read at
the attack.

The module also pins that the state the birthday bound is proved at is *live*
and not vacuously safe: a probability of 0 means nothing if the ledger is
deadlocked. `…Replay.Genesis ℓ ser h₀ a V` proves that at every width too
(`genesis-live`, `genesis-moves`); `genesis-preserves` stays a `ℓ = 1` pin.

The original `ℓ = 1` statements (`initial-total`, `preserved`, `destroyed`,
`rejected`, `chimeric-loses-value`, `consuming-preserves-value`, `genesis-*`)
remain at the bottom of the module as regression checks, still `refl`, oracle
sampling and ℚ arithmetic included.

### The attack against the family property

`…Transfer`'s last section reads the attack at the schedule. `Chimericᶠ V` is the chimeric
variant at the funded initialization, level by level; `funded-total` is the
equal-total side condition that lets §4's watch be read on it; and

```agda
chimeric-loses-value^ω  : (n : ℕ) → Pr (Chimericᶠ V n) (auditWatch (genesisTotal (2 + V)) n (At.replay V n)) ≡ 1ℚ
chimeric-not-preserving : (ε : ℕ → ℕ → ℚ) → NegligibleBound ε
                        → ¬ Hitsᴺ (λ n → morphism (Chimericᶠ V n)) (auditMonitorᶠ (genesisTotal (2 + V))) ε
```

hold for every genesis address `a` and every funded value `2 + V`; the second
refutes the monitored event bound at **every** negligible schedule, `PreservesValue`'s
`εᴸ` among them. The negation is asymptotic, not a single numerical instance: `preservesValue⇒saturated`
hands the attack's own strategy back a bound out of the contextual property,
the allowance is quantified first (at the constant `3`, the attack's
certificate), the slack second, and then negligibility of the birthday term
and of the slack puts `ε n 3 + ν n` eventually below `½` — which cannot
dominate probability one.

**The initialization gap, stated.** The attack needs a funded *account*, and
nothing credits one. `Ledger.checkWdrls-[]` and `System.ledger-keeps-accts-[]`
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
parameter, at the total `t` to preserve:

```agda
auditMonitorᶠ : (n : ℕ) → Proc (LedgerIf^ω n) (LedgerIf^ω n ⊗ᴵ Ωᴵ)

PreservesValue : Systems LedgerIf^ω → Set₁
PreservesValue R = Hitsᴺ (λ n → morphism (R n)) auditMonitorᶠ εᴸ
```

Unfolded: *no admitted query-bounded environment, however it interacts with the
closed system, ever sees an audit answer whose total differs from the one the
ledger started with, except with negligible probability.* Precisely — for every
polynomial allowance `p` there is a negligible `ν` such that **every certified
machine context** of allowance at most `p n` observes the flag with probability
at most `εᴸ n (p n) + ν n`, where `εᴸ n q = (q² + q)·2⁻ⁿ` (`εᴸ-negligible`).

Three design points are worth the reader's attention.

* **The event is interface-observable, and it is read off the run.**
  `auditMonitorᶠ n` is a process on the ledger interface that relays every
  query and answer and raises a private flag the first time an *audit answer*
  reports a total other than the genesis one — nothing about the system's
  internal state is read, which is why a UC emulation can carry it (a
  trajectory bound cannot, and is demoted to the appendix of §6).
  `UC.Machine.Monitor.flagReader` reads the environment's own test over
  `auditMonitorᶠ n ∘ R n`, so the experiment's **verdict is the flag**: the bound is a probability of
  that event, not of an arbitrary Boolean the test might return. And the
  environment is an arbitrary certified context of the machine model
  (`UC.Machine.EventBounds.BoundedAt`), not a strategy.
* **The slack comes after the allowance.** `Hitsᴺ` quantifies the allowance
  first and the negligible slack second, and the slack is uniform over every
  context that allowance admits. The other order does not follow from control
  at polynomial allowances: a system that answers truthfully until query `2^n`
  is negligibly far from one that never does.
* **Monitoring costs this number nothing.** `UC.Quantitative.EventLift.hitsᵘ`
  reads its strategy hypothesis at the environment's own cap: the monitored
  process is the flag wire of its accumulator (`UC.Machine.Monitor.monitor-flag`),
  so the lift is `UC.Machine.StateEvent.Lift.stateLift`, whose one extra unit is
  the flag ask — a real query of the extracted strategy, already inside its
  cap. (The retired monitor-side certificate charged a `q + 1` for the
  accumulator's potential instead; `docs/monitor-flag-spike.md` §4.) No
  certificate of the compiled *test* is charged either: the flag channel is
  internal to the monitored process, so what a strategy extracted from it can
  spend on the **ledger** is the honest allowance alone.

`preservesValue⇒saturated` reads the same bound back at the contexts an
ordinary strategy embeds to, on `UC.Quantitative.EventLift.agree` — the monitored
experiment there *is* layer 1's run of that strategy under `auditWatch`. That
is what lets §2's family refutation and §6's appendix keep speaking about
strategies with no change of meaning, and nothing is spent coming back.

The schedule is the canonical one — hash width `n` at security parameter `n` —
and `SerInj` is the one thing assumed about serialization, per level, because
`Tx` depends on the width and a single `ser` cannot be typed.

## 5. The ideal side, proved

`…Birthday` proves the bound for the *repaired* ledger over the random oracle:

```agda
target : TrajectoryLossBounded inputConsuming (genesis h₀ a₀ V) birthday-bound
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
ideal-preserves-value : SerInj → PreservesValue (genesisTotal V) Ideal
```

The step from `target` to the watch is `Observable.auditWatch-bounded`, on
`auditWatch-sound`: the watch reports nothing the trajectory did not have.
The step from the watch to every certified context is
`Property.hitsᴸ` (inside `ideal-preserves-value`), through
`UC.Quantitative.EventLift.hitsᵘ` (on `StateEvent.Lift.stateLift` at the
monitor's accumulator). No hypothesis is added
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
| a generated output identifier `(h , i)` coinciding with an existing one, genesis identifiers included | also the bad event: the invariant keeps every live key's hash inside `Hs`, whose base case is `h₀ ∷ []`, so the coincidence shows up as a duplicate there. That extra slot is `birthday-bound`'s `+ q` |

## 6. The transfer, and the three claims

`…Transfer` carries three separately named public claims. They are kept apart
on purpose: an upper bound on a *reported* failure is neither a statement about
internal state nor a statement that the implementation answers at all.

| claim | assumes | concludes |
|---|---|---|
| `preserves-value-transfer` | `SerInj`, an emulation | a discrepant audit **answer** is rarely accumulated and reported |
| `ledger-uc-to-state` | the above **+ `TruthfulAudit`** for a supplied state test, at a doubled allowance plus the monitor's one query | that **state event** is rarely raised, under every admitted experiment (`StateSafe`) |
| `ideal-spends-genesis` | nothing | the genesis output **is spent**, and the state moves |

### Claim 1: observable audit safety

```agda
preserves-value-transfer : (a V : ℕ) (R : Systems LedgerIf^ω) → SerInj
                         → R ≈ᶠᴺ Ideal a V → PreservesValue (genesisTotal V) R
```

This is the point of the example. `R ≈ᶠᴺ I` is an allowance-uniform,
simulator-free agreement with negligible error (`UC.Model.Family.Emulation`), and nothing else is
assumed. In particular there is no exact agreement anywhere, no totality
hypothesis and no allowance doubling: the premise's ε is folded into the
saturated slack, which is quantified after the allowance, so the conclusion's
number is the ideal one.

Both allowances are **exact**. The ideal bound `ideal-bounded` is read at the
context's own cap `p n`, through `Protocol.Machine.Agree.upper-run` — operational adequacy
read as a one-sided bound; the comparison is read at `p n + 1`, only because
`Model.Family.Emulation.≈ᶠ-runs`, which lands the premise's schedule on the direct
runs at a strategy's own ask-depth, takes a positive cap; and `Property.hitsᴸ`
lifts the sum back to every certified context. No schedule monotonicity is spent anywhere, which matters
because an arbitrary `NegligibleBound` has none.

`_≈ᶠᴺ_` is the direct-agreement relation this example needs; the generic
quantitative API the rest of the library is stated at is `_≤UC[_,_]_` with its
composition theorems, and `UC.Model.Family.Emulation.≤UC[]⇒≤UCᴺ` is its
crossing into the canonical negligible order (`docs/quantitative-family.md`
§§12, 14.4). The ledger does not go that way: it stays at `_≈ᶠ[_]_` throughout.

### …off a premise about the hash alone

The talk's last slide. The closed system factors through a hash port —
`ledger-factor`, on `UC.Seam.Grounded.factorᵖ` — and `hash-liftᵇ` pushes an
ε-comparison across that factoring: `≈ctx-ext` absorbs the ledger into the test
at its own query bound (`Transfer`'s `ledgerᶠ-qb`: `UC.QueryBound.qb-oneCall` at
`System.ledgerCall`), `≈ctx-sub` absorbs the unit regrading, and
`ledger-factor` reads both sides back as the closed systems `_≈ᶠ[_]_` compares.
The schedule it produces is `εᴴ ε n q = ε n (scale (scale q 1⁺) 1⁺)`, two
exact substitutions. `hash-liftⁿ` is its packaging at the witness form, where
`εᴴ-negligible` is spent. With one upper stage there is no simulator to compose
and hence none to forget afterwards, which is what lets the chain end.

```agda
ledger-preserves-value-from-hash :
    (a V : ℕ) (hash : Systems HashIf^ω) → SerInj → hash ≈ᶠᴺ oracle^ω
  → PreservesValue (genesisTotal V) (Realᴴ hash inputConsuming (genesisAt a V))
```

Assume only that the hash function emulates the random oracle, and the ledger
built on it preserves value. That is the whole claim the slides make.

### Claim 2: state-event safety

UC identifies no internal state, so a state event comes back only under
`TruthfulAudit` (`Property`): the implementation's audit answers detect the
supplied test `badR`, one-sidedly, at the completed-activation boundaries
`PrHit` samples. For a ledger image at `badTotal` that is
`Observable.auditWatch-complete` (`ideal-truthful`); for anything else it is
part of the statement, and `badR` is an arbitrary test, not conservation. The
conclusion is the model-level `StateSafe` — `UC.Machine.StateEvent.Read.StateBoundedᴺ`
of the flag-wire machine `morphism (R n) ▷ idleTest (R n) (badR n)` — over every
admitted experiment, not only strategies:

```agda
ledger-uc-to-state :
    SerInj → (R : Systems LedgerIf^ω) (badR : (n : ℕ) → St (R n) → Bool)
  → R ≈ᶠᴺ Ideal a V → TruthfulAudit (genesisTotal V) R badR
  → StateSafe R badR (λ n q → εᴸ n (q ℕ.+ q))
```

`Property.preservesValue⇒stateSafe` does the work: claim 1's contextual bound
is read back at the embedded strategies (`preservesValue⇒saturated`), where
detection is spent at the instrumented strategy `withAudits d`, and the
resulting `PrHit` bound is lifted to every admitted experiment by
`UC.Machine.StateEvent.Adequacy.hitᴺ⇒stateᴺ`, exactly. The instrumentation
doubles the allowance and monitoring costs nothing, so the schedule is
`εᴸ n (q + q)`.

`ledger-uc-to-pov-family` and `ledger-pov-family-negligible` are the
operational corollaries, read back at the embedded strategies through
`stateᴺ⇒hitᴺ` with the same premises and numbers.

At the ledger's own reading the test is `badTotal`, and the result is monetary
conservation. There `TruthfulAudit` is a theorem for any hash, so
`ledger-conserves-value-from-hash` needs only the hash premise of claim 1;
`Property.ideal-conserves-value` gets the ideal case straight from the birthday
bound, at `εᴸ` and with no audit spent.

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
  **zero slack**, and `mute-never-accepts` says it accepts nothing. So neither
  safety claim implies responsiveness — claim 2 is claim 1 plus detection —
  and that is claim 3's separate job, not a premise of either.
* `Liar`'s state is always bad (`always-bad`) while its answers never report a
  loss. `liar-preserves-value` gives it claim 1 too, its trajectory event
  weighs one, and `liar-not-truthful` shows `TruthfulAudit` fails of it. So a
  state-event conclusion genuinely needs the audit connection claim 2 assumes;
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
   adapter and then a `_≈ᶠᴺ_` proof off `MD.indistinguishable`.
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

The source-backed record of every claim above — compared systems, contexts,
certificates, simulators, error transformations and quantifier order — is
`docs/quantitative-family.md` §14.

The route this arc took to get here, including the premise shapes and the
carries that were tried and retired, is route history:
[`ledger-factoring.md`](ledger-factoring.md),
[`ledger-lift-eps.md`](ledger-lift-eps.md),
[`consumer-migration.md`](history/consumer-migration.md),
[`retirement.md`](history/retirement.md).

## 8. The serializer, concretely

`…Serialize` supplies one `ser` and proves `SerInj` for it, so the ideal
headline is available with nothing assumed about encoding:

```agda
ser    : (n : ℕ) → Ledger.Tx n → List Bool
serInj : SerInj
ideal-preserves-valueˢ : (a V : ℕ) → PreservesValue (genesisTotal V) (Ideal a V)
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
