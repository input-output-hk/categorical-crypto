# RO-model commitment: the extraction half

A hash-based commitment against a **corrupted committer**: `c = H(b ∷ r)` to
commit, `(b , r)` to open, an honest receiver that re-hashes and compares. The
simulator extracts the committed bit from the oracle answers it relayed. It is
the repository's first emulation whose ε is not zero. Modules:
`Examples.ROCommitment` (interfaces and machines), `.Extraction` (`extract`,
`Pins`), `.Game` (the closed games and the bound), `.UC` (images and
certificates), `.Asymptotic`, `.Test`.

## The protocol

Security parameter `k`. Points are `Vec Bool (suc k)`, digests `Vec Bool k`;
the committed bit rides in FRONT of the opening randomness, which is what makes
a preimage extractable at all.

| party | real world | ideal world |
|---|---|---|
| corrupted committer | `Advᴵ`: `queryᴬ x`, `commitᴬ c`, `openᴬ b r` | the same, through the simulator |
| honest receiver | the real protocol's `Honᴵ` reports | `F_com`'s, relayed |
| below | `Resᴵ` = a lazily sampled oracle **and** a one-shot cell | the same |

## Where `F_com`'s memory lives, and what was rejected

**The ideal functionality's one bit of state is a CELL in the resource below,
beside the oracle, so the ideal functionality is a `wireᴹ`.** `putᴿ b` stores
the committed bit and receipts the receiver, `getᴿ` releases it, `nakᴿ`
refuses; `downᶠ`/`upᶠ` relabel those onto `Lkᴵ` and `Honᴵ`. The real protocol
uses only the oracle half of `Resᴵ` and emits its own receipt, which is the
asymmetry the decision costs.

The reason is [`docs/hash-forward.md`](hash-forward.md) §"The one structural
fact that makes it affordable": `sub s ∘ gradedᵒ g` is `subᴵ s ∘ g` in `𝒢ₚ`,
whose composition is a ⊕-trace, and there are exactly two readable ways to get
one — `Protocol.Machine.Compose.morphismCompose` (both factors protocol images,
unavailable because `subᴵ s` is not one) and `UC.Machine.Wire.∘-wireᴹ` (the
lower factor a wire). A stateful `F_com` would cost the trace argument again,
for a `subᴵ` that cannot be a `morphism` image.

Three alternatives, and why each was rejected.

1. **A stateful ideal functionality with `traceᴹ` taken directly.** Not merely
   a re-run of `Protocol.Machine.Compose`: that argument is for two *protocol*
   images and `subᴵ s` is not one, so the composite would have to be unrolled
   through `iter` rather than assembled from existing lemmas.
2. **An explicit `GConstructionEmbedding` argument for this one composite.**
   Same content as (1) with the generic absorption lemmas inlined: `absorbˡ`/
   `absorbʳ` are exactly what `∘-wireᴹ` applies, and they need a wire on one
   side to apply at all.
3. **The cell inside the real protocol as well.** The real receiver has no bit
   to store at `commitᴬ c` — it holds the *digest* — so it would store a digest
   in a bit cell, and the resource would stop being `F_com`'s memory and start
   being an encoding.

What the decision buys beyond the trace: `subᴵ simulator ∘ ideal` reduces by
`∘-wireᴹ` to the simulator with its interface renamed and its own state, a
concrete machine with a readable state, which is what the closed game models.
Unlike the hash-then-forward toy, `real` is deliberately **not** `≈ᴹ` to that
composite: the emulation is approximate.

## The simulator

`simulator : Proc Lkᴵ Advᴵ`, three states (`waitˢ`, `relayˢ`, `checkˢ`); its
log is the list of oracle answers it has relayed:

* `queryᴬ x` → relay `hashˢ x`; the answer is logged and passed up as `ansᴬ`.
* `commitᴬ c` → `extract c L` reads the bit of the **unique** preimage of `c` in
  the log, `false` at none or at several; `commitˢ` that bit to `F_com`.
* `openᴬ b r` → relay `hashˢ (b ∷ r)`, then `openˢ` iff the digest is `c`
  **and** `b` is the extracted bit, `failˢ` otherwise (`release`).

The log conses an entry at EVERY relayed answer, including one the oracle
served from its table, so it is not the oracle's table: after a repeated query
it holds the digest twice and `extract` reads `false`
(`Realization.Bisim.extract-relog`). The closed game extracts from the oracle's
table instead; see "Not delivered" §1.

## The flags, and their potentials

The two games differ exactly at an opening the receiver accepts and the
simulator will not deliver: `H(b ∷ r) ≡ c` with `b` not the extracted bit.
`Game.agree-off` shows the two flags cover it, through the invariant
`Pins c e t` — *every* preimage of `c` in the table starts with `e` — the one
piece of combinatorics the argument needs:

| flag | potential | bound | established by |
|---|---|---|---|
| `dup (answers t)` — a repeat in the oracle's ANSWER log | `Uniform.Duplicate.Φ` | `(q² + q)·2⁻ᵏ` | `Potential.collision-cert` |
| a fresh sample landing on the outstanding digest | the indicator | `q·2⁻ᵏ` | `Potential.rare-cert` + `guess-drift` |

combined by `Potential.∨-cert` (a binding argument's bad event is a
disjunction). `Pins` is *established* at `commitᴬ` by `pins-extract`, which
needs a duplicate-free answer log — that is why the birthday flag is the first
one — and *preserved* by `pins-∷` across a sample that misses `c` — which is
why a sample that hits it is the second. At the opening `pins-lookup` reads it
off: the point just fetched is in the table (`fetch-bis` hands that back
explicitly, because the `with` on the table lookup would otherwise discard it),
and its answer is `c`, so its first bit is the extracted one.

**The fixed-secret caveat does not bite.** A secret already determined by the
state is one the next query hits with probability 1, so `RareRaise` needs the
point drawn lazily (`GamePlaying.Potential`'s header). Here the point is the
oracle's own fresh sample, drawn *at* the query by `fetch`, and the flag is
raised by the kernel's comparison against the stored digest — exactly the
shape `guess-drift` discharges.

## The bound

```agda
-- Examples.ROCommitment.Game
extraction-bound : (m : ℕ) (d : Strat Q R) → asks≤ m d
                 → ∣ Pr₁ (runWith respI sI₀ d) -ℚ Pr₁ (runWith respR sR₀ d) ∣ℚ ≤ℚ ε m
ε m = fromℕ (m * m + m) *ℚ inv-pow-2 k +ℚ fromℕ m *ℚ inv-pow-2 k
```

i.e. **`(m² + m)·2⁻ᵏ + m·2⁻ᵏ`** for every adaptive adversary of at most `m`
activations. `Asymptotic.εᶜ` merges the numerators into `(m² + 2m)·2⁻ᵏ` and
`Asymptotic.εᶜ-negligible` proves `NegligibleBound εᶜ` at the identity
schedule, the digest length being the security parameter.
`Test.bounded` instantiates `Asymptotic.extraction-boundⁿ` at `k = 5` (where it
is 15/32) against a live adaptive three-query attack — query the oracle, commit
at the answer, open at the same pair — so the quantifier is inhabited by an
adversary that reaches the opening.

## Exact query accounting

`Examples.ROCommitment.UC`, two weightings of one `UC.QueryBound.Exact` ledger
over the simulator's step:

| statement | `δ` | `cost` | ledger | reading |
|---|---|---|---|---|
| `sim-hash-count` (`simExactHash`) | `hashes` | `points` | constantly 0 | exactly one oracle relay per adversary message that names a point, no residual |
| `sim-message-count` (`simExactAll`) | `downward` | `perMessage` | 1 at `checkˢ` | one downward message per query, one per commitment, two per opening |

`simCert : Certified 2 simulator` is the matching amortised ceiling and
`simQB : QB 2 simulator` crosses it to the model.

**Why the simulator queries at the opening.** A simulator answering the
opening from its log alone would make the two oracle tables differ: in the
REAL world the receiver samples `H(b ∷ r)` and the table gains that entry, in
the IDEAL world it does not, and a later adversary query of `b ∷ r` returns it
on one side and a fresh uniform on the other. The values agree in distribution
only after a deferred-sampling argument; off the bad event they are **not**
pointwise equal (the real side's value is the one the opening rejected), so
`FLGP` does not reach it. Querying at the opening keeps the tables identical
step for step, which makes both `StepBisim` instances one case analysis each;
the price is one relay per opening, stated exactly above.

## Not delivered

### 1. The UC-level ε-statement

The closed bound is about two reactive `Dist-ℚ` kernels; the UC statement is
about the observation of a composite in the sealed model. At the open resource
domain it is `raw-emulation`, the hypothesis
`realᶠ ≈ctx[ εᶜ ] subᶠ comSim idealᶠ` of
`Examples.CoinToss.Compose.coin-toss-from-comᶜ`; `comSim`'s certificate and
`εᶜ-negligible` are the other two components of the `_≤UC^ωᵉ_` witness and are
delivered. The theorem actually aimed at is the resource-installed
`Examples.ROCommitment.Realization.Assembly.Realization`, whose route and
residuals are [`docs/rcom-icom-b1.md`](rcom-icom-b1.md) §7. Of the transport
layer underneath it ([`docs/dp-transport.md`](dp-transport.md),
[`docs/fcom-uc.md`](fcom-uc.md)) the real leg is a theorem —
`Realization.Bound.extraction-real` bounds the closed real MACHINE
`real 𝒫.∘ resource` against the pruned ideal GAME by `Game.ε m`. The ideal leg
is blocked at the machines as they stand: the simulator's log is not the
oracle's table (§"The simulator"), so after a repeated query it extracts
`false` where `Game.comI` extracts the committed bit, and the game's bad event
(a duplicate in the ORACLE's answer log) has not fired. Either the simulator
caches (logs only a point its log does not already answer), or `Game.respI` is
restated over the relay log — which makes `Game.cert` false, since a repeated
query then raises `dup` with certainty.

### 2. The log-only simulator

The residual of "Why the simulator queries at the opening" is the
deferred-sampling identification

```agda
defer : (t : Tbl) (x : Pt) (m : Com) (f : Bool) (d : Strat Q R)
      → Pr₁ (runWith respI (t , m) d)
        ≡ Pr₁ (runWith respI′ ((x , h) ∷ t , m) d)   -- averaged over a fresh h
```

— "an unread lazily sampled entry is invisible". The engine for it is
`GamePlaying.Defer.runWith-avg` ([`docs/fcom-hiding.md`](fcom-hiding.md)
§"The deferred-sampling lemma"), with `GamePlaying.Test.DeferMachine.defer` as
its smallest instance; it is not instantiated at this game, so the simulator
still relays at the opening.
