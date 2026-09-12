# RO-model commitment: the extraction half

Branch `fcom-extract`, off `protocol-rewrite` at `f3add698`.

A hash-based commitment against a **corrupted committer**: `c = H(b ∷ r)` to
commit, `(b , r)` to open, an honest receiver that re-hashes and compares. The
simulator extracts the committed bit from the oracle queries it relayed. This
is the first cryptographic result on the nontrivial-grade path, and the first
in the repository whose emulation carries an ε that is not zero.

Everything below is a checked term unless it is in the "Not delivered" section;
hatches in `src/` stay at their baseline of zero (16 grep hits, all of them the
words "postulate-free" in inherited comments, before and after).

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

**Decision: the ideal functionality's one bit of state is a CELL in the
resource below, beside the oracle, so the ideal functionality is again a
`wireᴹ`.** `putᴿ b` stores the committed bit and receipts the receiver, `getᴿ`
releases it, `nakᴿ` refuses; `downᶠ`/`upᶠ` relabel those onto `Lkᴵ` and `Honᴵ`.
The real protocol uses only the oracle half of `Resᴵ` and emits its own
receipt, which is the asymmetry the decision costs.

This is the constraint [`docs/hash-forward.md`](hash-forward.md) records under
"The one structural fact that makes it affordable": `sub s ∘ gradedᵒ g` is
`subᴵ s ∘ g` in `𝒢ₚ`, whose composition is a ⊕-trace, and there are exactly two
readable ways to get one — `Protocol.Machine.Compose.morphism-∘` (both factors
protocol images, unavailable because `subᴵ s` is not one) and
`UC.Machine.Wire.∘-wireᴹ` (the lower factor a wire). So a stateful `F_com`
would have cost the 312-line trace argument again, for a `subᴵ` that cannot be
a `morphism` image.

Three alternatives, and why each was rejected.

1. **A stateful ideal functionality with `traceᴹ` taken directly.** This is the
   argument the wire decision exists to avoid. It is not merely re-running
   `Protocol.Machine.Compose`: that module's argument is for two *protocol*
   images, and `subᴵ s` parks a continuation where a protocol image does not
   (`Protocol.Machine`'s own header), so the composite would have to be
   unrolled through `iter` rather than assembled from existing lemmas.
2. **An explicit `GConstructionEmbedding` argument for this one composite.**
   Same content as (1) with the generic absorption lemmas inlined; it buys
   nothing, because `absorbˡ`/`absorbʳ` are exactly what `∘-wireᴹ` already
   applies and they need a wire on one side to apply at all.
3. **The cell inside the real protocol as well** (both worlds using `putᴿ`).
   Dropped: the real receiver has no bit to store at `commitᴬ c` — it holds the
   *digest* — so it would have to store a digest in a bit cell, and the
   resource would stop being `F_com`'s memory and start being an encoding.

What the decision buys, beyond the trace: `subᴵ simulator ∘ ideal` reduces by
`∘-wireᴹ` to the simulator with its interface renamed and its own state, so the
ideal-with-simulator side is a *concrete machine with a readable state*, which
is what the closed game models directly.

Unlike the hash-then-forward toy, `real` is deliberately **not** `≈ᴹ` to that
composite — the emulation is approximate, and the whole point is the size of
the difference.

## The simulator

`Proc Lkᴵ Advᴵ`, three states, and its log IS the oracle's table (every oracle
query in the ideal world goes through it):

* `queryᴬ x` → relay `hashˢ x`; the answer is logged and passed up as `ansᴬ`.
* `commitᴬ c` → `extract c` reads the bit of the **unique** preimage of `c` in
  the log, `false` at none or at several; `commitˢ` that bit to `F_com`.
* `openᴬ b r` → relay `hashˢ (b ∷ r)`, then `openˢ` iff the digest is `c` **and**
  `b` is the extracted bit, `failˢ` otherwise.

## The flags, and their potentials

The two games differ exactly at an opening the receiver accepts and the
simulator will not deliver: `H(b ∷ r) ≡ c` with `b` not the extracted bit.
`Examples.ROCommitment.Game.agree-off` shows the two flags already cover it,
through the invariant `Pins c e t` — *every* preimage of `c` in the table starts
with `e` — which is the one piece of combinatorics the argument needs:

| flag | potential | bound | established by |
|---|---|---|---|
| `dup (answers t)` — a repeat in the oracle's ANSWER log | `Uniform.Duplicate.Φ` | `(q² + q)·2⁻ᵏ` | `Potential.collision-cert`, verbatim |
| a fresh sample landing on the outstanding digest | the indicator | `q·2⁻ᵏ` | `Potential.rare-cert` + `guess-drift`, verbatim |

`Pins` is *established* at `commitᴬ` by `pins-extract`, which needs a
duplicate-free answer log — that is why the birthday flag is the first one —
and *preserved* by `pins-∷` across a sample that misses `c` — which is why a
sample that hits it is the second. At the opening `pins-lookup` reads it off:
the point just fetched is in the table (`fetch-bis` hands that back explicitly,
because the `with` on the table lookup would otherwise throw it away), and its
answer is `c`, so its first bit is the extracted one.

**The fixed-secret caveat does not bite.** `docs/ro-game-hop.md` records that a
secret already determined by the state is one the next query hits with
probability 1, so `RareRaise` needs the point drawn lazily. Here the point is
the oracle's own fresh sample, drawn *at* the query by `fetch`, and the flag is
raised by the kernel's own comparison against the stored digest — exactly the
shape `guess-drift` discharges. Nothing is pre-sampled anywhere.

## The bound proved

`Examples/ROCommitment/Game.agda:extraction-bound`:

```agda
extraction-bound : (m : ℕ) (d : Strat Q R) → asks≤ m d
                 → ∣ Pr₁ (runWith respI sI₀ d) -ℚ Pr₁ (runWith respR sR₀ d) ∣ℚ ≤ℚ ε m
  where ε m = fromℕ (m * m + m) *ℚ inv-pow-2 k  +ℚ  fromℕ m *ℚ inv-pow-2 k
```

i.e. **`(m² + m)·2⁻ᵏ + m·2⁻ᵏ`** for every adaptive adversary of at most `m`
activations, at either world's own initial state. `Asymptotic.εᶜ` merges the two
numerators into `(m² + 2m)·2⁻ᵏ` and `Asymptotic.εᶜ-negligible` proves
`NegligibleBound εᶜ` at the identity schedule, the digest length being the
security parameter.

`Examples/ROCommitment/Test.agda:bounded` instantiates it at `k = 3` against a
live adaptive three-query attack — query the oracle, commit at the answer it
got, open at the same pair — which is what says the quantifier is inhabited by
an adversary that reaches the opening and not only by ones that stop first.

## Reused verbatim, generalized, new

| piece | status |
|---|---|
| `GamePlaying.Coupling.FLGP`, `badProb-bounded` | verbatim, through `hop-bound` |
| `GamePlaying.Hop.runWith-bisim`, `hop-bound` | verbatim, two `StepBisim` instances |
| `Potential.collision-cert`, `KeepOrSample` | verbatim |
| `Potential.rare-cert`, `RareRaise`, `guess-drift` | verbatim |
| `Uniform.Duplicate.dup`, `Φ`, `Φ-keep`, `Φ-fresh`, `Φ-init` | verbatim, via `collision-cert` |
| `Approximate.Decay.negligibleBound-inv-pow-2` | verbatim |
| `UC.QueryBound.Exact.Ledger`, `UC.QueryBound.Certified` | verbatim |
| `UC.Model.Seal.gradedᵒ`/`procᵒ` | verbatim |
| **`GamePlaying.Potential.∨-cert`** | **generalized — new, generic, beside its two siblings** |
| `Examples.ROCommitment.Extraction` | new: `extract`, `Pins` and its three lemmas |
| `Examples.ROCommitment` | new: the interfaces and the three machines |
| `Examples.ROCommitment.Game` | new: the two games, the coupling, the bound |
| `Examples.ROCommitment.UC` | new: the images, `Certified 2`, the two exact ledgers |
| `Examples.ROCommitment.Asymptotic` | new: the merged ε and its negligibility |
| `Examples.ROCommitment.Test` | new: the acceptance instance |

`∨-cert` is the only change to an existing module and it is additive: two flags,
two certificates, the potentials added and the bounds added. A binding argument
needs it because its bad event is a disjunction; nothing in it mentions a
commitment, an oracle or this example.

## Exact query accounting

`Examples/ROCommitment/UC.agda`, two weightings of the same
`UC.QueryBound.Exact` ledger over the simulator's own step:

| statement | `δ` | `cost` | ledger | reading |
|---|---|---|---|---|
| `sim-hash-count` | `hashes` | `points` | constantly 0 | exactly one oracle relay per adversary message that names a point, with **no residual at all** |
| `sim-message-count` | `downward` | `perMessage` | 1 at `checkˢ` | one downward message per query, one per commitment, two per opening |

`simCert : Certified 2 simulator` is the matching amortised ceiling and
`simQB : QB 2 simulator` crosses it to the model.

**A deviation from the brief, stated plainly.** The brief asks for "exactly one
downward oracle query per adversary oracle query and **none otherwise**", i.e.
a simulator that answers the opening from its log without querying. That
simulator is *not* what is implemented here, and the reason is a real
obstruction rather than a convenience:

> If the simulator does not query at the opening, then in the REAL world the
> receiver samples `H(b ∷ r)` and the oracle's table gains that entry, while in
> the IDEAL world it does not. The two tables then differ by one lazily sampled
> value, and a later adversary query of `b ∷ r` returns it on one side and a
> fresh uniform on the other. The values agree in distribution, but only after a
> *deferred-sampling* bisimulation — the ghost-table argument
> `Examples.MerkleDamgard.Core.ideal-marginal` runs, which is the single
> largest proof in that file. Off the bad event the two are **not** pointwise
> equal, so `Coupling.FLGP` does not reach it: the real side's value is the one
> the opening rejected, the ideal side's is unconstrained.

Querying at the opening keeps the two tables identical step for step, which is
what makes both `StepBisim` instances one case analysis each. The cost is one
extra oracle relay per opening message, and the accounting above states it
exactly rather than bounding it. The log-only simulator is recorded as a
residual below.

## Modules

All checked with `pagda --useUntracked false check … -- +RTS -M8G -H1G -RTS`,
rc=0 and an empty
`ModuleDoesntExport|UselessPublic|UselessPrivate|DuplicateUsing|error:|Failed to solve|Heap exhausted`
gate; the warm column is a single-`Checking`-line run.

| module | LOC | warm | rule-5 budget |
|---|---|---|---|
| `Examples.ROCommitment.Extraction` | 120 | 8.3 s | 90 s |
| `Examples.ROCommitment` | 214 | 9 s | 113 s |
| `Examples.ROCommitment.Game` | 595 | 8 s | 209 s |
| `Examples.ROCommitment.UC` | 266 | 10 s | 126 s |
| `Examples.ROCommitment.Asymptotic` | 52 | 6 s | 73 s |
| `Examples.ROCommitment.Test` | 45 | 6 s | 71 s |
| `GamePlaying.Potential` (+38) | 199 | 9 s | 110 s |

## Not delivered, precisely

### 1. The UC-level ε-statement — the whole of it

The closed bound is a `Dist-ℚ` statement about two reactive kernels. The UC
statement the consolidation plan's §3.3 asks for is about the *observation of a
composite* in the sealed model, and the two do not meet. At one level it reads:

```agda
raw-emulation :
    (W : Channel)
    (Et : T₀ W (T₀ (ifaceᵒ Advᴵ) (ifaceᵒ Honᴵ)) ⇒ Ωᵒ)
    (m  : 𝟘ᵒ ⇒ T₀ W (ifaceᵒ Resᴵ))
    {c c′ : ℕ} → QB c Et → QB c′ m
  → Obs ((Et ∘ T₁ᵒ W realᵒ) ∘ m)
    ≈ₚ[ εᶜ k (ctxBudget c c′) ]
    Obs ((Et ∘ T₁ᵒ W (sub simᵒ ∘ idealᵒ)) ∘ m)
```

with `simQB : QB 2 simulator` and `εᶜ-negligible : NegligibleBound εᶜ` as the
other two components of the plan's witness form. The two components ARE
delivered; the relation is not. Four things stand between them, in order of
increasing cost:

**(a) `plug-runᵍ`.** `docs/hash-forward.md` item 1 prices this at "`unprocᵒ-∘`
twice and probably cheap":

```agda
plug-runᵍ : {A B X : Iface} (f : Proc A (X ⊗ᴵ B)) (a : Proc unitᴵ X)
            (w : Proc unitᴵ A) (e : Strat (Neg B) (Pos B))
          → obs (tv₁ (ifaceᵒ X) (gradedᵒ f) (auditTest B e ∘ T₁ (ifaceᵒ X) (sub (procᵒ a))))
                auditClose
            ≈ₚ runᴹ ((subᴵ′ a 𝒫.∘ f) 𝒫.∘ w) e
```

**(b) A three-party adequacy.** `UC.Seam.Adequacy.adequacy` is stated for
`Proc unitᴵ B` — an environment above and nothing else. With an adversary
machine plugged at the grade and a resource plugged below, the closed system is
three-party, and the induction `play-run` carries has to be redone with two
loops rather than one:

```agda
adequacyᵍ : (A B X : Iface) (f : Proc A (X ⊗ᴵ B)) (a : Proc unitᴵ X)
            (w : Proc unitᴵ A) (d : Strat (Neg B) (Pos B))
          → runᴹ (pairedᴹ B d ((subᴵ′ a 𝒫.∘ f) 𝒫.∘ w)) (ask tt out)
            ≈ₚ runᴹ ((subᴵ′ a 𝒫.∘ f) 𝒫.∘ w) d
```

**(c) No concrete resource.** `Resᴵ` is an interface. The game fixes a lazily
sampled oracle and a one-shot cell; the machine layer has no `Proc unitᴵ Resᴵ`
implementing them, and `Examples.RandomOracle`'s oracle is an `SFunᵉ` over
`Dist-ℚ`, not a `Proc` over `Dₚ`.

**(d) The two probability layers do not meet at these machines.** The UC cone
runs on `Dₚ` (`ProbabilisticLogic.Dp`, the rational probabilistic delay monad)
and the game cone on `Dist-ℚ`. The one bridge, `Protocol.Machine.Agree.prAgree`,
is stated at `Protocol unitᴵ B` — a LAYER-1 protocol image — and
`hash-forward.md` item 5 explains why `real` is not one and cannot be made one
without redoing the trace argument. So there is presently no route from
`runᴹ (…)` in `Dₚ` to `runWith respR sR₀` in `Dist-ℚ` for these machines at all.
The missing statement is:

```agda
closed-kernel : (oracle : Proc unitᴵ Resᴵ) (a : Proc unitᴵ Advᴵ)
                (d : Strat (Neg Honᴵ) (Pos Honᴵ)) (q : ℕ) → asks≤ q d
              → Pr≤ q (runᴹ ((subᴵ′ a 𝒫.∘ real) 𝒫.∘ oracle) d)
                ≡ Pr₁ (runWith respR sR₀ (compile a d))
```

for a `compile` turning the two plugged machines into one `Strat Q R`. Even
with (a)–(c) in hand this is the substantive item: it is
`Examples.MerkleDamgard`'s `run-Sys`/`runFrom-kernel` argument, but across the
`Dₚ`/`Dist-ℚ` boundary rather than inside `Dist-ℚ`, and `prAgree`'s two nested
`Stable` inductions are what it would have to be rebuilt from.

(a)–(d) together are larger than the rest of this branch, which is why steps 1,
2 and 4 are delivered in full and step 3 stops at its two provable components.

### 2. The log-only simulator

Recorded above under the exact accounting. The residual is the deferred-sampling
identification:

```agda
defer : (t : Tbl) (x : Pt) (m : Com) (f : Bool) (d : Strat Q R)
      → Pr₁ (runWith respI (t , m) d)
        ≡ Pr₁ (runWith respI′ ((x , h) ∷ t , m) d)   -- averaged over a fresh h
```

i.e. "an unread lazily sampled entry is invisible", which is
`MerkleDamgard.Core.ideal-marginal`'s ghost argument in its own right. With it,
the simulator could answer the opening from the log alone and the accounting
would read exactly one relay per adversary oracle query and none otherwise.

### 3. No `≤UC[ c ]`, no `≤UC`

`UC.Seam.Graded.≤UC[]ᵍ` and `UC.Graded.≤UCᵍ` consume a `Factors` — an exact
machine equality — which is precisely what an approximate emulation does not
have. Nothing here weakens them; they simply do not apply. `simQB` is produced
and is the input `≤UC[]ᵍ` would take, so an ε-carrying analogue of `_≤UC[_]_`
(which does not exist: `UC.Seam.Audit._≤UC[_]_` packages an exact `≈ℰᶜ`) would
drop straight in.

### 4. The hiding half

The brief is the extraction half only. Hiding — a corrupted receiver, the
commitment indistinguishable from a fresh uniform until opened — is
`docs/ro-game-hop.md`'s first bullet and would reuse `rare-cert` at the SAME
`guess-drift`, with the lazily-drawn secret the caveat there is about. It shares
the interfaces and the resource of this branch and nothing else.

### 5. No family over `k`

`Examples.ROCommitment` and its cone are parameterized by `k`, and
`Asymptotic.extraction-boundⁿ` quantifies over it, so the levelwise statement is
there. What is absent is the FAMILY packaging — `UC.Asymptotic.Family`'s
`Systems`/`_≈ᶠ[_]_` are stated at `closedᵒ (morphism (R n))`, the trivial grade
at protocol images, and the plan's step 3 (generalizing them to graded semantic
morphisms) is scheduled separately and deliberately untouched here.

## Against the consolidation plan's architectural decisions

* **Decision 1** — no new relation on top of `_≈ᵁ_`/`_≤UC_`; the ε lives in
  `GamePlaying`, where it already did.
* **Decision 2** — the only absorption is `sub simᵒ ∘ idealᵒ`, the presheaf's
  own action; nothing new was defined for it.
* **Decision 3** — no `Simulator`, `ClosingContext`, `MonitoredExperiment` or
  `Monitor` record, and no new category. The branch adds no record at all: the
  simulator is a plain `Proc Lkᴵ Advᴵ`, the certificates are `UC.QueryBound`'s
  existing `QBᵢ`/`QEᵢ`, and `∨-cert` inhabits `GamePlaying`'s existing
  `SuperCert`.
* **Decision 4** — `Strat` untouched; `Test`'s attack is ordinary finite syntax.
* **Decision 5** — query certificates stay standalone; `UCSetup` and `Budget`
  are untouched, and the quantitative witness (`εᶜ-negligible`) is kept
  explicitly beside the certificate rather than folded into a relation.
* **Decision 6** — no observation was added or changed.
* **§3.3** — the quantitative statement is a relation on concrete morphisms with
  an explicit ε and explicit certificates, and the two components that do not
  need the missing bridge are delivered as such.

## Nothing was weakened

No pre-existing statement was edited. `GamePlaying/Potential.agda` gains
`∨-cert` beside `rare-cert` and `collision-cert` (and `proj₂`/`_,_` in one
import); `CategoricalCrypto.agda` and `UC.agda` gain inventory entries and
`open import` lines. `UC/Asymptotic/Family.agda` is untouched, as are
`Abstract2*`, `UC/Robust*`, `UC/Model/Bridge.agda` and `UCSetup.agda`.
