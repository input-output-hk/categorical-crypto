# The RO game-hopping toolkit, hoisted out of Merkle–Damgård

2026-09-11, branch `game-hop` (off `protocol-rewrite` at `ceec075e`).

Merkle–Damgård was the only consumer of the random-oracle game-hopping argument, and
part of that argument was written inside it. This note says what moved, what the
generic pieces are, what a future RO-model commitment proof would instantiate, and
what is genuinely MD-specific and stayed put.

## What was already general (nothing to do)

`CategoricalCrypto.GamePlaying` already carried, parameterized over an arbitrary
reactive kernel, both halves of the ε-argument:

* `badProb-super` — the **supermartingale bound**: an invariant `Inv` preserved on
  support, plus a potential `φ` non-negative under `Inv`, ≥ 1 on bad states and
  non-increasing in expectation per query, bounds the bad-probability of any adaptive
  distinguisher by the initial potential. `SuperCert` bundles it and
  `badProb-bounded` reads off the bound.
* `Coupling.FLGP` — the **Fundamental Lemma of Game-Playing in coupled form**: one
  kernel emits the shared state and both answers, the ideal projection copying the
  real answer while the post-state is good. No side conditions.

So deliverable 1's first two bullets were a no-op: they are not MD-specific and never
were. What *was* buried in MD is everything that turns those two into a theorem.

## What was hoisted

### `CategoricalCrypto.GamePlaying.Hop`

```agda
  StepBisim : Type
  StepBisim = ∀ s s′ → s ≋ s′ → ∀ q (F : St × R → ℚ) (F′ : St′ × R → ℚ)
            → (∀ t t′ → proj₁ t ≋ proj₁ t′ → proj₂ t ≡ proj₂ t′ → F t ≡ F′ t′)
            → E (resp s q) F ≡ E (resp′ s′ q) F′

  runWith-bisim : StepBisim → ∀ d s s′ → s ≋ s′
                → Pr₁ (runWith resp s d) ≡ Pr₁ (runWith resp′ s′ d)
```

(inside `module _ (resp : St → Q → Dist-ℚ (St × R)) (resp′ : St′ → Q → Dist-ℚ (St′ × R))
(_≋_ : St → St′ → Type)`), and

```agda
  hop-bound : {ε : ℕ → ℚ} (respR : StR → Q → Dist-ℚ (StR × R))
              (respI : StI → Q → Dist-ℚ (StI × R)) (s₀ : St) (sR : StR) (sI : StI)
            → (∀ d → Pr₁ (runWith realK s₀ d) ≡ Pr₁ (runWith respR sR d))
            → (∀ d → Pr₁ (runWith idealK s₀ d) ≡ Pr₁ (runWith respI sI d))
            → SuperCert realK bad s₀ ε
            → ∀ m d → asks≤ m d
            → ∣ Pr₁ (runWith respI sI d) -ℚ Pr₁ (runWith respR sR d) ∣ℚ ≤ℚ ε m
```

(inside `module _ (bad : St → Bool) (respB : St → Q → Dist-ℚ (St × (R × R)))`, whose
`Coupling bad respB` supplies `realK`/`idealK`).

`runWith-bisim` is the generalization of MD's `ghost-erase` and `ideal-marginal`:
*both* are the statement "a projection of the coupling IS a reference kernel,
exactly", and both were proved by the same induction over the distinguisher with the
expectation-rewriting chain interleaved into it. The generic lemma carries the
induction; what a consumer owes is one query's statement, with the continuation
replaced by an arbitrary integrand and the induction hypothesis by the premise that
the two integrands cannot tell related outcomes apart. The relation `_≋_` is what
carries the ancillary state one side has and the other does not — a flag, a ghost
table.

`hop-bound` is the last step of every proof in this shape: FLGP (identical-until-bad)
composed with `badProb-bounded` (the supermartingale), transported along the two
marginal identifications. It is `indistinguishable`'s proof, minus MD.

### `ProbabilisticLogic.Distribution.Uniform.Duplicate` (n)

The duplicate flag and its birthday potential, oracle-free:

```agda
  Φ : ℕ → Log → ℚ
  Φ m L = bool→ℚ (dup L) +ℚ Γ (length L) m

  Φ-keep  : ∀ m L → Φ m L ≤ℚ Φ (suc m) L
  Φ-fresh : ∀ m L → E (uniform-Vec n) (λ h → Φ m (h ∷ L)) ≤ℚ Φ (suc m) L
  Φ-init  : ∀ m → Φ m [] ≤ℚ fromℕ (m * m + m) *ℚ inv-pow-2 n
```

plus `0≤Φ`, `dup⇒1≤Φ`, `memb`/`dup` and `indicator-≤`. `Γ-monoˡ` (a pool that starts
larger accumulates more) was added next to its siblings in `Uniform.Birthday` for
`Φ-init`.

### `CategoricalCrypto.GamePlaying.Potential`

The two ready-made certificates, each turning a per-query hypothesis into a
`SuperCert`.

**Generic collision / birthday.** Flag = a repeat in a log of uniformly sampled
n-bit values; bound `(m² + m)·2⁻ⁿ`.

```agda
  KeepOrSample : (St → Q → Dist-ℚ (St × R)) → (St → Log) → Set
  KeepOrSample resp log = ∀ s q (F : Log → ℚ)
    → (E (resp s q) (λ sr → F (log (proj₁ sr))) ≡ F (log s))
    ⊎ (E (resp s q) (λ sr → F (log (proj₁ sr))) ≡ E (uniform-Vec n) (λ h → F (h ∷ log s)))

  collision-cert : (resp : St → Q → Dist-ℚ (St × R)) (log : St → Log) (s₀ : St)
                 → log s₀ ≡ [] → KeepOrSample resp log
                 → SuperCert resp (λ s → dup (log s)) s₀
                     (λ m → fromℕ (m * m + m) *ℚ inv-pow-2 n)
```

This is `ChimericLedger.Birthday`'s argument **without the serialization layer**, and
it does come out simpler: the invariant is trivial (`Inv = λ _ → ⊤`) and `Φ-keep` /
`Φ-fresh` are unconditional. The ledger's `Stales` trick is **not** needed generically,
and the reason is worth recording: the ledger's bad event is *value destruction*, which
a coincidence only makes *possible*; its invariant exists to prove that implication
(a table hit at an accepted transaction cannot happen while nothing is stale), not to
run the potential. Here the flag **is** the bad event, so there is nothing to imply.
A consumer in the ledger's position keeps its own invariant and reuses `Φ-*`; a
consumer in the toy position gets the whole certificate for free.

**Fresh-point guessing.** Flag raised with probability ≤ ε per query, never lowered;
bound `m·ε`, at ε ≡ 2⁻ᵏ the `q·2⁻ᵏ` shape a hiding argument needs.

```agda
  RareRaise : (St → Q → Dist-ℚ (St × R)) → (St → Bool) → ℚ → Set
  RareRaise resp flag e = ∀ s q → E (resp s q) (λ sr → bool→ℚ (flag (proj₁ sr)))
                                ≤ℚ bool→ℚ (flag s) +ℚ e

  rare-cert : (resp : St → Q → Dist-ℚ (St × R)) (flag : St → Bool) (s₀ : St) (e : ℚ)
            → 0ℚ ≤ℚ e → flag s₀ ≡ false → RareRaise resp flag e
            → SuperCert resp flag s₀ (λ m → fromℕ m *ℚ e)

  guess-drift : ∀ k (f : Bool) (p : Vec Bool k)
              → E (uniform-Vec k) (λ r → bool→ℚ (f ∨ ⌊ r ≟ p ⌋))
              ≤ℚ bool→ℚ f +ℚ inv-pow-2 k
```

### One caveat that is real, not an artefact

A **fixed** secret `r` sitting in the state does not satisfy `RareRaise`, and no
per-state supermartingale can prove it does: `φ-step` quantifies over *all* queries at
*all* states under the invariant, and at a state that determines `r` the query `r`
raises the flag with probability 1. The information-theoretic content of "the
adversary does not know `r`" is not a property of a single state.

The standard fix is the one the statement above already encodes: sample the secret
**lazily**. The coupling draws the fresh point at the query that could hit it, exactly
as MD's coupling raises its flag by the kernel's own freshness checks rather than by
inspecting a pre-sampled table. With the draw inside the step, the drift is provably
2⁻ᵏ per query and `rare-cert` applies. A proof that wants a *fixed* `r` in the state
must either re-derive the bound by averaging over `r` at the top (a different lemma,
not a `SuperCert`) or hop first to the lazy game.

### Acceptance instances — `CategoricalCrypto.GamePlaying.Test`

* `LogMachine n` — a query idles or draws one fresh uniform sample into a log;
  `bounded : ∀ m d → asks≤ m d → badProb logK dup [] d ≤ℚ fromℕ (m * m + m) *ℚ inv-pow-2 n`.
* `GuessMachine k` — a query names a k-bit point, tested against a fresh uniform draw;
  `bounded : ∀ m d → asks≤ m d → badProb guessK id false d ≤ℚ fromℕ m *ℚ inv-pow-2 k`.

Both carry the certificate all the way through `badProb-bounded`, i.e. to an adaptive
bound, which is the thing that says the builders are usable rather than merely
well-typed.

## What an RO-model commitment proof would instantiate

Target: `commit m r = H(m ∥ r)` with `r` a secret k-bit opening, `H` the random oracle.

* **Hiding** — the coupling: real answers `H(m ∥ r)`, ideal answers a fresh uniform
  value independent of `m`; the two agree unless the adversary queries `m ∥ r`, which
  is the flag. Identify each projection with its reference kernel by `runWith-bisim`
  (two `StepBisim` instances, one per side — the ideal side being the interesting one,
  as in MD), bound the flag by `rare-cert` at ε ≡ 2⁻ᵏ with `guess-drift` discharging
  the drift (with `r` drawn lazily, per the caveat above), and assemble with
  `hop-bound`. No new induction and no new supermartingale.
* **Binding** — the flag is a collision in the oracle's answer log, so the potential is
  `collision-cert`'s: `(q² + q)·2⁻ⁿ`. What the commitment layer owes is `KeepOrSample`
  for its kernel (one fresh sample per oracle query — true for a lazily sampled RO, not
  true for MD, see below) and, if its bad event is "two openings of one commitment"
  rather than the raw dup flag, the implication from a coincidence to that event — the
  ledger's position, its own invariant.
* **Extraction** (the simulator observing the adversary's oracle queries) is **out of
  scope** here: nothing in this toolkit models a simulator, and `hop-bound` is a
  two-world statement. Extraction needs the UC layer, not the game-hop layer.

## What stayed MD-specific

* **`md-cert`'s invariant and potential.** MD's potential is a collision *count* plus a
  triangle budget (`φsc m sc = collC sc +ℚ Γ (pool sc) (m * (k ∸ 1))`), not an
  indicator; its `Inv` is the chain-forest invariant `MDInv` (UniqueKeys, Rooted,
  RecChains, OwnedLast) and the descent `walk-hit-collC`. None of that is a birthday
  potential in the generic sense, and it is not reusable: it is the combinatorics of
  *chaining*.
* **`KeepOrSample` fails for MD.** One MD query walks up to `k` blocks, so its log
  gains up to `k` samples per query — which is exactly why MD's budget carries the
  factor `m * (k ∸ 1)` and why `walk-φ` is an induction over the block list rather
  than a single drift step. Generalizing `collision-cert` to "at most `j` samples per
  query" would be a different lemma; MD would still not use it, because its flag is
  not the dup flag.
* **`walkR` / `detach` / `walk-φ`** — the chain-walk lemmas. They are about `walk`, a
  Merkle–Damgård-specific object.

What *did* move out of MD is the two inductions (`ghost-erase`, `ideal-marginal`) and
the final assembly (`indistinguishable`); all three statements are unchanged and their
proofs are now applications. A side effect: Core's warm typecheck dropped from ~34 s to
~14 s, because the expectation-rewriting chains are elaborated once each instead of
once per distinguisher clause.

## Recorded wish

`Examples/ChimericLedger/Birthday.agda` should be re-derived from
`Uniform.Duplicate`: its private `memb`/`dup`/`indicator-≤`/`length-Hs` and its
`φ`-arithmetic (`point-step`, the two `bound` branches) are `Φ`, `Φ-keep` and
`Φ-fresh` specialised to `Hs tbl` — the pool with `h₀` prepended, i.e. `Φ` at the log
`Hs tbl` rather than at `tbl`. The invariant (`Good`, `Stales`) and the
`badTotal`-vs-flag implication stay where they are; only the counting collapses. That
file is owned by another agent in this arc, so nothing was changed there. When it is
rewired, the two files should share one `dup` and the duplicate definitions should go.
