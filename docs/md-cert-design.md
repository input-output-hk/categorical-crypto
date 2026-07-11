# Design: discharging `md-cert` (the MD birthday certificate)

Target: construct the one remaining cryptographic postulate of
`Examples/MerkleDamgard.agda`,

```agda
md-cert : SuperCert C.realK proj₁ (false , [] , []) bound
```

i.e. exhibit an invariant `Inv`, a potential `φ`, and the eight certificate
fields.  The adaptive/game content is already proven (`badProb-super`); every
obligation below is per-step and non-adaptive.

Notation: a state is `(f , sc , sg)` (flag, compression table, ghost table);
`k` = blocks per message (`NonZero k`); the *pool* of a table is
`ivEntry ∷ interior sc` — the `{IV} ∪ interior-outputs` value list whose
duplicate pairs `collC` counts.

```agda
collC : Comp.Table → ℚ
collC sc = Comp.state-collisions (ivEntry ∷ interior sc)

pool : Comp.Table → ℕ                    -- = length (ivEntry ∷ interior sc)
pool sc = suc (length (interior sc))
```

## 1. The potential

```agda
φ m (f , sc , sg) =
  collC sc +ℚ (triangle (pool sc + m * (k ∸ 1)) -ℚ triangle (pool sc)) *ℚ inv-pow-2 n
```

current collisions + birthday budget for the ≤ `m·(k−1)` interior samples the
remaining `m` queries can draw.  (Only *interior* calls enlarge the pool: the
final call's entry has `idx = len`, is filtered by `interior`, and never enters
`collC` — this is why the budget is `k−1` per query, comfortably inside
`bound m = triangle (m * k) · 2⁻ⁿ`.)

**Key discovery of this design pass — `φ` is an *exact* martingale along the
walk.**  For the one-call potential `ψ_C sc = collC sc + (C − triangle (pool sc))·2⁻ⁿ`
(any constant `C`):

* **interior miss** (fresh `hm`): `collC ((key , hm) ∷ sc) ≡ collC sc +
  count-matches (pool-list sc) hm` (definition-chasing + δ-symmetry), and
  `E[count-matches (pool-list sc) hm] ≡ pool sc · 2⁻ⁿ` is **exactly the proven
  `RandomOracle.E-collisions`**; meanwhile `triangle (pool + 1) − triangle pool
  ≡ pool` cancels it.  `E[ψ_C ∘ step] ≡ ψ_C`.
* **final miss**: pool and `collC` unchanged (final entries filtered) — `ψ_C`
  unchanged *whatever* is sampled.
* **hit**: state unchanged.

So the walk lemma is an `≡`-style induction (the `≤` enters only when a *hit*
skips budget, via `triangle`-monotonicity), in the exact same style as the
already-proven `walkR`/`detach`:

```agda
walk-φ : ∀ m sc h bs idx
       → E (walk sc h bs idx) (λ w → φ' m (proj₁ w))
       ≤ℚ collC sc +ℚ (triangle (pool sc + intCalls bs + m * (k ∸ 1))
                        -ℚ triangle (pool sc)) *ℚ inv-pow-2 n
  -- φ' m sc' = the sc-component of φ;  intCalls bs = length bs ∸ 1
```

Crucially the induction hypothesis quantifies over **all** states, so it moves
under `E` by plain `E-mono` — **no support reasoning anywhere in `φ-step`**.

Per-field verdicts on the `φ` side:

| field | discharge | needs |
|---|---|---|
| `φ-nn` | provable, no `Inv` | `0 ≤ δ/count-matches/collC` (sums of {0,1}); `triangle`-mono; `0 ≤ inv-pow-2 n` |
| `φ-step` | provable, no `Inv` | `walk-φ` + `E-collisions` + `ghost-erase`-style plumbing through `respB` (the ghost/`newAns` sampling is `φ`-constant, `E-const`); ℕ-arith `intCalls (toBlocks M) = k ∸ 1`, `(k∸1) + m(k∸1) = (suc m)(k∸1)` |
| `φ-init` | provable | `collC [] ≡ 0`, `pool [] ≡ 1`, `triangle 1 ≡ 0`, `triangle`-mono + `1 + m(k∸1) ≤ m·k` for `m ≥ 1` (equality `0 ≤ 0` at `m = 0`) |
| `φ-bad` | trivial from `Inv` component (I1) | — |

## 2. The invariant

```agda
Inv (f , sc , sg) =
    (I1)  f ≡ true → 1ℚ ≤ℚ collC sc
  × (I4)  UniqueKeys sc
  × (f ≡ false →                         -- pre-corruption structure:
      (I3)  ∀ (M , h) ∈ sg → ChainIn sc IV (toBlocks M) 1 h
    × (I5)  ∀ final entry e ∈ sc → ∃ (M , h) ∈ sg with e the final call of
            that recorded chain)
```

`ChainIn` is the positional chain predicate (`lookup (pack h b idx) ≡ just hm`,
recursively), `UniqueKeys` = no duplicate keys (inserts only happen on misses).
Two deliberate design choices:

* **I1 is stated in ℚ (`1 ≤ collC`)**, not "a collision exists" — this bakes
  the integrality step (`collC ≠ 0 ⇒ collC ≥ 1`, from `collC` being a sum of
  {0,1}-δ's) into the invariant once, so `φ-bad` is a projection.
* **I3/I5 are conditional on `f ≡ false`.**  This is what makes them *true*:
  a flagged-new query records a ghost value `u` unrelated to the chain, so the
  unconditional versions are false — but the flag is monotone, so along any
  still-unflagged history every recording was unflagged and faithful.

`inv₀` is immediate (flag false, tables empty).

## 3. `pres` — preservation, branch by branch

Support machinery first: `Preserved` is an `OnSupport` statement, so we need a
small **combinator kit** proved from the concrete `List⁺`-representation:
`OnSupport-return`, `OnSupport-bind`, `OnSupport-Dmap`, plus `All` over
`⁺++⁺`/`scale-ℚ` (scaling changes weights, not points).  Mechanical.

Then a **walk-support lemma** (the only support-heavy induction): on the
support of `walk sc h bs idx`,

1. `sc' ≡ (new entries) ++ sc`, each new key previously missing ⟹ `UniqueKeys`
   preserved, existing `ChainIn`/lookups preserved (fresh keys don't shadow),
   `collC` monotone (`collC (e ∷ s) ≥ collC s`);
2. the walked prefix of `M`'s own chain is `ChainIn`-embedded in `sc'`, with
   its per-position keys/values exposed;
3. **replay determinism**: if `ChainIn sc IV (toBlocks M) 1 h` and
   `UniqueKeys sc`, the support is the singleton `(sc , h , true)`.

Now the branches of `respB` (from a state satisfying `Inv`):

* **`f ≡ true`** (either branch): `f' ≡ true`; I1 persists by `collC`
  monotonicity (1); I3/I5 vacuous.  Easy.
* **repeat, `f ≡ false`**: I3 gives the embedded chain; (3) forces full replay,
  `hR ≡ h`, so the consistency check passes and `f' ≡ false` — the flag-raise
  case has *empty support*.  No new entries ⟹ all components persist.
* **new, `f ≡ false`, final call missed**: `f' ≡ false`; walk-support gives
  I4 and persistence; recording `(M , hR)` with the freshly embedded chain
  re-establishes I3; the new final entry is `M`'s own ⟹ I5.
* **new, `f ≡ false`, final call HIT** — *the descent, the one real lemma*:
  need `1 ≤ collC sc'`.  Proof sketch, fully constructive:
  - Decide `collC sc' ≟ 0`.  If nonzero, done (integrality).
  - If zero: pool values pairwise distinct, so **values determine interior
    entries** (value-injectivity).  The hit final key belongs (I5) to a
    recorded `M'` with embedded chain (I3); `M ∉ sg ⟹ M ≢ M'`.  The two
    chains share the final key, hence value at position `k−1` and block `b_k`.
    Descend positions `j = k−1 … 1`: shared value at `j` + distinctness ⟹
    *same entry* at `j` ⟹ shared key ⟹ shared value at `j−1` *and shared
    block* at `j`; at `j = 0` both values are `IV`.  Hence all blocks agree,
    `toBlocks M ≡ toBlocks M'`, and **`toBlocks` is injective**
    (`chunk`/`take-drop` reconstruction) ⟹ `M ≡ M'` — contradiction.
  - The descent is a reverse induction over the shared suffix; formalize on
    reversed block lists (or an accumulator-style `ChainIn` view).

## 4. Lemma inventory, effort, build order

| # | group | effort | risk |
|---|---|---|---|
| C | triangle/ℕ/ℚ arithmetic, `0 ≤ inv-pow-2` | S | low |
| B | δ-sym; `0 ≤`/integrality/monotonicity of `count-matches`/`collC`; `collC ≡ 0 ⇒` distinct pool | M | low |
| D | `walk-φ` + `respB` plumbing ⟹ **`φ-step`, `φ-nn`, `φ-init`** | M–L | low (walkR/detach-style; `E-collisions` proven) |
| A | `OnSupport` kit (bind/return/Dmap) from `RationalDist` internals | M | low-medium (internals spelunking) |
| E | `lookup-bs` semantics; fresh-insert preservation | M | low |
| F | walk-support (extension + trace + replay-singleton) | L | medium |
| G | descent + `toBlocks`-injectivity | L | **medium-high** (the one research-grade piece) |
| H | `pres` assembly; `inv₀`; record instance | M | low |

Recommended order: **C+B → D** (lands `φ`-side fields; can already refactor
`md-cert` into `pres`+`φ-bad`-only residuals) → **A → E → F → G → H**.
Estimated total ~900–1500 lines over 2–4 sessions; the only piece with genuine
formalization risk is G (reverse-induction bookkeeping), and its statement is
purely about deterministic table structure — no probability.

## 5. Pitfalls recorded (from the ideal-marginal experience)

* State every integrand lambda with an annotated domain; pass `E-bind`/
  `lookupᴰℚ-return` integrands explicitly (metas don't solve in `trans`-chains).
* No `with` on recursive paths — use forward-declared helpers taking the
  scrutinee as an argument (`detachC` pattern).
* Write with-branch chain endpoints in reduced form.
* Flag-order matters: keep checks as `check ∨ f` so `∨` reduces.
* `interior` filters by `idx <? len` from the *key*; final entries carry
  `idx = len = k` — the pool/`collC` invariance of final inserts is definitional
  modulo that filter step.
