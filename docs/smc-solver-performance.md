# Performance of the APROP SMC solver

The `Categories.APROP.Hypergraph.Solver` decision procedure proves free-symmetric-monoidal
term equalities by

```agda
f ≈Term g  :=  soundness-full-wired (from-just (findIso ⟪ f ⟫ ⟪ g ⟫))
```

It is complete and axiom-free (`--safe`), but it does **not** scale. This note records what
the cost actually is, measured by `agda --profile=definitions`, and why.

## The measurement

A temporary probe (`ScaleProbe.agda`, since removed) timed the two phases separately —
`iso-k = from-just (findIso …)` (forces the *search* to evaluate) versus
`sound-k = soundness-full-wired iso-k` (the *correctness proof*) — while independently scaling
the two candidate cost drivers.

### Finding 1 — `findIso` is essentially free; all cost is in `soundness-full-wired`

In every case the `iso`/`findIso` definitions cost ≤ 146 ms (usually below the profiler's
threshold), while the `sound` definitions carried 100% of the visible time. This matches the
source: `searchIso` is a backtracking search over **edges** with fuel `nE_H × nE_J`, and the
coherence goals have 0–3 edges (the pentagon has *zero*). The search is never the bottleneck.

### Finding 2 — `soundness-full-wired` cost is the product of two steep axes

**Axis A — wire count** (trivial `id` round-trip, ~0 structural morphisms):

| wires | `soundness-full-wired` |
|------:|-----------------------:|
| 3     | 51 ms                  |
| 5     | 183 ms                 |
| 8     | 683 ms                 |

≈ `k^2.5`. The decoder / iso-invariance walks every wire carrying the `subst`/transport/UIP
bookkeeping (`Verify` also scans every vertex with decidable equality + `FlatView`).

**Axis B — structural-morphism count** at a *fixed* 3 wires (chaining `α⇐ ∘ α⇒` pairs, which
equal `id` but grow the term):

| associator pairs | `soundness-full-wired` |
|-----------------:|-----------------------:|
| 1                | 541 ms                 |
| 4                | 3.4 s                  |
| 8                | 6.7 s                  |

The striking datum: a **single** associator pair at 3 wires costs 541 ms — **10×** the bare
3-wire identity (51 ms). Each `α` drags in the heavy per-constructor `bridge`-α decode machinery
(`Soundness/Discharge/BridgeAlphaFormCompound`, a pentagon + well-founded recursion); each `σ`
pulls in the even-heavier σ-block-hexagon family (`Sub/SigmaBlockHexagon`, …).

## Root cause

The solver's *correctness route* re-runs the entire soundness development — the algorithmic
decoder, the iso-invariance, and the per-constructor `bridge`/decode machinery — at typecheck
time, and that machinery's cost is **multiplicative in (wire count) × (structural-morphism
count)**, with associators and braids being individually expensive.

This is not a search blowup or a complexity bug; it is the **decode/transport tax** — the same
accidental complexity catalogued in `size-reduction-strategies.md` — showing up at *use* time
instead of *proof* time.

## Why the pentagon is fine but `GConstruction.assoc'-coherence` OOMs

- Every test in `Solver/Tests.agda` uses `X = Fin 3` and a handful of small associators — minimal
  on *both* axes. `test-pentagon`/`test-hexagon` are cheap for that reason, not because
  associator coherence is intrinsically cheap.
- `GConstruction.assoc'-coherence` is large on *both* axes: ≈ 8 wires (4 objects × the ± pair
  components) × ≈ 50 structural morphisms (many `α` *and* `σ`) + 3 generator edges. The product
  lands in the multi-GB / hundreds-of-seconds regime: heap-exhausted at 9 GB / 381 s, OOM-killed
  at 14 GB / 50 s. (The `findIso`/transport *wiring* for that goal is correct — A built it and
  confirmed `⟦lhsᵗ⟧₁ ≡ goalLHS` definitionally; it is purely the proof *evaluation* that blows up.)

## Head-to-head: APROP solver vs matrix solver, with an `opaque` fairness control

The APROP solver's cost has *two* per-use components: (a) normalizing the soundness proof, and
(b) the `findIso ⟪f⟫ ⟪g⟫` search. To isolate (b), wrap `soundness-full-wired` in `opaque` — so a
use site sees only its *type*, exactly as the matrix solver's `solveSM` sees only the (postulated)
`matrix-faithful`. This is the fair control.

With `opaque`, `soundness-full-wired` itself drops to **16 ms** (one-time), and the per-test cost
becomes pure `findIso`. Comparing that against the matrix solver's decide step
(`diagram lhs ≡ diagram rhs` by `refl`), same equations, `X = Fin 3`, per-definition profile:

| Fin-3 equation | APROP `findIso` (soundness `opaque`) | matrix `diagram`+`refl` | ratio |
|---|---|---|---|
| pentagon | 1272 ms | 78 ms | ~16× |
| hexagon | 1020 ms | 42 ms | ~24× |
| σ∘σ | 247 ms | <~10 ms (below threshold) | >25× |
| triangle | 201 ms | — (probe hit an unrelated `unit` overload) | — |
| ⊗-∘-dist | 162 ms | **`refl` FAILS** (needs `≈D`) | n/a |

**So yes — the matrix representation's decide primitive is genuinely ~16–25× faster** than the
hypergraph `findIso`, *and* the `opaque` control confirms the user's intuition that the
soundness-normalization half of the APROP cost is avoidable (it moves to a one-time cost). What
remains expensive in the APROP solver is `findIso` + `⟪_⟫` + the `decode-rel-resp-iso` machinery —
the hypergraph round-trip's decide step — which is intrinsically heavier than computing a Bool/Set
matrix and comparing.

**Three honest caveats** (so this is not a clean "matrix wins"):
1. **The matrix `refl`-decide only covers definitionally-equal-diagram cases** (pure structural,
   where labels line up: pentagon/hexagon/σ∘σ). For label-permuted cases — `⊗-∘-dist` with two
   generators, σ-naturality — `refl` *fails*; they need `≈D` with an explicit permutation witness,
   which in the current tests is **hand-written**. `findIso` **automatically searches** for that
   permutation for *all* cases. So part of the matrix speed is that, on these cases, it does a
   definitional check rather than a search; a *complete automated* matrix solver must automate the
   `≈D` search (`Reflect`'s `readPerm`/`sortSwaps`), whose cost is **not measured here** (likely
   cheap — `readPerm` reads the permutation directly rather than back-tracking like `findIso` — but
   unverified).
2. **`matrix-faithful` is postulated** (the APROP path is fully proven, `--safe`). For a *speed*
   comparison this is the correct control — a proven `matrix-faithful`, applied via
   `F-resp-≈ freeFunctor`, would (like `opaque` soundness) add no per-use cost — but the matrix
   solver is not yet sound end-to-end.
3. `opaque` removes the soundness-normalization cost but **not** `findIso`. So `opaque` alone would
   *not* make `GConstruction.assoc'-coherence` tractable — its blow-up is dominated by `findIso`/`⟪_⟫`
   over an 8-wire × ~50-morphism term, which `opaque` does not touch.

(`opaque`-ing `soundness-full-wired` is, separately, a legitimate ~free improvement: it makes every
downstream *use* of the theorem cheap without weakening it. Worth keeping independent of any solver
work.)

## Implication

The fix is the same as for shrinking the soundness proof itself: a real coherence solver
(`size-reduction-strategies.md`, Lever 1 / `braided-coherence-solver.md`, Option 2) or a
strict-monoidal representation (Option A) would collapse exactly the decode/transport normal forms
that explode here. The head-to-head confirms the *representation* matters: the matrix/normalization
decide step is an order of magnitude cheaper than the hypergraph round-trip, so a finished direct
solver would be both fast and (unlike the APROP one) non-circular. Until then, the APROP solver is
practical only at roughly pentagon/hexagon size — and should at minimum be `opaque` at the top.
