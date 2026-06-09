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

## Are the two algorithms actually different? (2026-06-09)

The matrix variant and the hypergraph `findIso` solve the *same* problem — decide whether two
diagrams are equal, i.e. whether the two wirings agree up to relabelling. But the algorithms read
very differently:

- **`findIso` (hypergraph) — boundary-seeded search + verify.** `Solver/Search.agda`: seed `φ` from
  the `dom`/`cod` correspondence, then a backtracking DFS (`matchEdge` enumerates shape-compatible
  candidate J-edges → recurse → backtrack; fuel `nE×nE`), then `Verify` checks every `≅ᴴ` invariant
  with decidable equality. It *constructs and verifies an isomorphism*.
- **Matrix — deterministic canonical form.** `Reflect.agda`: `isMinimal` peels generators in
  dependency order (a topological sort), and `swapAll`/bubble-sort decomposes the wiring permutation
  into adjacent transpositions; equality is then a literal comparison of the canonical Bool/Set
  matrix. It *normalizes and compares*. No search.

**…but on the actual input class they nearly coincide.** Every `⟪f⟫` is **monogamous and acyclic**
(each wire produced once / consumed once; the producer/consumer relation is a strict order). For
such a graph, seeding from the boundary makes propagation **forced**: following each edge's
incidence determines the next vertex pairing, so `matchEdge` almost never has a real branch — hence
FindIso's own note, *"complete in practice on `⟪_⟫`-translated graphs."* So `findIso`'s search
**degenerates to deterministic, boundary-seeded propagation** — the same topological canonicalization
the matrix does explicitly. The genuine difference is therefore **representational, not algorithmic**:
the matrix is a flat array (cheap to build and compare); `findIso` threads `Fin`-indexed
vertex/edge lists and builds the `≅ᴴ` record incrementally, then re-scans it in `Verify` with
decidable equality + UIP + `FlatView`.

**Is there clear evidence which is better?** The head-to-head (above) gives the only hard numbers:
the matrix decide step is ~16–25× faster on the shared `Fin-3` equations. But that gap is the
**representational** one (flat matrix vs hypergraph-list + `≅ᴴ`-proof-via-`Verify`) — *not* a
search-vs-no-search result, because on these (small, mostly edge-free) graphs `findIso` does not
backtrack. There is **no evidence of an algorithmic (backtracking) advantage** either way, and it is
hard to manufacture: monogamy is exactly what kills the branching that would distinguish a search
from a canonical form. So the honest verdict is *the matrix representation is cheaper to compute and
compare; the underlying algorithms are essentially the same deterministic topological canonicalization.*

**Could we port the matrix algorithm to hypergraphs, keeping its characteristics?** Yes — and the
characteristic worth porting is the **explicit flat canonical form + literal comparison**, replacing
`findIso`'s construct-and-`Verify`. The ingredients already exist in the soundness development:

- a canonical **topological edge order** — `decode`'s "natural order", the linear-extension /
  no-inversion machinery (`Combinatorics/LinearExtension`, Lemma C, `EdgeDependency`);
- the **permutation layer** — `PermuteCoherence` (`FinBij`/`eval`), the analogue of the matrix's
  bubble-sort transposition decomposition.

So a canonical-form hypergraph decision procedure = *canonically label `⟪f⟫` and `⟪g⟫` via the
topological order (intrinsic to the graph, with a fixed tie-break for independent edges), compare
the flat labelled incidence, and read the bijection off the two relabellings* — no search, no
incremental `≅ᴴ`-proof. This is the standard **DAG canonical-labelling** approach (polynomial,
because the graphs are acyclic — unlike general graph canonical labelling), and it would inherit the
matrix's representational speed-up directly on the hypergraph side. The one careful part is the
tie-break for automorphic/independent edges (the matrix sidesteps it via the term-induced order; an
intrinsic labelling must pick a canonical representative) — but that is exactly what the
no-inversion / linear-extension lemmas already reason about.

**Edge-scaling probe (2026-06-09).** Profiling `from-just (findIso ⟪f⟫ ⟪f⟫)` for one generator
`g : a → a`, increasing the edge count:

| N edges | chain `g∘…∘g` | parallel `g⊗…⊗g` |
|--------:|--------------:|------------------:|
| 4       | 95 ms         | 22 ms             |
| 8       | 746 ms (7.9×) | 96 ms (4.4×)      |
| 16      | 8351 ms (11.2×) | 581 ms (6.0×)   |

Two findings:
- **No exponential backtracking.** The *parallel* case — `N` independent edges with the *identical*
  label/shape, exactly the configuration that would make an iso-search branch — is the **cheaper**
  one and scales with the **lower** exponent (~N^2.3) than the chain (~N^3). If `findIso` were
  back-tracking over the `N!` candidate matchings of identical parallel edges it would blow up
  exponentially; instead it is sub-cubic. So the boundary seed + monogamy do kill the branching,
  confirming the "deterministic in practice" claim — the algorithm is **not** pathological.
- **But the per-size cost is super-linear (~N²–N³), and it is representational.** The cost is *not*
  search; it is building `⟪_⟫` (the *pruned* composition machinery `hComposeP` — `count-non`/`remap`
  over growing vertex lists, the same pruned-`∘` cost seen elsewhere) plus `Verify` (decidable-equality
  scans over all vertices), all evaluated in Agda's term evaluator. Tellingly the **chain** (deep
  nested `hComposeP`) is *worse* than the **parallel** (flat `hTensor`, no pruning) — i.e. the cost
  tracks the translation/verify machinery, not the matching.

So the hard evidence confirms and sharpens the verdict: the matrix–vs–hypergraph gap is
**representational, not a search-vs-no-search algorithmic gap** — and the hypergraph representation's
cost is itself **super-linear** in size (dominated by pruned-`⟪_⟫` + `Verify`), which is exactly what
a flat canonical form (matrix, or a DAG canonical labelling on the hypergraph) would replace.

## The two `solveH!` variants, measured (2026-06-09) — the hypergraph bridge is *slower*

With the `findIsoᴮ` bridge built (`MatrixBridge`/`InterpretBridge`), the two `solveH!` variants differ
*only* in the iso finder — `findIso` (backtracking search) vs `findIsoᴮ` (canonical-form construction
on hypergraphs); everything else (opaque `soundness-full-wired`, the abstract-`C` transport) is shared.
Profiling the two iso finders on the same equations:

| equation | `findIso` (search) | `findIsoᴮ` (bridge) |
|---|---|---|
| `idˡ` (nE=1) | <10 ms | 12 ms |
| σ-naturality (nE=2) | 33 ms | 219 ms |
| σσ-naturality (nE=2) | 25 ms | 187 ms |

**`findIsoᴮ` is ~5–7× *slower*, not faster.** This looks like it contradicts the head-to-head above,
but it doesn't — it sharpens it:

- The ~16–25× head-to-head win belonged to the smc-coherence **flat Bool-matrix** solver
  (`diagram f ≡ diagram g` by `refl` — a cheap array compare). `findIsoᴮ` is a *different* thing: it
  **reconstructs a hypergraph isomorphism** (because `soundness-full-wired` consumes a `≅ᴴ`), via the
  canonical labelling `align` + the two deciders `decBijLaws` + `decCanonMatch` + the `matIso→hgIso`
  record assembly. `decCanonMatch` alone costs ≈ `findIso`'s `Verify`; `findIsoᴮ` then pays `align`
  (peel + `posIn`/`lookupD` + `sortℕ`), `decBijLaws`, the per-edge `ecode` extraction, and the
  12-field assembly *on top*. So it is strictly more work.
- And the "no search" advantage buys nothing here, because — per the edge-scaling probe — `findIso`
  **never backtracks** on monogamous `⟪_⟫` graphs. There was no search cost to eliminate.

**Takeaway.** The hypergraph-native canonical bridge's value is *architectural* — a sound,
postulate-free, no-search-*in-principle* `≅ᴴ` construction that demonstrably drops into `solveH!` — but
it is **not** a speed win over `findIso`. A genuine speed win needs the **flat representation**: decide
equality on the Bool/`SetMatrix` directly (the smc-coherence route) and reach `≈Term` via
`matrix-faithful` — *not* by reconstructing the `≅ᴴ` that `findIso`/`findIsoᴮ` both produce. Equivalently:
the cost is `⟪_⟫` + `Verify`-class scanning, which both finders pay; only abandoning the
hypergraph-iso *reconstruction* (flat-matrix `≈M` + `matrix-faithful`) removes it.

## Implication

The fix is the same as for shrinking the soundness proof itself: a real coherence solver
(`size-reduction-strategies.md`, Lever 1 / `braided-coherence-solver.md`, Option 2) or a
strict-monoidal representation (Option A) would collapse exactly the decode/transport normal forms
that explode here. The head-to-head confirms the *representation* matters: the matrix/normalization
decide step is an order of magnitude cheaper than the hypergraph round-trip, so a finished direct
solver would be both fast and (unlike the APROP one) non-circular. Until then, the APROP solver is
practical only at roughly pentagon/hexagon size — and should at minimum be `opaque` at the top.

The algorithm comparison adds a cheaper near-term option: since `findIso`'s cost here is *building
and verifying* the iso rather than *searching* for it, replacing it with an explicit DAG canonical
labelling (reusing the linear-extension + `FinBij` machinery) would port the matrix's speed-up to the
hypergraph side **without** leaving the proven hypergraph world — complementary to the
`≈M → ≅ᴴ` bridge (`braided-coherence-solver.md`), which reaches the same canonical form via the
matrix representation.
