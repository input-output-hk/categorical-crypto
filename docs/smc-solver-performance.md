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

## The `≈M → ≅ᴴ` bridge decision is measurably cheaper (2026-06-09)

A follow-up spike asked the narrower question behind the `≈M → ≅ᴴ` bridge (derive `≅ᴴ` from matrix
equivalence, reuse the existing soundness): is *deciding matrix-equivalence* cheaper than the
`findIsoᴮ` deciders `decBijLaws + decCanonMatch`? Measured on single-generator chains `gᴺ`
(`H = J`, no relabelling), forcing each decision:

| N (nE) | `decBijLaws + decCanonMatch` | matrix floor `matSig(hg→mat)` | advantage |
|---:|---:|---:|---:|
| 4 (5)  | 2,057 ms  | 631 ms   | 3.3× |
| 8 (9)  | 25,025 ms | 4,730 ms | 5.3× |
| 16 (17)| 412,381 ms| 48,799 ms| 8.5× |

So the matrix decision is **3–8× cheaper, widening with size** — and `matSig` is a strict *lower
bound* (the real decision is that build plus a linear `≟` sweep). Two reasons, both of which the
earlier "it'll tie" guess underweighted: (1) `decBijLaws` (the four bijection round-trips) is the
dominant, steepest-exponent cost (~55%), and the bridge **avoids it** — the matrix permutation gives
bijectivity structurally; (2) even `decCanonMatch` *alone* (909/10,874/177,393 ms) loses to the
matrix floor, gap widening 1.4× → 3.6× — the flat Bool-matrix check genuinely beats the list-based
incidence sweep. (Aside: `decBijLaws` could also be dropped in the hypergraph route by proving
`canonV`/`canonE` are permutations, but even then `decCanonMatch` alone still loses to the matrix
floor — the matrix representation is intrinsically cheaper for the decision.)

**Verdict: the bridge's decision-cost is GO.** The remaining cost is the faithfulness proof
`matrixEquiv → ≅ᴴ` — moderate (~half is the already-proven `matIso→hgIso`; the new part is recovering
the ordered incidence from the positionally-indexed matrix plus enriching `hg→mat` to be
*label-aware*, since the current Bool/connectivity-only matrix loses `vlab`/`elab`), with **no
coherence content** (it's an encoding-correspondence, not the term-level `matrix-faithful`).

## The `≈M → ≅ᴴ` bridge built + profiled END-TO-END (2026-06-09)

The bridge is now built: `Solver.MatrixBridgeM` (`canonMat` — a *label-aware* canonical matrix
recording, in canonical order, the vertex labels + edge codes + reindexed incidence; `matrixEquiv H
J := canonMat H ≡ canonMat J`; `decideMatrixEquiv` — the cheap flat compare; `matEquiv→hgIso`, made
`opaque`; `findIsoᴹ`) and `Solver.InterpretBridgeM` (`solveH!ᴹ`). `findIsoᴹ ⟪f⟫ ⟪g⟫` genuinely
reduces to `just` (the implicit `T (is-just …)` auto-discharges on σ-nat / idˡ / σσ-nat / the
edge-free σ-involution), and the opaque `matEquiv→hgIso` keeps the per-use decision = the matrix
compare only.

Profiling the THREE iso finders (`--profile=definitions`, `from-just (find… : Maybe (H ≅ᴴ J))`) on
the single-generator chain family `gᴺ` (`H = J`, no relabelling) + σ-naturality, with the shared
`⟪_⟫` translations hoisted into their own definitions so each timing is the finder cost alone:

| N (nE) | `findIso` (search) | `findIsoᴮ` (decBijLaws+decCanonMatch) | `findIsoᴹ` (matrix bridge) | ᴮ→ᴹ |
|---:|---:|---:|---:|---:|
| 4 (4)   |    68 ms |     845 ms |     202 ms | 4.2× |
| 8 (8)   |   685 ms |  15,737 ms |   3,044 ms | 5.2× |
| 16 (16) | 8,131 ms | 421,182 ms |  56,703 ms | 7.4× |
| σ-nat (2)| 18 ms  |     264 ms |      69 ms | 3.8× |

**`findIsoᴹ` realizes the predicted decision win over `findIsoᴮ`: 4–7×, widening with size** — exactly
the 3–8× the head-to-head spike measured for the *decision* alone, now realized END-TO-END (the
opaque faithfulness never enters the per-use path). The win is the two avoided deciders: `findIsoᴮ`
pays `decBijLaws` (the four bijection round-trips — the steepest cost) + `decCanonMatch`, whereas
`findIsoᴹ` pays one flat structural compare of two `CanonData` records; bijectivity is supplied
*structurally* by the (opaque) `CanonPerm`-derived `BijLaws`, never decided.

**But `findIsoᴹ` is still 3–7× *slower* than the backtracking `findIso`.** This is the honest caveat:
`findIsoᴹ`'s residual cost is *building the two `canonMat`s* — the full topological peel
(`Canon.canonV`/`canonE`) + the per-edge `posIn` reindexing — which on these monogamous `⟪_⟫` graphs
is heavier than `findIso`'s `Verify` sweep (and `findIso` never backtracks here, so there was no
search cost to beat). The matrix bridge wins against its true peer (`findIsoᴮ`, the other no-search
`≅ᴴ` *reconstruction*), but the canonical-labelling build is itself super-linear — the same
representational cost the doc above identifies. A genuine speed win over `findIso` still needs the
flat term-level `≈M` + `matrix-faithful` route (not reconstructing a `≅ᴴ`); `findIsoᴹ` is the cheapest
of the `≅ᴴ`-reconstructing finders, not cheaper than search.

## Cost attribution within `findIso` (2026-06-09) — it is *re-evaluation without sharing*

A final attribution probe separated the components of the post-`opaque` per-use cost
(`findIso ⟪f⟫ ⟪g⟫` on single-generator chains, `--profile=definitions`):

| probe | N=8 | N=16 | meaning |
|---|---:|---:|---|
| `tr` — deep-force the translation once (`forceH ⟪chain N⟫`, no iso machinery) | 75 ms | 466 ms | **the translation itself is cheap** |
| `tr2` — force it **twice in one definition** | 150 ms | — | **exactly 2× ⇒ Agda does NOT share**: syntactically identical subterms are fully re-evaluated |
| `iso` — full `findIso` (right-nested chain) | 798 ms | 8,310 ms | 10.6× / **17.8×** the one-shot translation, growing |
| `isoL` — same, **left-nested** chain | 1,041 ms | 20,028 ms | association matters: left-nesting is 1.3× / **2.4×** worse, diverging |
| `snd-inline` — `soundness-full-wired (from-just (findIso …))` inlined | 1,900 ms | — | = iso + ~1.1 s application overhead |
| `snd-hoisted` — `soundness-full-wired iso-8` (named iso) | 1,172 ms | — | the ~1.1 s overhead is paid either way (one ⟪⟫-type conversion); hoisting is program-neutral |

**This revises the earlier attribution.** The translation `⟪f⟫` costs only ~5–10% of `findIso`
when forced *once*; the other ~90–95% is `findIso`'s machinery **re-walking unshared thunks** —
every field access re-pays the O(depth) `hComposeP` evaluation, and the redundancy multiplier
(10.6× → 17.8×) grows with size. The hypergraph representation is fine; the evaluator's lack of
sharing is the bottleneck.

### The remaining levers, ranked (matrix-soundness route excluded)

1. **Literalization of `⟪f⟫` before the search (the big one, est. ~10×, growing).** Force the
   translation **once** into *literal* constructor data and run `findIso` over the literals (O(1)
   per access). Note `tabulate`/`Vec` does **not** achieve this — its elements stay unshared thunks
   (the `tr2` finding) — so the working implementation is a small **reflection macro**: `quoteTC` +
   `normalise` each field of `⟪f⟫`, splice a literal `Hypergraph` value `Hf` plus a `refl`-checked
   `Hf ≡ ⟪f⟫` (conversion pays one full normalization ≈ `tr`), then `subst₂`-transport
   `findIso Hf Hg` back to `⟪f⟫ ≅ᴴ ⟪g⟫`. Sound, `--safe`-compatible (cf. `Categories.Tactic.Category`),
   ~200–400 LOC of reflection code, no new math. Expected end state ≈ `tr` + cheap search: ~0.5–1 s
   instead of 8.3 s at N=16. (Bonus: literal graphs also un-stick the `refl`-style validations that
   currently require hand-built hypergraphs.)
2. **Re-association pre-pass — but to BALANCED form, not right-nested (correction).** A follow-up
   probe (16 and 32 generators) measured balanced `∘`-trees at **3,512 ms / 29.2 s** vs right-linear
   **9,502 ms / 113.8 s** vs left-linear (20 s at 16) — i.e. **balanced < right < left, gaps growing**
   (2.7× → 3.9× balanced-vs-right). So the originally-proposed *right*-reassociation would have
   merely shifted cost: it helps left-heavy goals ~2.4× but *pessimizes* balanced ones ~2.7–3.9×.
   The mechanism: every field access pays the `hComposeP` layers on its path, so what matters is
   path *depth* — O(log n) balanced vs O(n) linear (modulated by the G/K asymmetry, which is why
   right beats left among linear shapes). The correct lever is a **rebalancing** `reassoc` (same
   trivial assoc-only `≈Term` proof, ~50–100 LOC): speeds linear inputs 2.7–5.7× (growing), no-op on
   balanced. Note it is largely **subsumed by (1)**: literalization removes the per-access
   multiplier, leaving shape sensitivity only in the single forced normalization (where balanced
   still wins ~2×: `tr` 247 vs 491 ms) — so do (1) first; (2) is a compounding ~2× on top.
3. **The ~1.1 s `soundness-full-wired`-application overhead** — real, paid once per solve even with
   the named-iso pattern; likely one re-normalization of the `⟪_⟫`-typed index during conversion.
   Bounded but worth a look after (1), since (1) makes the iso's type a literal too.
4. *(Workflow)* put expensive solver calls in **leaf modules** (paid once, cached in `.agdai`), and
   split very large equations by `≈-Term-trans` into solver-sized steps — cost is super-linear in
   size, so splitting wins.

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
matrix representation. *(Superseded in part by the attribution probe above: the cheapest path is to
keep `findIso` and remove the re-evaluation, via literalization.)*
