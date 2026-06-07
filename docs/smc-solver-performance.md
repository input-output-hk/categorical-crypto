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

## Implication

The fix is the same as for shrinking the soundness proof itself: a real coherence solver
(`size-reduction-strategies.md`, Lever 1) or a strict-monoidal representation (Option A) would
collapse exactly the decode/transport normal forms that are exploding here — so they would not
only shrink the proof, they would make the SMC *solver* fast enough to discharge goals like
`GConstruction`'s. Until then, the solver is practical only at roughly pentagon/hexagon size.
