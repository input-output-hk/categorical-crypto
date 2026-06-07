# Option 2: a direct braided coherence solver (investigation)

The recurring conclusion of the size-reduction and solver-performance analyses
(`size-reduction-strategies.md`, `smc-solver-performance.md`) is that the one lever which would
*both* shrink the soundness proof *and* make a usable SMC solver is a **direct coherence
decision procedure** — one that decides free symmetric-monoidal term equality by
**normalization**, not by the hypergraph round-trip (`soundness-full-wired ∘ findIso`).

This note investigates what building that would take.

## What "direct" buys: non-circular and fast

The APROP `Solver` decides `f ≈Term g` via `soundness-full-wired (from-just (findIso ⟪f⟫ ⟪g⟫))`.
That route (a) is **circular** with the soundness theorem (so it cannot be used to *prove* or
shrink soundness), and (b) inherits the decode/transport normalization wall, so it OOMs past
hexagon size.

A direct solver normalizes each side to a canonical wiring representation, compares, and
transports the verdict to any SMC via the free functor (`Functor.F-resp-≈ freeFunctor _`, exactly
how `MonoidalCoherence.Solver.solveM` works). Because the correctness theorem is a *direct*
coherence argument, it is:

- **non-circular** w.r.t. the hypergraph soundness theorem → usable to discharge the soundness
  proof's own M/K obligations (Lever 1 / Option A), and
- **fast** → no `decode`/`subst`/`bridge` normalization, so it would close goals like
  `GConstruction.assoc'-coherence` in one cheap call.

## Two existing substrates

### Substrate B — `SymmetricMonoidalCoherence/*` (branch `smc-coherence`) — RECOMMENDED

A matrix / wiring-diagram solver, already built end-to-end:

- `Matrix.agda` (179 LOC, `--safe`, **0 postulates**) — matrices in a biproduct/span category
  (the wiring representation; `≈M` is matrix equality).
- `Reflect.agda` (459 LOC, **0 postulates**) — reflection between `HomTerm` and diagrams.
- `Translation.agda` (127 LOC) — `size : ObjTerm → ℕ`, `matrix : HomTerm A B → SetMatrix (size A) (size B)`.
- `Coherence.agda` (72 LOC) — the keystone and the interface:
  ```
  matrix-faithful : matrix f ≈M matrix g → f ≈Term g          -- the deep theorem (postulated)
  solveSM f g meq = Functor.F-resp-≈ freeFunctor (matrix-faithful f g meq)
  ```
- `Tests.agda` (626 LOC) + `SolverTests.agda` (109 LOC, **0 postulates**) — a working test suite.

`--without-K` (not yet `--safe`, because of the postulates). The gap is **~27 postulates in two
tiers**:

- **Soundness tier (routine):** ~20 `Diagram.wdiagram-resp-≈ <law>` (one per `≈Term` axiom:
  `idˡ … pentagon … hexagon`) + `Translation.matrix-resp-≈`. Each says "this generating law
  preserves the wiring matrix." Mostly mechanical matrix arithmetic; a handful
  (`pentagon`/`hexagon`/`α-comm`) need real diagram algebra.
- **Completeness tier (the deep core):** `matrix-faithful` (equal matrix ⇒ `≈Term`) +
  `Diagram.reflect-correct` (the structural-coherence sub-case) + `canonicalize-resp-≈D`.

### Substrate A — `FreeStrictMonoidal.HomTermⁿ` (branch `main`)

A rewriting normal form: `HomTermⁿ` (a sequence of generator-layers at wire offsets — the planar
string-diagram NF), the interchange rewrite `_→ʳ_`, and the hard offset-reindexing (`Setup`). But
it is **data only** — no normalization function, no soundness, no confluence/completeness — and
it is **planar** (no `σ` in the NF, so it would need a permutation layer added for the symmetric
case). Plus 4 routine prefix-arithmetic postulates. Much earlier-stage than B; would need the
entire confluence theory from scratch.

**Verdict:** Substrate B is the right starting point — its interface, reflection, and tests are
done; only the correctness postulates remain.

## The crux: `matrix-faithful`

Everything hinges on one theorem: **two terms with equal wiring matrices are `≈Term`-equal.**
This is the symmetric-monoidal coherence theorem — the *same mathematical content* as the ~18k-LOC
APROP hypergraph soundness development, but expressed in the matrix/span representation.

Two reasons to believe the matrix route is *shorter* than the hypergraph one:

1. **It reuses the independent K-kernel.** `Categories.PermuteCoherence.*`
   (`FinBij`/`Eval`/`Faithfulness`/`Canonical`, ~520 LOC, **0 APROP-Hypergraph imports**) already
   proves the permutation coherence `FaithfulnessResidual : eval π ≈ eval π' → permute π ≈ permute π'`,
   axiom-free. A wiring matrix *is* an evaluated permutation-with-labels, so `matrix-faithful`
   should reduce to "strip `α/λ/ρ` (they are identities on matrices) + apply FinBij coherence to
   the permutation part" — the `reflect-correct` postulate is explicitly the structural-coherence
   sub-case, which is exactly the FinBij content.
2. **No decode/pruned/transport baggage.** The matrix representation is computational (decidable
   `≈M`), so the proof inducts directly, without the `process-edges`/`extract-prefix`/pruned-vs-
   unpruned/transport machinery that dominates the hypergraph development.

**This is the make-or-break and the one genuine unknown.** If `matrix-faithful` reduces cleanly
(structural induction + FinBij reuse), Option 2 is the biggest win available. If it turns out as
hard as the hypergraph soundness theorem, it is a lateral move (re-proving the same result in a new
representation). This cannot be settled by reading — it needs a spike.

## Payoff if it lands

1. **GConstruction.`assoc'-coherence` closes in one fast call** (matrix comparison, no decode wall).
2. **Discharges the soundness proof's M-content** (`DecodeTensorShape`/`BoxKernel`/`BridgeAlpha…`)
   and the σ-block **K-content** via strictification — the morphism normal form *is* the
   strictification (Lever 1 + Option A together).
3. **A fast, non-circular SMC solver** — what the APROP `Solver` structurally cannot be.
4. **Possibly subsumes much of the hypergraph soundness tree** (both prove SMC coherence) — the
   largest conceivable reduction, but a major architectural pivot, and only if `matrix-faithful`
   is genuinely cheaper than the hypergraph proof.

## Recommended staging

1. **De-risk (low risk, ~days):** discharge a representative slice of the soundness-tier postulates
   (`wdiagram-resp-≈ idˡ/assoc/⊗-∘-dist`, then `pentagon`/`hexagon`) to confirm the matrix
   arithmetic is as routine as it looks and the representation is sound. This also moves `Matrix`/
   `Translation` toward `--safe`.
2. **Spike the crux (high uncertainty):** attempt `reflect-correct` (the structural-coherence core
   of `matrix-faithful`) reusing `PermuteCoherence.FinBij`. The outcome of this spike *is* the
   go/no-go for Option 2 — it tells you whether the matrix representation yields a short coherence
   proof.
3. **Only then commit:** finish `matrix-faithful`, port the package from `smc-coherence` to `main`
   (it is 388 commits off the current soundness tree), and build the `FreeMonoidal ↔ strict`
   bridge needed to apply the solver to the soundness proof and to `GConstruction`.

## Spike results (2026-06-07) — qualified GO; the math is done, the work is engineering

A go/no-go spike on `smc-coherence` (baseline `SolverTests` builds green, EXIT 0) **inverted** the
prior expectations:

**Completeness core — GO (it genuinely collapses, does not relocate).** `≈D` encodes exactly
(generator-permutation `π`) + (same labels) + (block agreement) (`WDiag.agda:76–87`);
`reflect`/`canonicalize` already factor a morphism into structural-normalization
(`normalize`/`flattenV`) + read-permutation (`readPerm`) + adjacent-transposition decomposition
(`sortSwaps`/`swapAllHom`) + generator-peeling (`Reflect.agda:146–219`). The structural base case
`structural-coherence` (`Diagram.agda:422`) is *exactly* a Kelly/FinBij statement — and the
external kernel discharges it **constructively**: `PermuteCoherence.Faithfulness` typechecks
against this branch's `FreeMonoidal` (EXIT 0), and `FaithfulnessInductive` proves
`faithfulness : FaithfulnessResidual` (`eval π ≈ eval π' → permute π ≈ permute π'`) `--safe
--without-K` with **no postulates**. So the deep combinatorial core already exists and reuses — the
coherence problem collapses onto it.

**Soundness tier — the surprise NO-GO (it is *not* routine).** Each `wdiagram-resp-≈ <axiom>` needs
a bespoke symbolic-dimension Bool-matrix arithmetic proof (`sumB`/`classify`/`δ` identities over
abstract `size`s); zero discharged cleanly, even `id⊗id≈id` (4-way case split + custom lemmas).
Estimate **~50–90 LOC × ~21 axioms ≈ 1,000–1,900 LOC** of mechanical-but-laborious grind. No deep
difficulty (pentagon/hexagon are `k=0`, no harder than the rest — the diagram doesn't "see"
bracketing/braiding), but substantial. The author pre-built the toolkit (`δ-shift`/`δ-ne`/…,
`Diagram.agda:219–298`), indicating it was always meant as laborious-mechanical.

**Two further engineering costs surfaced.**
- **Two-track split:** `solveSM` rests on `Coherence.matrix-faithful` over the **`matrix`/`≈M`
  SetMatrix** track, but the FinBij-reduction machinery (`reflect-correct`/`structural-coherence`)
  lives in the **separate `wdiagram`/`≈D` Bool-matrix** track, and `wdiagram-faithful` is consumed
  by nothing. The reduction must be wired into the track `solveSM` actually uses (or `solveSM`
  repointed). Resolve this first.
- **Porting friction:** the kernel chain `PermuteCoherence` (~26 files) + `SigmaBlockHexagon`
  (975 LOC) + the **experiments-branch `MonoidalCoherence`** (which diverged: added a
  `DecidableEquality X` param + Hedberg UIP to go `--without-K`, universe-polymorphic `Solver`)
  must be ported onto a common base. Confined to `MonoidalCoherence`, not pervasive, but it's the
  `--safe`/`--without-K` friction point.

**Remaining glue (genuine new work, but structural not coherence):** bridge `reflect`/`canonicalize`'s
`flattenV`/`readPerm` to the kernel's `unflatten`/`permute`/`eval-↭`, show `≈M`/`≈D`-equality
induces the equal-FinBij hypothesis `p ≅↭ q`, and assemble the generator-peeling induction (the
kernel only covers the zero-generator base case).

## Bottom line

**Verdict: qualified GO.** The strategic bet is sound — the deep coherence content collapses onto an
already-proven, reusable FinBij kernel; it does **not** merely relocate the problem. But landing it
is a **multi-session engineering effort**, not a quick win: ~1–1.9k LOC of mechanical matrix-arithmetic
for the soundness tier, the representation-bridging glue + generator-peeling induction, plus a
cross-branch `MonoidalCoherence`/kernel port with a `--safe`/`--without-K` reconciliation — and the
two-track (`≈M` vs `≈D`) split must be resolved first. No open mathematics; substantial plumbing.
