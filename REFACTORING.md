# Goal: complete the completeness theorem

`Categories.APROP.Hypergraph.CompletenessFull.completeness-full :
⟪ f ⟫ ≅ᴴ ⟪ g ⟫ → f ≈Term g` builds cleanly with `⟪_⟫` from
`Translation` (pruned `hComposeP`), keeping symmetry with
`Soundness.agda`. `Solver/Tests.agda` exercises 20 categorical-axiom-
shaped equations end-to-end through `completeness-full ∘ findIso` —
all 20 pass.

## Current postulate inventory

The completeness path depends on **one narrow postulate**, bundled
into the `CompletenessAssumptions` record in
`Completeness/DecodeRel/Inductive.agda`:

```agda
record CompletenessAssumptions : Set where
  field
    decode-rel-resp-iso
      : ∀ {A B} (f g : HomTerm A B)
      → ⟪ f ⟫ ≅ᴴ ⟪ g ⟫
      → decode-rel f ≈Term decode-rel g
```

This is the Route 1 high-level statement: the structural decoder
`decode-rel` is iso-invariant.  See REFACTORING.md § "Route 1" for
the discharge strategy.

The previously-postulated `nf-resp-≅ᴴ-residual` (at the bridge level)
is now DERIVED as a three-step composition in `WithAssumptions`:

```agda
nf-resp-≅ᴴ-residual f g iso =
  bridge f       ≈⟨ P1 ⟩    -- bridge↔decode-rel (constructive)
  decode-rel f   ≈⟨ P2 ⟩    -- iso invariance (POSTULATE)
  decode-rel g   ≈⟨ P3 ⟩    -- decode-rel↔bridge (constructive)
  bridge g
```

with named pieces

- **P1**: `bridge≈decode-rel f = ≈-Term-sym (decode-roundtrip-rel f)`
  — the (sym of the) bridge roundtrip from `DecodeRel.agda:157-171`.
- **P2**: `decode-rel-resp-iso f g iso` — the Route 1 postulate.
- **P3**: `decode-roundtrip-rel g` — the symmetric roundtrip.

P1 and P3 are constructive.  P2 is the only postulate.

`CompletenessFull.agda` takes this record as a parameter and is
therefore `--safe`-clean: the trust is exposed only at the call site
that supplies a record instance.

`decode-rel-resp-≅ᴴ-full` is a 4-line composition
`trans (decode-roundtrip-rel f) (trans (nf-resp-≅ᴴ iso) (sym
(decode-roundtrip-rel g)))`, no recursion.

### Dispatcher (`nf-resp-≅ᴴ` in `WithAssumptions`)

Case-splits before falling through to the residual:

1. Both `NoSigma` → `Structural-coherence-≈Term-noσ` (Mac Lane,
   constructive via `solveM`).
2. Both atomic `Agen` → `decode-rel-resp-≅ᴴ-Agen-Agen` (constructive
   in `RespIso/AgenAgen.agda`).
3. Edge-count contradictions: any `NoAgen` vs `HasAgen` (or atomic
   `IsAgen`) mix is vacuous via `ψ`/`ψ⁻¹` on `Fin 0`.
4. Both `SingleAgen` (σ-free, exactly one `Agen` subterm each) →
   `single-agen-coherence-≈Term`, which constructively extracts the
   three flat equalities via `single-agen-flat-data` and 3-way
   dispatches on the Agen edge's interface in `⟪g⟫`:
     * **ein non-empty**: `single-agen-NF-coherence-discharge-nonempty`.
     * **ein empty AND eout non-empty**:
       `single-agen-NF-coherence-discharge-nonempty-eout`.
     * **both ein and eout empty** (scalar u : 1 → 1):
       `single-agen-NF-coherence-discharge-scalar` (commit `23d3000`).
5. Else → `nf-resp-≅ᴴ-residual`.

After (1)–(4), the residual fires only when at least one side contains
a σ subterm OR contains ≥2 Agen subterms.

## Architectural blockers

Two counter-example families established by independent investigation:

1. **σ-naturality half-swap (tensor)**: `Agen u ⊗ id` vs `id ⊗ Agen u`
   at `unit ⊗ A → unit ⊗ A` are `≈Term`-equal via σ-naturality, their
   hypergraphs are `≅ᴴ`-isomorphic via a half-swap, but no
   L→L-restricting sub-iso exists (Soundness's σ-naturality witness in
   `Categories.APROP.Hypergraph.SigmaNat` is literally the half-swap
   producer).

2. **idˡ/idʳ-absorption (composition)**: `Agen u ∘ id` vs
   `id ∘ Agen u` at `unit → unit → unit` are `≈Term`-equal via
   `idˡ`/`idʳ`, their composite hypergraphs are isomorphic, but
   sub-iso extraction is impossible (one composite slice has 1 edge,
   the "extracted" sub-iso would need 0 edges).

These pathologies architecturally block the **inductive** strategies
that powered the old `decode-rel-resp-≅ᴴ-full` (decomposing isos
recursively through `⊗⊗`/`∘∘`/`⊗∘`/`∘⊗`).  Direct inductive proof of
the residual is not on the table — see Routes 1 and 2 below.

### Earlier unsoundness retractions (cautionary)

- `425bf16` reverted `⊗-∘-dist-FromAPROP-iso` and its mirrors:
  vertex-count mismatch (`⟪p ⊗ q⟫` and `⟪(p⊗id) ∘ (id⊗q)⟫` differ by
  `nA + nB` under unpruned `hCompose`).  `_≅ᴴ_` requires a
  Fin-bijection on vertices.
- Earlier `perm-eq-from-iso` split of `Structural-coherence-≈Term` was
  reverted: `Data.List.Relation.Binary.Permutation.Propositional._↭_`
  is not truncated, so the propositional equality of permutations was
  unprovable as stated.

## Discharged: Field 1 (`single-agen-NF-coherence`)

Originally a second record field for the σ-free single-Agen case.
Fully discharged constructively over commits `7aebf2c..23d3000` in
three sub-cases (ein-non-empty, eout-non-empty, scalar).  The
discharge chain composes: `flat-data-to-ObjTerm` → flat→ObjTerm eqs;
`YL-length-from-iso[-eout]` → length-of-YL equality (non-empty case
only); `positional-alignment-from-length` → flatten-of-YL/YR eqs;
`single-agen-strip` → σ-free wrappers; `discharge-aligned` → wrapper
closure via `NoSigma-coherence`, `bridge-naturality-pos`, bridge iso
laws.  The eout-side uses `⟪_⟫-cod-unique` + `remap-injective`.  See
`Completeness/DecodeRel/Inductive.agda` for the live code.

## Routes for discharging `nf-resp-≅ᴴ-residual`

Deep investigation produced two main routes plus a speculative third.
Neither Route 1 nor Route 2 is a clear winner — both carry significant
hidden risks identified below.

### Route 1 — Iso-invariant decoder (proves the theorem)

**Plan**: define `decode-of : Hypergraph → HomTerm` that is
iso-invariant, then prove

```
bridge f ≈Term decode-of ⟪f⟫ ≈Term decode-of ⟪g⟫ ≈Term bridge g
```

The middle step is the new lemma:
`H ≅ᴴ K → decode-of H ≈Term decode-of K`.

**Existing foundation (strong)**:

- `decode-rel : HomTerm A B → HomTerm (unflatten (flatten A)) (unflatten (flatten B))`
  is fully defined (`DecodeRel.agda:53-78`), recursive on term structure.
- `decode-roundtrip-rel : decode-rel f ≈Term bridge f` is **completely
  constructive** (`DecodeRel.agda:157-171`); atomic cases reduce to
  `≈-Term-refl`, ∘/⊗ cases use now-`refl` shape lemmas.
- `Linear` invariant + `⟪⟫-Linear` constructive (`Linearity.agda`).
- `extract-prefix-from-↭` (`DecodeProperties.agda:467-520`) absorbs
  permutations on the *vertex-lookup* side.
- **NEW** (`Route1Composition.agda`): `decode-rel-resp-iso` is now a
  CONSTRUCTIVE function derived from two narrower postulates at the
  algorithmic-decoder level:
  - `decode-rel-≈-decode` — agreement between the structural decoder
    `decode-rel` and the algorithmic decoder `decode` (~50-100 LOC
    discharge sketch in comments; "provable" per DecodeRel.agda
    comments).
  - `decode-resp-iso` — algorithmic decoder iso invariance, bundling
    sub-properties (b), (c), (d) of Route 1's discharge.

  Trust shift: from 1 opaque term-level postulate to 2 narrower
  algorithmic-level postulates.  The composition is a 3-line
  constructive chain via `decode-rel-≈-decode` + `decode-resp-iso` +
  `≈-Term-sym` of `decode-rel-≈-decode`.  Also exports
  `route1-assumptions : CompletenessAssumptions` that wires the
  constructive `decode-rel-resp-iso` into the existing
  `Inductive.agda` record.

- **NEW** (`LinearityIso.agda`, **`--safe`-clean**, ~440 LOC):
  Linear preservation under iso (sub-property (a) of Route 1's
  discharge) is now FULLY CONSTRUCTIVE.
  - `count-↭` — count is invariant under list permutation (~13 LOC).
  - `count-map-via-bij` — count under bijection-map relabels via the
    inverse (~10 LOC).
  - `tabulate-bij-↭` — `tabulate (f ∘ π) ↭ tabulate f` for self-
    bijections π on `Fin n` (~70 LOC).  Induction on n with
    bijection deflation via stdlib's `punchIn`/`punchOut`.
  - `bij-fin-ℕ-≡` — m ≡ n from a Fin-bijection (~10 LOC).
  - `tabulate-bij-↭-via-eq` — extension to Fin m → Fin n
    bijections (~3 LOC).
  - `concat-↭` — concat preserves ↭ (~10 LOC).
  - **`Linear-resp-iso : H ≅ᴴ K → Linear H → Linear K`** — the main
    theorem, ~80 LOC composition.  For each v : Fin K.nV,
    derives `count v (producedList K) ≡ count (φ⁻¹ v) (producedList H)`
    via the iso's φ/ψ data + the helpers; Linear K then follows by
    applying Linear H at φ⁻¹ v.
  
  Sub-property (a) is now in the bank for the eventual discharge of
  `decode-rel-resp-iso`.  Three sub-properties remain ((b)
  edge-reorder, (c) vertex-relabel, (d) stack-permutation absorption).

**The missing core lemma**: edge-reorder invariance.  The decoder
processes edges in order `range nE`.  Under the iso's `ψ` bijection,
the "same edges" appear in DIFFERENT orders on the two sides.  Needed:

```agda
process-edges-↭
  : (es₁ es₂ : List (Fin H.nE)) → es₁ ↭ es₂
  → process-edges H es₁ s ≈Term process-edges H es₂ s
```

This lemma does NOT exist in the codebase.  `extract-prefix-from-↭`
is the closest analog but absorbs permutations on the lookup-list
side, not the edge-sequence side.

**Critical concern — architectural blockers can resurface**: for
`f = Agen u ⊗ id` vs `g = id ⊗ Agen u`, the half-swap iso has the
same Agen edge but with reversed ein vertex order under φ.  The
decoder's `extract-prefix` consumes the stack in different orders,
producing terms whose `σ`/`α`/`λ`/`ρ` permutation skeletons differ.
Bridging them requires `σ∘[f⊗g]≈[g⊗f]∘σ` — the same axiom whose
hypergraph image (the half-swap iso) was the original obstacle.  The
blocker doesn't disappear; it shifts from term-structural induction
to permutation arithmetic on edge sequences.

**Concrete LOC and risk breakdown**:

| Module | LOC | Risk |
|---|---|---|
| `process-edges-↭` (edge reordering) | ~250 | **High**: permutation arithmetic subtleties |
| `vertex-relabel-invariance` (φ side) | ~150 | Medium: mostly rewriting |
| `decode-rel-resp-iso` (combine) | ~200 | **High**: tensor/compose threading |
| `extract-prefix-under-relabel` | ~100 | Low: similar to existing |
| `iso-preserves-Linear` | ~10 | Trivial |
| **Total** | **~700** | **High** |

**Failure mode**: if the permutation structure gets baked into the
term recursively (e.g., in the ⊗ case where permutations on left and
right sides must thread together), the proof could grow exponentially
in depth, hitting Agda's computational limits.  The σ-naturality
pathology becomes "permutation depth blowup" rather than "no sub-iso
exists" — same fundamental difficulty, different layer.

**Viability test status (probe in `Completeness/EdgeReorder.agda`)**:
the `refl` and `prep` cases are proven constructively (~30 LOC); the
`swap` case is analysed structurally.  Findings:

- **The natural lemma is FALSE in general.**  Concrete counter-example:
  for edges `e₁ : [v₁]→[v₂]` and `e₂ : [v₂]→[v₃]` from stack `[v₁]`,
  the order `[e₁,e₂]` produces final stack `[v₃]` but `[e₂,e₁]`
  produces `[v₂]` (because `e₂` cannot fire when its prerequisite
  `v₂` isn't on the stack — `extract-prefix` silently skips).  Final
  multisets aren't `↭`-related.
- **The correct lemma requires a topological-success precondition**
  (`AllFire es s` = every edge in `es` successfully extracts from
  the running stack).  For the iso case (`H ≅ᴴ K`, both Linear),
  this precondition holds for both orderings — but proving its
  preservation under iso adds substantial bookkeeping (~200 LOC).
- **POSITIVE finding: σ-naturality on Agen edges is NOT required.**
  The decoder structure places Agen edges "side-by-side in tensor"
  through `unflatten-++-≅` chains, not "swapped through σ".
  Commuting `(Agen e₁ ⊗ id)` past `(Agen e₂ ⊗ id)` uses `⊗-∘-dist`
  + Mac Lane coherence on the surrounding wrappers — NOT σ-naturality
  on the generators themselves.  The architectural blocker does NOT
  recur in Route 1.
- **REVISED LOC estimate**: ~1100-1550 (up from 700), reducible to
  ~800-1000 if `solveM` is extended to absorb the per-swap-atom Mac
  Lane chase wholesale.

**Verdict**: Route 1 is **viable but more expensive than first
estimated**.  The architectural blocker is real but does not block
Route 1 specifically — it's displaced into Mac Lane coherence
gymnastics on coherence wrappers, which are constructive though
verbose.  The next test would be proving the "both fire, non-
interacting" swap sub-case fully in Agda (~200 LOC) to confirm the
Mac Lane chase actually composes without surprises.

### Route 2 — Solver-emits-≈Term (sidesteps but does not discharge)

**Plan**: change `findIso : H J → Maybe (H ≅ᴴ J)` to
`findIso : f g → Maybe (⟪f⟫ ≅ᴴ ⟪g⟫ × f ≈Term g)`.  Each search step
emits the categorical-axiom rewrite that justifies it.  The postulate
stays in `CompletenessAssumptions` but is **never reached** by the
standard pipeline (Tests.agda routes through the enriched `findIso`).

**Pipeline structure** (`FindIso.agda:47-71`): Seed → Search → Verify.

| Stage | Role | ≈Term emission | Effort | Risk |
|---|---|---|---|---|
| **Seed** (`Seed.agda:70-92`) | Match boundary vertices by interface | Coherence iso (`unflatten-flatten-≈`) | ~50 LOC | Low |
| **Search** (`Search.agda:55-88`) | Backtrack edge bijection ψ | Naturality axioms per match | ~300 LOC | **High** |
| **Match** (`Match.agda:85-108`) | Per-edge bijection extension | Generator-specific dispatch | ~250 LOC | **High** |
| **Verify** (`Verify.agda:149-240`) | Assemble iso record + invariants | Pass-through | ~20 LOC | Low |

**Critical issue**: `findIso` currently takes hypergraphs, NOT terms.
The term structure isn't visible to the solver.  Threading term info
through all five files (FindIso, Search, Match, Verify, PBij) is a
major refactor.  `searchIso`'s signature changes from
`(fuel : ℕ) → VertexBij → EdgeBij → Maybe (...)` to one carrying
`f, g : HomTerm` plus an accumulated partial rewrite proof.

`Match.matchEdge` would need **generator introspection** — distinguish
σ-edges from Agen-edges from structural edges — to dispatch the right
axiom.  Currently matching is purely shape-based (atom-list agreement,
edge count).  Generator-aware dispatch is ~300-400 LOC of *risky*
new code with novel invariants.

**Coverage limitation**: Route 2 provides `f ≈Term g` only when the
iso came from `findIso`.  For the postulate's signature
`∀ {A B} (f g : HomTerm A B) → ⟪f⟫ ≅ᴴ ⟪g⟫ → bridge f ≈Term bridge g`,
where the iso is *given* (could come from anywhere), Route 2 doesn't
help.  Consequences:

- All 20 tests in `Solver/Tests.agda` are routed through `findIso`,
  so Route 2 covers them.
- `completeness-full` as a general theorem still syntactically
  requires `CompletenessAssumptions`; with Route 2, the record is
  never invoked by the standard pipeline but remains a "trust
  assumption for non-solver isos" in the type.

**Architectural blocker check**: the σ-naturality counter-example IS
in the test suite (`Tests.agda:195`, `test-σ∘[f⊗g]`).  Under Route 2,
when `findIso` runs on this case:

1. Seed pairs boundary vertices (structural, no axiom needed).
2. Search matches the Agen-pair edges from LHS to RHS (positions
   shifted due to the swap).
3. Search matches the σ-edge.  To emit ≈Term, this step must
   recognize "σ-edge interacting with reordered tensor inputs" and
   apply `σ∘[f⊗g]≈[g⊗f]∘σ`.  The axiom exists constructively as a
   `_≈Term_` constructor; what's missing is dispatch logic in Match.

**Failure mode**: generator-aware dispatch in Match could fail to
cover edge cases.  Tests pass case-by-case, but new tests or
solver-emitted isos for complex axioms could expose dispatch gaps.

### Comparison

| Dimension | Route 1 | Route 2 |
|---|---|---|
| Discharges the postulate? | Yes (any iso) | No (only solver isos) |
| `completeness-full` becomes constructive? | Yes | Only for solver-derived inputs |
| LOC estimate | ~700 | ~660 |
| Riskiest module | `process-edges-↭` | `Match` generator dispatch |
| Architectural blocker handling | Resurfaces as permutation depth | Bypassed structurally; per-step axiom dispatch |
| Failure mode | Term blowup / Agda compute limit | Dispatch gaps in Match |
| Reusability of new code | Permutation lemmas (stdlib-flavor) | Solver-specific |
| Auditability | One big proof | Many small per-axiom proofs + dispatch logic |
| Test coverage cost | None (one proof discharges all) | Per-test rewrite chain (~10 steps each) |

### Route 3 — Linear / vertex-counting argument (speculative)

Not yet investigated in depth.  The intuition: prove the postulate
for the *Linear* fragment using a multiset/counting argument that
operates at the hypergraph level, not via term-structural induction
or edge ordering.  Linearity (`Linearity.agda`) is preserved under
the translation; the iso preserves it; vertex-multiset equality
might encode the structural data needed to bridge `f` and `g` without
touching the permutation pathology.  Would need its own research pass.

## Recommendation

After the viability probe (`Completeness/EdgeReorder.agda`):

- **Route 1 is viable but expensive** (~1100-1550 LOC).  The
  architectural blocker does not recur for the decoder; the cost is
  Mac Lane coherence chase per swap atom plus the `AllFire`
  precondition bookkeeping.
- **Route 2 is cheaper for current call sites** (~660 LOC) but does
  not discharge `completeness-full` for arbitrary isos.
- **Route 3 (Linear/vertex-counting)** is still speculative.

Suggested path forward:

1. **Confirm the Mac Lane chase composes** by proving the "both fire,
   non-interacting" swap sub-case fully (~200 LOC).  Definitive
   confirmation that Route 1's expensive-but-tractable estimate is
   accurate.
2. If step 1 succeeds, decide based on appetite: Route 1 (general
   theorem, more LOC) vs Route 2 (test-coverage-only, less LOC).
3. If step 1 hits unexpected blockers, pivot to Route 2 starting
   with Seed + Verify (the easy stages), building up to Search/Match
   per-test rather than uniformly.

## Helpers and infrastructure (still live)

- `Completeness/PermutationCoherence.agda` —
  `↭-to-≅ : xs ↭ ys → unflatten xs ≅ unflatten ys`.  Used by
  `bridge`/`bridge⁻¹` derivations.
- `Completeness/Unflatten.agda` — `unflatten`/`unflatten-flatten-≈`,
  the `bridge` half-isomorphism foundation.
- `Completeness/BridgeOps.agda` — `bridge-∘`/`bridge-⊗`/
  `bridge-⊗-decompose`, constructive distributivity laws.
- `Completeness/DecodeRel.agda` — `decode-rel`, `decode-roundtrip-rel`
  (constructive).
- `Completeness/DecodeAttempt.agda` — `decode-attempt-Linear`,
  `decode`, `bridge`.  Candidate infrastructure for Route 1.
- `Completeness/DecodeProperties.agda` — `extract-prefix-from-↭`,
  permutation absorbers.  Candidate infrastructure for Route 1.
- `Completeness/Linearity.agda` — `Linear` invariant.  Candidate
  infrastructure for Routes 1 and 3.

## Orphaned files

Following the Path B switchover, the heavy inductive-decomposition
modules (`RespIso/TensorTensor.agda`, `ComposeCompose.agda`,
`AtomicCompound.agda`, the `Discharge/{AgenCompound1E,IsoDecomposeTT,
IsoDecomposeCC,CrossOC,CrossCO}.agda` group, and `BlockDiagonal/*`)
were deleted.

Files still present under `Completeness/DecodeRel/RespIso/` and their
status:

- `RespIso/AgenAgen.agda` — **live** (dispatcher case 2).
- `RespIso/Discharge/AtomicCompound0E.agda` — **partially live**;
  exports `NoSigma` + `Structural-coherence-≈Term-noσ` (Mac Lane
  discharge via `solveM`), used in dispatcher case 1.  The rest is
  reference material.
- `RespIso/Atomic.agda`, `AtomicData.agda`, `AlphaBackwardSigma.agda`,
  `AlphaForwardSigma.agda`, `IdSigma.agda`, `UnitCross.agda` — fully
  orphaned (not reached from `completeness-full`); self-referencing
  only.  Candidates for deletion if reference value is exhausted.
