# Goal: complete the completeness theorem

The completeness theorem `Categories.APROP.Hypergraph.CompletenessFull.completeness-full`
is now wired through `decode-rel-resp-≅ᴴ-full` (in `DecodeRel/Inductive.agda`)
and depends on **five narrow postulates** in three sub-modules.  All of
the atomic-case work (Phase 1) and the inductive framework (Phase 2) have
been discharged.  What remains is targeted vertex/edge bookkeeping and
two pieces of symmetric-monoidal coherence content.

## Current state

`CompletenessFull.completeness-full : ⟪ f ⟫ ≅ᴴ ⟪ g ⟫ → f ≈Term g` builds
cleanly.  The dependency tree of remaining postulates:

```
completeness-full
└── decode-rel-resp-≅ᴴ-full       (Inductive.agda — fully proved)
    ├── decode-rel-resp-≅ᴴ-atomic (Atomic.agda — fully proved, Phase 1)
    ├── decode-rel-resp-≅ᴴ-atomic-compound  ─┐
    ├── decode-rel-resp-≅ᴴ-compound-atomic ─┤ derived from each other
    │   └── 2 postulates in AtomicCompound.agda:
    │       • atomic-compound-0E  (structural-coherence equation)
    │       • Agen-compound-1E    (1-edge decomposition)
    │   (nE-Agen-iso-1 already discharged via Discharge/NEAgenIso1.agda)
    ├── decode-rel-resp-≅ᴴ-⊗⊗     (TensorTensor.agda)
    │   └── iso-decompose-⊗⊗      (1 postulate — vertex/edge bookkeeping)
    ├── decode-rel-resp-≅ᴴ-∘∘     (ComposeCompose.agda)
    │   └── iso-decompose-∘∘      (1 postulate — deepest math)
    ├── decode-rel-resp-≅ᴴ-∘⊗     (Inductive.agda — 1 postulate)
    └── decode-rel-resp-≅ᴴ-⊗∘     (derived from -∘⊗ via sym-≅ᴴ)
```

| Path postulate count | After |
|---|---:|
| Original (indexed Hypergraph, algorithmic decode) | 9–10 |
| After refactors A, B, C | 1 (top-level `decode-rel-resp-≅ᴴ`) |
| After Phase 1 (atomic dispatcher) | 1 (still top-level, atomic case dispatched) |
| After Phase 2 framework | **5** narrow postulates |

## Remaining postulates and plans

### 1. `iso-decompose-⊗⊗` (TensorTensor.agda)

```agda
iso-decompose-⊗⊗
  : ∀ {A B C D}
      (f₁ : HomTerm A B) (g₁ : HomTerm C D)
      (f₂ : HomTerm A B) (g₂ : HomTerm C D)
  → ⟪ f₁ ⊗₁ g₁ ⟫ ≅ᴴ ⟪ f₂ ⊗₁ g₂ ⟫
  → (⟪ f₁ ⟫ ≅ᴴ ⟪ f₂ ⟫) × (⟪ g₁ ⟫ ≅ᴴ ⟪ g₂ ⟫)
```

**Soundness**: confirmed sound after investigation.  Boundary equations
`φ-dom : K.dom ≡ map φ G.dom` (position-ordered list equality, with both
sides split as `injL …-dom ++ injR …-dom` of length `|flatten A|`) force
`φ` to map f₁'s boundary into f₂'s boundary element-wise; propagation
through `ψ-ein`/`ψ-eout` extends "structurally straight" behaviour into
the interior.

**Plan**: ~100–200 LOC of vertex/edge bookkeeping in two passes.
1. Pass 1: derive half-restricted `φ` from `φ-dom`/`φ-cod` (slice the
   bijection at index `|flatten A|`; use `splitAt`-properties from
   `Data.Fin.Properties`).
2. Pass 2: derive half-restricted `ψ` from `ψ-ein`/`ψ-eout` + the
   half-restricted `φ`.  Edges with at least one boundary endpoint
   are forced into the matching half; for purely-interior edges,
   restrict via `splitAt` on `Fin (G.nE)` analogous to `φ`.
3. Assemble two `_≅ᴴ_` records (one for each half) using the existing
   `hTensor-impl.elab-c-inj₁/₂` to manage the `subst₂ Gen` transports.

The forward direction `hTensor-resp-≅ᴴ` likely exists in
`Hypergraph.Congruence`; the reverse machinery is the analogue we need.

### 2. `iso-decompose-∘∘` (ComposeCompose.agda)

```agda
iso-decompose-∘∘
  : ∀ {A B X Y} (g₁ : HomTerm X B) (f₁ : HomTerm A X)
                  (g₂ : HomTerm Y B) (f₂ : HomTerm A Y)
  → ⟪ g₁ ∘ f₁ ⟫ ≅ᴴ ⟪ g₂ ∘ f₂ ⟫
  → Σ (HomTerm A X) λ f₂' →
    Σ (HomTerm X B) λ g₂' →
        (⟪ f₁ ⟫ ≅ᴴ ⟪ f₂' ⟫)
      × (⟪ g₁ ⟫ ≅ᴴ ⟪ g₂' ⟫)
      × (decode-rel (g₂' ∘ f₂') ≈Term decode-rel (g₂ ∘ f₂))
```

**This is the deepest remaining mathematical content.**  The
existential `f₂'`/`g₂'` ranges over `HomTerm`s at the same middle
object `X` as f₁/g₁ (matching the IH's required type), with a
`≈Term`-bridge absorbing the X-vs-Y middle-object mismatch.

**Plan (5 named sub-lemmas, sketched in ComposeCompose.agda)**:
1. `partition-ψ`: split the edge bijection along the G/K boundary
   using `hCompose-impl.elab-c-inj₁/₂` (`FromAPROP.agda` lines
   ≈488–536).
2. `partition-φ`: split the vertex bijection.  Subtlety: `hCompose`
   identifies boundary vertices ("remap"), so φ only partitions after
   quotienting boundary vertices — needs the existing `ein-coh`/
   `eout-coh` plus `partition-ψ`.
3. `extract-sub-iso-f`, `extract-sub-iso-g`: build the `_≅ᴴ_` records
   from the partitioned data using `subst₂-resp-≅ᴴ`.
4. `bridge-coherence`: construct the `≈Term` bridge from `g₂' ∘ f₂'`
   to `g₂ ∘ f₂`.  Uses associativity, the X-vs-Y coherence iso
   (derived from `unflatten-flatten-≈`), and `identityˡ`/`identityʳ`.

Estimate: ~500–1000 LOC, ~1-2 weeks of focused work.

A *narrower* deliverable (X ≡ Y case only — same middle object): if
the iso preserves the middle, the bridge collapses to refl and only
steps (1)–(3) are needed.  Roughly ~200–400 LOC.

### 3. `decode-rel-resp-≅ᴴ-atomic-compound-0E` (AtomicCompound.agda)

```agda
decode-rel-resp-≅ᴴ-atomic-compound-0E
  : ∀ {A B} {f g : HomTerm A B}
  → Atomic f → Compound g
  → nE ⟪ g ⟫ ≡ 0
  → ⟪ f ⟫ ≅ᴴ ⟪ g ⟫
  → decode-rel f ≈Term decode-rel g
```

Both `f` and `g` are 0-edge structural morphisms (no `Agen`
sub-occurrences); the existing `Discharge/AtomicCompound0E.agda`
proves the inductive characterisation that `nE ⟪g⟫ ≡ 0` implies `g` is
`Structural` (no `Agen` anywhere), and dismisses the `Agen` LHS branch.

**What's left**: a symmetric-monoidal coherence theorem stating that
any two `Structural` `HomTerm`s of matching type with isomorphic
hypergraph translations are `≈Term`-equal.  This is Mac Lane coherence
extended to `σ`.

**Plan**:
- Path A (broad): extend `Categories.MonoidalCoherence.Solver.solveM`
  (currently Mac Lane only) to symmetric monoidal categories — handle
  `σ` via permutation tracking.  Roughly 1–2 weeks; produces a
  general-purpose tactic discharging many other postulates simultaneously.
- Path B (targeted): hand-prove the coherence equation by induction
  on `Structural g`, threading `σ∘[f⊗g]≈[g⊗f]∘σ`, `α-comm`,
  `triangle`, `pentagon`, and (in the σ branch) the existing
  `σ-flatten-empty-is-id` from `RespIso/IdSigma.agda` and the
  hexagon-based derivations from `RespIso/AlphaForwardSigma.agda`.
  Roughly 3–5 days.

### 4. `decode-rel-resp-≅ᴴ-Agen-compound-1E` (AtomicCompound.agda)

```agda
decode-rel-resp-≅ᴴ-Agen-compound-1E
  : ∀ {A B} {g : mor A B} {h : HomTerm A B}
  → Compound h
  → nE ⟪ h ⟫ ≡ 1
  → ⟪ Agen g ⟫ ≅ᴴ ⟪ h ⟫
  → decode-rel (Agen g) ≈Term decode-rel h
```

`h` is compound with exactly one edge total; exactly one sub-term of
`h` contains the unique `Agen` (with the same generator `g` as the LHS
by `ψ-elab`), and the other sub-term is `Structural` (0 edges).
`Discharge/AgenCompound1E.agda` already splits this into four
shape-routed cases (∘-left, ∘-right, ⊗-left, ⊗-right).

**Plan**:
1. Extract sub-iso `⟪ Agen g ⟫ ≅ᴴ ⟪ h-with-Agen ⟫` (the sub-term
   containing the unique edge) — `iso-decompose-⊗⊗`/`-∘∘` provides
   the surrounding decomposition.
2. By Agen-Agen (already proved in `RespIso/AgenAgen.agda`), the
   underlying generators agree.
3. The structural sibling (0 edges) collapses to identity-like under
   `atomic-compound-0E` (postulate above) — or more directly, via the
   `idˡ`/`idʳ` axiom + bridge.

Total ~200–400 LOC, but depends on items 1 (iso-decompose) and 3
(atomic-compound-0E) being discharged.

### 5. `decode-rel-resp-≅ᴴ-∘⊗` (Inductive.agda)

```agda
decode-rel-resp-≅ᴴ-∘⊗
  : ∀ {Ap Aq Bp Bq X}
      (g : HomTerm X (Bp ⊗₀ Bq)) (f : HomTerm (Ap ⊗₀ Aq) X)
      (p : HomTerm Ap Bp) (q : HomTerm Aq Bq)
  → ⟪ g ∘ f ⟫ ≅ᴴ ⟪ p ⊗₁ q ⟫
  → decode-rel (g ∘ f) ≈Term decode-rel (p ⊗₁ q)
```

(The symmetric `-⊗∘` is derived constructively via `sym-≅ᴴ`.)

**Plan (in `Discharge/CrossOC.agda`)**: introduce a single
`iso-decompose-∘⊗` postulate that produces interchange factors
`f' : Ap⊗Aq → X` and `g' : X → Bp⊗Bq` (at f's/g's exact endpoints, so
IH applies directly), sub-isos to f and g, and a `≈Term` bridge to
`p ⊗₁ q`.  The canonical witness shape is
`f' = γ.from ∘ (id ⊗ q)`, `g' = (p ⊗ id) ∘ γ.to` for a coherence iso
`γ : Bp ⊗ Aq ≅ X` extracted from the composite hypergraph iso —
analogous bookkeeping to `iso-decompose-∘∘` (item 2).

Estimate: ~200–400 LOC once `iso-decompose-∘∘`'s machinery is in
place; substantially less if reused.

## Dependency order for discharge

The five postulates depend on each other as follows; pick discharge
order accordingly:

1. **`iso-decompose-⊗⊗`** — independent; pure ⊗-bookkeeping.
2. **`iso-decompose-∘∘`** — independent; pure ∘-bookkeeping (but
   substantial).
3. **`decode-rel-resp-≅ᴴ-Agen-compound-1E`** — depends on
   `iso-decompose-⊗⊗`, `iso-decompose-∘∘`, and `atomic-compound-0E`.
4. **`decode-rel-resp-≅ᴴ-atomic-compound-0E`** — depends only on
   symmetric-monoidal coherence machinery.
5. **`decode-rel-resp-≅ᴴ-∘⊗`** — depends on the same bookkeeping as
   `iso-decompose-∘∘`.

Most efficient order: 1, 4 in parallel, then 2 (which unblocks 3 and
5).

## Helpers already in place

The `RespIso/Discharge/` subdirectory contains scaffolding from earlier
attempts that future work can build on:

- `Discharge/NEAgenIso1.agda` — discharged proof of `nE-Agen-iso-1`
  (`Fin 1 ↔ Fin n` forces `n = 1`).  Imported by `AtomicCompound.agda`.
- `Discharge/IsoDecomposeTT.agda` — scaffold for item 1.
- `Discharge/IsoDecomposeCC.agda` — scaffold for item 2 with 5
  named sub-lemmas identified.
- `Discharge/AtomicCompound0E.agda` — proves `nE ⟪g⟫ ≡ 0 → Structural g`
  constructively; only the symmetric-monoidal coherence step remains
  as a narrowed postulate.
- `Discharge/AgenCompound1E.agda` — four-way shape split for item 3.
- `Discharge/CrossOC.agda` / `Discharge/CrossCO.agda` — scaffold for
  item 5 and its symmetric.

## Alternative paths (still open)

- **Modify `Solver/findIso` to extract `≈Term` proofs alongside the
  iso**.  Each `pairUp`, `tryEdge`, and `verify` step would emit a
  parallel `≈Term` rewrite.  Same total effort as the direct approach,
  more localized to `Solver/`.
- **Build a normal-form decoder**.  Define `nf : Hypergraph → HomTerm`
  invariant under `≅ᴴ` (the existing `decode-attempt-Linear` is a
  candidate).  Then `decode-rel-resp-≅ᴴ-full` follows from
  `nf-resp-≅ᴴ` plus `decode-rel f ≈ nf ⟪f⟫`.
