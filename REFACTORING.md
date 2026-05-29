# Goal: complete the completeness theorem

`Categories.APROP.Hypergraph.CompletenessFull.completeness-full :
⟪ f ⟫ ≅ᴴ ⟪ g ⟫ → f ≈Term g` builds cleanly with `⟪_⟫` from
`Translation` (pruned `hComposeP`), keeping symmetry with
`Soundness.agda`. `Solver/Tests.agda` exercises 20 categorical-axiom-
shaped equations end-to-end through `completeness-full ∘ findIso` —
all 20 pass.

This file documents the **current trust surface** and the constructive
narrowings landed. Session-by-session narratives have been removed;
consult `git log` for history.

## Trust surface

The completeness path depends on a single record `Build` exposed in
`Completeness/DecodeRespIso.agda`. The record has three fields:

| Field | Status |
|---|---|
| `process-term-permute-aligned` (c') | Constructively derivable from `APROPMacLaneAtoms` |
| `X-permute-self-loop-id` (XSL) | Narrows to a single Kelly-coherence postulate via `Sub/KellyCoherence.agda` |
| `decode-rel-≈-decode` (F) | Narrows to 11 atomic per-constructor fields via `Completeness/DecoderAgreementSafe.agda` |

`Solver/TestsTrust.agda` postulates the whole `Build` record (the
project's single trust point); downstream consumers are `--safe` clean.

A generic `Categories.APROP.Hypergraph.CompletenessAssumptions.Assumptions`
record (no APROP imports, all fields stated in `FreeMonoidalData` /
`FinBij` terms) currently exposes one field, `smc-faithfulness`, that
is consumed by `Sub/XSLByFinBij.agda` to derive the Fin-level
`SelfLoopPostulate`. The remaining APROP-specific obligations cannot
be moved to `Assumptions` (their types mention `Hypergraph FlatGen`,
`⟪_⟫F`, `process-edges`, etc.).

## FreeSMC reduction of `APROPMacLaneAtoms` (in progress)

`Categories/FreeSMC/*` re-states the c'-chain atoms at the generic
`FreeMonoidalData ⦃ Symm ≤ v ⦄` level (no APROP/Hypergraph), so the
trust collapses toward symmetric-group coherence rather than anything
APROP-specific.  `MacLaneAtoms.SMCMacLaneAtoms` is the Sense-1 record;
`Discharge/APROPMacLaneFromSMC.agda` bridges it to `APROPMacLaneAtoms`.

Discharged constructively (`--safe`, no postulates):
- `Steps.fire-clean` (splitJoin / subst₂ elimination, definitional).
- `FinalStackPerm` + `StackPerm.swap-stack-↭` (atom-1 stack witness).
- `ProcessFinal.process-steps-final-↭` (final stack respects edge-↭, via
  net-multiset invariant) — removed `process-steps-final-↭` as a field.
- `BraidBlock.braid-natural`, `BraidPermute.{permute-swap-refl-σ-block,
  permute-rotate}`, `SigmaBlockTensor.σ⊗-from-hexagon₂`,
  `PermuteInverse.{permute-inverse-left,pvv-inverse-left}` — the
  generator-slide / permute-inverse tooling.
- `SigmaBlockHexagon` was generalised from `sig-dec` to `d`
  (3 APROP consumers updated; XSL chain re-verified).
- `swap-core` is now a DERIVED value (was a field): proved from `swap-gens`
  + `pvv-inverse-left`, factoring/cancelling the input permute.

Residual fields of `SMCMacLaneAtoms` (5): `permute-faithfulness` (kept,
= the XSL Kelly residual), `swap-gens` (bare 2-generator interchange),
`process-steps-↭-term`, `bridge-cross`, `bridge-reorder`.

## c' (`process-term-permute-aligned`) — current factorisation

The c' field is constructively derived in
`Discharge/ProcessTermPermuteAlignedFromIrreducibles.agda` via:

```agda
process-term-permute-aligned-from-atoms
  : APROPMacLaneAtoms → <c'-signature>
```

with **NO postulates** and `--safe --with-K` clean throughout the chain.

`APROPMacLaneAtoms` is the minimal sound residual record. 2 top-level
fields, 4 effective atoms:

| Atom | Source | Nature |
|---|---|---|
| `swap-atom-aligned` | `Sub/SwapAtomAssumptionDischarge.SwapAtomResidual` | Mac Lane chase on two adjacent independent edges (interchange via `⊗-∘-dist`) |
| `swap-with-rest-aligned` | same | Single swap with non-trivial rest list (Mac Lane + stack-permute coherence) |
| `swap-already-fires` | same | Topological soundness: permuted edge order respects production-then-consumption |
| `bridge-to-g-permute` | inline (verbatim copy of `ProcessTermAligned2Residual.bridge-to-g-permute`) | Bridge between `proj₂ proc-G` and `proj₂ proc-F` under iso + `↭` |

All four atoms are mathematically true (no counter-example, sound shape)
but not yet constructively inhabited.

### Constructive closures landed

Obligations that previously appeared as residuals and are NOW
constructively discharged (no longer fields of `APROPMacLaneAtoms`):

- **A-nat** (`AllFire-natural-range`): `Sub/AllFireNatural.agda`,
  ~937 LOC, structural induction on `f`.
- **AllFire transport under bijection** (`AllFire-resp-aligned-tabulate`):
  ~60 LOC in `Sub/IsoInducesEdgePerm.agda`; transports `AllFire`
  through any ein/eout/dom-compatible Fin bijection.
- **`iso-induces-edge-↭-direct`**: constructively closed in
  `Sub/IsoInducesEdgePerm.iso-induces-edge-residual` via a
  cardinality-cast ψF + `AllFire-natural-range-source` applied
  through `AllFire-resp-aligned-tabulate`.
- **`prep-aligned` + `trans-intermediate-allfire`**:
  `Sub/SwapAtomAssumptionDischarge.agda`.
- **`bridge-to-g-list`**: top-level discharge in
  `Sub/BridgeToGFull.agda` taking `walk + sob` extras.
- **`Linear-hyp`**: removed as a record field; threaded per call-site
  via `⟪⟫-Linear f`.

### Soundness bugs found and fixed

Two previously-introduced residual fields had **provably false** type
signatures; both were eliminated this session:

1. `permute-eq-bridge` (`Σ stack-eq P`) — refuted by `Sub/StackListEq.agda`'s
   4-atom counter-example. Replaced by the native `↭`-form
   `bridge-to-g-permute` (no propositional list equality).
2. `FromAPROP-iso-from-Translation-iso` (full vertex bijection) —
   refuted by the same pruning counter-example as `BoundaryRespectsIso`.
   Replaced by `iso-induces-edge-↭-direct` (no vertex bijection in the
   output).

## XSL — current factorisation

Narrowed to a single Kelly's-coherence postulate in
`Sub/KellyCoherence.agda`:

```agda
postulate Kelly-faithfulness : FaithfulnessResidual ...
```

`XSLByFinBij.WithFaithfulnessResidual` derives `SelfLoopPostulate`
(Fin/Unique level), and `XToFinLift` extends to the X-level XSL on
mapped lists with `InjectiveVlab + Unique` preconditions.

The full XSL on arbitrary X-lists is **false** (counter-example:
`xs = [a, a]`, `r = swap a a refl` gives σ ≢ id at X-level); the chain
only produces it on the Fin-Unique pre-image cases that actually arise
in the decoder consumer path.

The Mac Lane chain in `Categories/PermuteCoherence/*` (~3000 LOC) is
constructive except for the Kelly postulate; it's reusable SMC
permute-coherence infrastructure independent of the APROP context.

## F (`decode-rel-≈-decode`) — current factorisation

`Completeness/DecoderAgreementSafe.agda` (`--safe`-clean) decomposes
the field into **11 yet-narrower per-constructor fields**:

- 9 atomic-constructor fields: `decode-rel-≈-decode-{Agen,σ,id,λ⇒,λ⇐,
  ρ⇒,ρ⇐,α⇒,α⇐}-T` (agreement at a single atomic shape).
- 2 distributivity fields: `decode-∘-shape-T`, `decode-⊗-shape-T`.

`DecoderAgreementSafe.WithAssumptions` performs structural induction
on `f` to derive the polymorphic `decode-rel-≈-decode` from these 11
fields. The ∘ and ⊗ cases are FULLY CONSTRUCTIVE via IHs +
distributivity; the 9 atomic cases mirror the still-open
`decode-roundtrip-{Agen,σ,id,...}` postulates from
`DecodeRoundtrip.agda`.

`DecodeRespIso.buildFromResiduals` takes residual records for both c'
(via `ProcessTermAligned2Residual`) and F (via `DecodeShapeResiduals`
+ `RhoShapeResidual` + `agenSigmaResiduals` + α⇒/α⇐ atomic) and
constructs a `Build` value.

The current `TestsTrust.agda` uses the coarse single-postulate path;
the 15-field path is available for users who want finer auditability.

## Architectural blockers (constructive refutations in tree)

Three intermediate lemmas are **provably false** in general and have
constructive `→ ⊥` witnesses in the codebase. Future refactors must
not regress to these shapes:

1. **`boundary-respects-iso`** — `⟪f⟫ ≅ᴴ ⟪g⟫ → ⟪f⟫F ≅ᴴ ⟪g⟫F`.
   Counter-example: `f = id ∘ id` vs `g = id`. Translation prunes the
   redundant vertex (nV=1); FromAPROP keeps it (nV=2); no Fin-bijection
   exists. File: `Completeness/BoundaryRespectsIso.agda`.

2. **`FromAPROP-iso-from-Translation-iso`** — same vertex-counting
   issue applied to the full `FromAPROP-Iso-Data` record. The
   constructive refutation lives in `Sub/IsoInducesEdgePerm.agda`
   Section 10 (`module Refutation`).

3. **`stack-list-eq`** — the propositional list equality between
   vlab-mapped final stacks. Counter-example: `f = Agen φ₁ ⊗ Agen φ₂`
   vs `g = σ ∘ (Agen φ₂ ⊗ Agen φ₁) ∘ σ` produces stacks `[w,z]` vs
   `[z,w]` — same multiset, list-different. File: `Sub/StackListEq.agda`.

Standing implication: any field whose return type contains a
propositional equality between FromAPROP-side vertex-list-derived data
must be restated using `Perm.↭` (multiset), not `_≡_`. Several
sessions' worth of soundness bugs traced to this issue.

## What remains to fully close `Build`

To produce an unconditional, postulate-free `completeness-full`,
discharge the residuals listed in the trust surface table:

- **`APROPMacLaneAtoms`'s 4 atoms** (c'): require extending `solveM`
  to handle σ-naturality, OR implementing one of the architectural
  routes below. Estimated 500-1500 LOC.
- **`Kelly-faithfulness` postulate** (XSL): import / formalise the
  Mac Lane / Kelly symmetric monoidal coherence theorem. Estimated
  500-1000 LOC if not directly available in agda-categories.
- **`decode-rel-≈-decode`** (F): mostly structural induction; the 11
  atomic per-constructor cases mirror the still-open
  `decode-roundtrip-{Agen,σ,id,...}` postulates from
  `DecodeRoundtrip.agda`.

### Routes to discharge `APROPMacLaneAtoms`

#### Route 1 — Iso-invariant decoder

Define `decode-of : Hypergraph → HomTerm` that is iso-invariant,
prove `H ≅ᴴ K → decode-of H ≈Term decode-of K`. The architectural
blockers above DO NOT recur for the decoder structure: the σ content
lives in the `permute`-fragment Kelly chase, not in σ-naturality on
generators.

Estimated 1100-1550 LOC across `process-edges-↭`,
`vertex-relabel-invariance`, `extract-prefix-under-relabel`, and the
tensor/compose threading.

The viability probe `Completeness/EdgeReorder.agda` shows the natural
lemma is false without a topological-success precondition (AllFire),
but holds under that precondition.

#### Route 2 — Solver-emits-≈Term (test-coverage only)

Change `findIso : f g → Maybe (⟪f⟫ ≅ᴴ ⟪g⟫ × f ≈Term g)`. The
postulate stays in `Build` but is never invoked by the standard
pipeline. Estimated 660 LOC, primarily in `FindIso/{Search,Match}.agda`.

Does NOT discharge the postulate for arbitrary isos.

#### Route 3 — Linear / vertex-counting argument (speculative)

Prove `Build` for the *Linear* fragment via a multiset/counting
argument at the hypergraph level. Not yet investigated.

## Live infrastructure (constructive, reusable)

- `Completeness/PermutationCoherence.agda` —
  `↭-to-≅ : xs ↭ ys → unflatten xs ≅ unflatten ys`. Used by
  `bridge`/`bridge⁻¹` derivations.
- `Completeness/Unflatten.agda` — `unflatten`/`unflatten-flatten-≈`,
  the `bridge` half-isomorphism foundation.
- `Completeness/BridgeOps.agda` — `bridge-∘`/`bridge-⊗`/
  `bridge-⊗-decompose`, constructive distributivity laws.
- `Completeness/DecodeRel.agda` — `decode-rel`, `decode-roundtrip-rel`
  (constructive).
- `Completeness/DecodeAttempt.agda` — `decode-attempt-Linear`,
  `decode`, `bridge`.
- `Completeness/DecodeProperties.agda` — `extract-prefix-from-↭`,
  permutation absorbers.
- `Completeness/Linearity.agda` — `Linear` invariant.
- `Completeness/LinearityIso.agda` — `Linear-resp-iso` (~440 LOC, fully
  constructive). Template for any future iso-respecting count proof.
- `Categories/PermuteCoherence/*` — reusable SMC permute-coherence
  infrastructure (FinBij faithfulness scaffolding, canonical
  bubble-sort decomposition, constructive `permute-inverse-{left,right}`).
- `Sub/SigmaBlockHexagon.agda` — constructive σ-block Yang-Baxter
  identity (~1927 LOC). Available for any future σ-fragment closures.

## Dispatcher (`nf-resp-≅ᴴ` in `WithAssumptions`)

Case-splits on the shape of `f`/`g` before falling through to the c'
consumer:

1. Both `NoSigma` → `Structural-coherence-≈Term-noσ` (Mac Lane,
   constructive via `solveM`).
2. Both atomic `Agen` → `decode-rel-resp-≅ᴴ-Agen-Agen` (constructive
   in `RespIso/AgenAgen.agda`).
3. Edge-count contradictions: any `NoAgen` vs `HasAgen` (or atomic
   `IsAgen`) mix is vacuous via `ψ`/`ψ⁻¹` on `Fin 0`.
4. Both `SingleAgen` (σ-free, exactly one `Agen` subterm each) →
   `single-agen-coherence-≈Term`, **fully discharged constructively**
   in `Completeness/DecodeRel/Inductive.agda` (three sub-cases on the
   Agen edge's interface):
   - **ein non-empty**: `single-agen-NF-coherence-discharge-nonempty`.
   - **ein empty AND eout non-empty**:
     `single-agen-NF-coherence-discharge-nonempty-eout`.
   - **both ein and eout empty** (scalar `u : 1 → 1`):
     `single-agen-NF-coherence-discharge-scalar`.
5. Else → `nf-resp-≅ᴴ-residual` (consumes c' via `decode-rel-resp-iso`).

After (1)-(4), the residual fires only when at least one side contains
a σ subterm OR contains ≥2 Agen subterms.

## Orphaned files

Reference-only material under `Completeness/DecodeRel/RespIso/` that
is no longer reached from `completeness-full`:

- `RespIso/Atomic.agda`, `AtomicData.agda`, `AlphaBackwardSigma.agda`,
  `AlphaForwardSigma.agda`, `IdSigma.agda`, `UnitCross.agda` — fully
  orphaned; self-referencing only. Candidates for deletion if reference
  value is exhausted.

Live files in `Completeness/DecodeRel/RespIso/`:

- `RespIso/AgenAgen.agda` — dispatcher case 2.
- `RespIso/Discharge/AtomicCompound0E.agda` — exports `NoSigma` +
  `Structural-coherence-≈Term-noσ` (Mac Lane discharge via `solveM`),
  used in dispatcher case 1.
