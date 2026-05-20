# Goal: complete the completeness theorem

`Categories.APROP.Hypergraph.CompletenessFull.completeness-full :
⟪ f ⟫ ≅ᴴ ⟪ g ⟫ → f ≈Term g` builds cleanly with `⟪_⟫` from
`Translation` (pruned `hComposeP`), keeping symmetry with
`Soundness.agda`. `Solver/Tests.agda` exercises 20 categorical-axiom-
shaped equations end-to-end through `completeness-full ∘ findIso` —
all 20 pass.

## Current postulate inventory

The completeness path depends on **two narrow postulates**, bundled
into the `CompletenessAssumptions` record in
`Completeness/DecodeRel/Inductive.agda`:

```agda
record CompletenessAssumptions : Set where
  field
    single-agen-NF-coherence
      : ∀ {A B} {f g : HomTerm A B}
          (sf : SingleAgen f) (sg : SingleAgen g)
          (flat-A-eq : flatten (SingleAgenGen.Aᵢ (single-agen-u sf))
                     ≡ flatten (SingleAgenGen.Aᵢ (single-agen-u sg)))
          (flat-B-eq : flatten (SingleAgenGen.Bᵢ (single-agen-u sf))
                     ≡ flatten (SingleAgenGen.Bᵢ (single-agen-u sg)))
          (flat-u-eq : subst₂ FlatGen flat-A-eq flat-B-eq
                          (flat (SingleAgenGen.u (single-agen-u sf)))
                       ≡ flat (SingleAgenGen.u (single-agen-u sg)))
      → ⟪ f ⟫ ≅ᴴ ⟪ g ⟫
      → f ≈Term g

    nf-resp-≅ᴴ-residual
      : ∀ {A B} (f g : HomTerm A B)
      → ⟪ f ⟫ ≅ᴴ ⟪ g ⟫
      → bridge f ≈Term bridge g
```

`CompletenessFull.agda` takes this record as a parameter and is
therefore `--safe`-clean: the trust is exposed only at the call site
that supplies a record instance.

`decode-rel-resp-≅ᴴ-full` is a 4-line composition
`trans (decode-roundtrip-rel f) (trans (nf-resp-≅ᴴ iso) (sym
(decode-roundtrip-rel g)))`, no recursion.  `decode-roundtrip-rel` is
fully constructive (in `DecodeRel.agda`), so the bridge
`decode-rel f ≈Term bridge f` costs nothing.

Trust content of `single-agen-NF-coherence`: only the Mac-Lane chase
that closes the σ-free wrappers around an already-aligned generator.
The iso → flat-data step is constructive (`single-agen-flat-data` in
`Inductive.agda`).

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
   three flat equalities via `single-agen-flat-data` and feeds them
   to the narrowed `single-agen-NF-coherence`.
5. Else → `nf-resp-≅ᴴ-residual`.

After (1)–(4), the residual fires only when at least one side contains
a σ subterm OR contains ≥2 Agen subterms.

## Architectural blockers (Field 2 / `nf-resp-≅ᴴ-residual`)

Two counter-example families established by independent investigation:

1. **σ-naturality half-swap (tensor)**: `Agen u ⊗ id` vs `id ⊗ Agen u`
   at `unit ⊗ A → unit ⊗ A` are `≈Term`-equal via σ-naturality, their
   hypergraphs are `≅ᴴ`-isomorphic via a half-swap, but no
   L→L-restricting sub-iso exists (Soundness's σ-naturality witness is
   literally the half-swap producer).

2. **idˡ/idʳ-absorption (composition)**: `Agen u ∘ id` vs
   `id ∘ Agen u` at `unit → unit → unit` are `≈Term`-equal via
   `idˡ`/`idʳ`, their composite hypergraphs are isomorphic, but
   sub-iso extraction is impossible (one composite slice has 1 edge,
   the "extracted" sub-iso would need 0 edges).

These pathologies architecturally block the **inductive** strategies
that powered the old `decode-rel-resp-≅ᴴ-full` (decomposing isos
recursively through `⊗⊗`/`∘∘`/`⊗∘`/`∘⊗`).  Path B bypassed cases (1)–(4)
above, leaving only the residual.  Direct inductive proof of the
residual is not on the table — see "Alternative paths for Field 2"
below.

### Earlier unsoundness retractions (cautionary)

- `425bf16` reverted `⊗-∘-dist-FromAPROP-iso` and its mirrors:
  vertex-count mismatch (`⟪p ⊗ q⟫` and `⟪(p⊗id) ∘ (id⊗q)⟫` differ by
  `nA + nB` under unpruned `hCompose`).  `_≅ᴴ_` requires a
  Fin-bijection on vertices.
- Earlier `perm-eq-from-iso` split of `Structural-coherence-≈Term` was
  reverted: `Data.List.Relation.Binary.Permutation.Propositional._↭_`
  is not truncated, so the propositional equality of permutations was
  unprovable as stated.

## Recent narrowing: Field 1 trust content

Landed in `Completeness/DecodeRel/Inductive.agda` (after the
`SingleAgen?` classifier):

- `NoSigma→NoAgen`, `nE-SingleAgen`, `SingleAgen-edge` — structural
  helpers locating the unique `Agen` edge inside `⟪f⟫`.
- `SingleAgenGen` record + `single-agen-u` — extractor for the
  underlying `mor Aᵢ Bᵢ` generator (independent of `single-agen-strip`).
- `elab-at-SingleAgen-edge` — at the unique Agen edge, `elab ⟪f⟫`
  equals `flat u` under two existentially-packaged transports.
  Inductive cases share `fold-elab-step`, composing the IH on the
  sub-term with `hComposeP-impl.elab-c-inj₁/inj₂` and
  `hTensor-impl.elab-c-inj₁/inj₂`; base case `Agen u` discharges to
  `refl` via Agda unification on `hGen`'s internal `lem-in`/`lem-out`.
- `single-agen-flat-data` — combines `ψ-elab` at `SingleAgen-edge sf`
  with `elab-at-SingleAgen-edge` on both sides, aligns
  `ψ (SingleAgen-edge sf)` with `SingleAgen-edge sg` via `Fin 1`
  uniqueness (using `nE-SingleAgen sg`), peels the `subst₂`s, and
  emits the triple `(flat-A-eq, flat-B-eq, flat-u-eq)`.
- `single-agen-u-strip-{Aᵢ,Bᵢ,u}` — consistency lemmas witnessing
  that `single-agen-u` and `single-agen-strip` produce the same
  underlying generator data.  Foundational for the wrapper-closure
  work below (lets future code switch between Gen-form and NF-form
  without re-running structural induction at each call site).
- **Rewired `CompletenessAssumptions.single-agen-NF-coherence`**: now
  takes `SingleAgen` witnesses and the three flat equalities (rather
  than `SingleAgenNF` records).
- **Rewired `WithAssumptions.single-agen-coherence-≈Term`**: derives
  the flat data via `single-agen-flat-data` and passes the triple
  into the narrowed postulate.

All `--safe`-clean.  `CompletenessFull.agda` and `Solver/Tests.agda`
both still pass (20/20 tests).  Postulate count unchanged at 2;
content strictly narrower.

### Why type alignment can't fully collapse

`u_f : mor Aᵢ_f Bᵢ_f` and `u_g : mor Aᵢ_g Bᵢ_g` live in different
`mor` types.  The iso forces only `flatten Aᵢ_f ≡ flatten Aᵢ_g`,
not `Aᵢ_f ≡ Aᵢ_g`, because `flatten` is not injective on `ObjTerm`
(`unit ⊗ A` and `A` flatten the same).  Similarly the strip's wrapper
types `YL ⊗ Aᵢ ⊗ YR` are accumulated outside-in from syntactic shape
and generally differ across `f, g` even at equal flatten.  The
Mac-Lane chase closes the wrappers *once* the ObjTerm-level alignment
is built — that's what the postulate still owns.

## Next directions

### Field 1 — Mac-Lane wrapper closure

Two candidate routes:

1. **Push the discharge into the constructive Mac-Lane solver**: extend
   `solveM` (`Categories.MonoidalCoherence`, ~378 LOC) to handle terms
   with a single `Agen u`-edge "pinned" at the centre.  The wrappers
   around it reduce to a NoSigma equation, modulo a single
   subst-on-the-inner-u.  ~100–300 LOC; reusable infrastructure
   beyond this file.
2. **Two-sided strip symmetric closure**: build the strip records via
   `single-agen-strip`, observe both sides reduce to `c-to ∘ (id ⊗
   (Agen u ⊗ id)) ∘ c-from`, and bridge the two via the flat
   equalities + Mac-Lane isos derived from `unflatten-flatten-≈`.
   ~100–200 LOC; more concrete than (1) but tied to the current strip
   shape.  Uses the new `single-agen-u-strip-*` consistency lemmas.

### Field 2 — Architecturally blocked; alternative paths

Direct inductive proof of `nf-resp-≅ᴴ-residual` is blocked by the
σ-naturality and idˡ/idʳ counter-examples above.  Two viable routes:

- **Solver-emitting-≈Term** — modify `Solver/findIso` to emit a
  parallel `≈Term` rewrite witness alongside the iso (each
  `pairUp`/`tryEdge`/`verify` step emits a parallel rewrite).
  Localized change inside `Solver/`; sidesteps the residual at all
  current call sites.  Replaces the *theorem* rather than proves it.
- **`≅ᴴ`-invariant normal-form decoder** — define
  `nf : Hypergraph → HomTerm` so that `⟪f⟫ ≅ᴴ ⟪g⟫ → nf ⟪f⟫ ≈Term
  nf ⟪g⟫`.  `Completeness/DecodeAttempt.agda` (`decode-attempt-Linear`)
  and `Completeness/Linearity.agda` are candidate infrastructure.
  Real proof of the underlying claim; substantial (~500–1000 LOC).

## Helpers and infrastructure (still live)

- `Completeness/PermutationCoherence.agda` —
  `↭-to-≅ : xs ↭ ys → unflatten xs ≅ unflatten ys`.  Used by
  `bridge`/`bridge⁻¹` derivations and would be reused by Field 1
  Mac-Lane bridge construction.
- `Completeness/Unflatten.agda` — `unflatten`/`unflatten-flatten-≈`,
  the `bridge` half-isomorphism foundation.
- `Completeness/BridgeOps.agda` — `bridge-∘`/`bridge-⊗`/
  `bridge-⊗-decompose`, constructive distributivity laws.
- `Completeness/DecodeRel.agda` — `decode-rel`, `decode-roundtrip-rel`
  (constructive).
- `Completeness/Linearity.agda` — `Linear` invariant on hypergraphs;
  natural framework for label-multiset counting.

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
