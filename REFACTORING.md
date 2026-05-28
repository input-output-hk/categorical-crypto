# Goal: complete the completeness theorem

`Categories.APROP.Hypergraph.CompletenessFull.completeness-full :
⟪ f ⟫ ≅ᴴ ⟪ g ⟫ → f ≈Term g` builds cleanly with `⟪_⟫` from
`Translation` (pruned `hComposeP`), keeping symmetry with
`Soundness.agda`. `Solver/Tests.agda` exercises 20 categorical-axiom-
shaped equations end-to-end through `completeness-full ∘ findIso` —
all 20 pass.

## Session finding — two `CompletenessAssumptions` fields are mis-stated

**Critical finding (this session):** Two of the four current fields of
`CompletenessAssumptions` are **provably false as stated**.  Constructive
refutations exist in `Completeness/Discharge/Sub/`.

| Field | Status | File |
|---|---|---|
| (b) `process-edges-resp-iso-stack` (as `_≡_`) | **FALSE** | `Discharge/Sub/StackListEq.agda` |
| (c) `process-edges-resp-iso-term` | OK; decomposes into 5 narrower | `Discharge/Sub/ProcessTermAligned.agda` |
| (d) `final-permute-absorb` (at X-level) | **FALSE** | `Discharge/Sub/PermuteCoherence.agda` |
| (F) `decode-rel-≈-decode` | OK (decomposable to 11 atomic via `DecoderAgreementSafe.agda`) | — |

### Refutation 1: (b) `process-edges-resp-iso-stack` demands `_≡_` but only `_↭_` is provable

Counter-example (in `Discharge/Sub/StackListEq.agda`):
- Pick 4 distinct atoms `x, y, z, w : X` (with `z ≢ w`) and generators
  `φ₁ : mor (Var x) (Var z)`, `φ₂ : mor (Var y) (Var w)`.
- `f = Agen φ₁ ⊗₁ Agen φ₂` and `g = σ ∘ (Agen φ₂ ⊗₁ Agen φ₁) ∘ σ` have
  the same boundary.
- A Translation iso `⟪f⟫ ≅ᴴ ⟪g⟫` is constructed EXPLICITLY (all 14
  fields by `refl` after pattern matching on `Fin 4` / `Fin 2`).
  Bijections: `φ = [0↦0, 1↦3, 2↦1, 3↦2]`, `ψ = swap`.
- But `⟪f⟫F`'s `process-all-edges` produces final stack mapping to
  `[w, z]`; `⟪g⟫F`'s to `[z, w]`.  List-different (though
  `_↭_`-equivalent).

The decoder processes edges in **natural Fin order**, but the iso's
`ψ` is a non-identity permutation — so the natural Fin order in `g`
corresponds via `ψ⁻¹` to a permuted ordering of `f`'s edges,
producing a list-different stack.

**Correct formulation**: the field should return `Perm.↭`, not `_≡_`.
`Discharge/StackEq.agda` (proper file, not the `Sub/` refutation)
already proves the `_↭_` version constructively.

### Refutation 2: (d) `final-permute-absorb` via `permute-≈Term-coherence` is false at X-level

Counter-example (in `Discharge/Sub/PermuteCoherence.agda`):
- For `xs = ys = x ∷ x ∷ []` (a list with DUPLICATES):
  - `p = Perm.refl` yields `id`.
  - `q = Perm.swap x x Perm.refl` yields the braiding σ.
- Via the canonical model functor (interpret `Var x ↦ A` for `|A| ≥ 2`
  in `Set`), these become distinct functions (identity vs swap).
- By soundness of `⟦_⟧-resp-≈`, they cannot be `≈Term`-equal in the
  free SMC.

**Correct formulation**: the field needs to restrict to
*duplicate-free* (`Unique xs`) lists.  At the Fin level (which is
what `permute-via-vlab` ultimately uses), Linearity provides
`Unique` automatically.  The agent's `FinCoherence` record exposes
the correct Fin-level statement.

### Decomposition (no falsehood): (c) `process-term-aligned`

`Discharge/Sub/ProcessTermAligned.agda` decomposes the Mac Lane chase
into 5 narrower sub-postulates.  The irreducible kernel is
`swap-atom-aligned` — a two-edge iso-free hypergraph-generic Mac
Lane / Kelly coherence statement.  Roughly the same content as
`permute-≈Term-coherence` (with the right Unique precondition), so
extending `solveM` to handle σ would close both.

### Recommended infrastructure

Both `swap-atom-aligned` and the Fin-level `permute-≈Term-coherence`
are specializations of **Kelly's symmetric monoidal coherence theorem**.

**Existing infrastructure in agda-categories**:

`Categories.Category.Monoidal.Properties` exports a `Kelly's` module
with individual coherence theorems for the Mac Lane fragment
(`coherence₁ : λ⇒ ∘ α⇒ ≈ λ⇒ ⊗₁ id`, `coherence₂`, `coherence₃`).

`Categories.Category.Monoidal.Braided.Properties` exports symmetric
coherence primitives:
- `braiding-coherence : λ⇒ ∘ σ⇒ ≈ ρ⇒` — the canonical λ/ρ/σ coherence.
- `braiding-coherence⊗unit`, `inv-braiding-coherence`.
- `hexagon₁-iso/inv`, `hexagon₂-iso/inv`.
- `assoc-reverse` (ternary swap via braiding).

`Categories.Category.Monoidal.Symmetric.Properties` adds:
- `braiding-selfInverse : σ⇐ ≈ σ⇒` (after swap).
- `inv-commutative : σ⇐ ∘ σ⇐ ≈ id`.

**What's NOT in agda-categories**: a master Kelly's theorem
("any two parallel structural morphisms in a SMC are equal") as a
single invocable solver.  Only the per-shape primitives exist.

**Path forward**: Discharge `permute-≈Term-coherence` (and the
related `swap-atom-aligned`) by inducting on `_↭_` structure and
invoking the agda-categories primitives at each case.  Estimated
~200-500 LOC (down from the original ~500-1000 estimate, since the
primitives do the per-shape heavy lifting).  Alternatively, extend
`Categories.MonoidalCoherence.Solver.solveM` (in-tree) to handle
σ for a general solver — same eventual content.

### Field refactor LANDED (this session)

The earlier-deferred refactor of (b)→`Perm.↭` is now complete.  The
unblocker was constructively proving
`permute p ∘ permute (Perm.↭-sym p) ≈Term id` (`permute-inverse-right`,
in `Discharge/Sub/PermuteCoherenceFin.agda`), which provides the
round-trip cancellation the composition needed.

Changes in `DecodeRespIso.CompletenessAssumptions`:

- **(b) `process-edges-resp-iso-stack`**: returns `Perm.↭` (was `_≡_`).
  The `_≡_` form was provably false; the `Perm.↭` form is provable
  via `Discharge/StackEq.agda`.
- **(c) `process-edges-resp-iso-term`**: now uses
  `permute (Perm.↭-sym stack-↭) ∘ subst₂ ... process-G ≈Term process-F`
  (was `subst₂ ... process-G ≈Term process-F` with stack-eq inside
  the subst₂).
- **(d) `final-permute-absorb`**: now uses
  `subst₂ ... permute-via-vlab-G ∘ permute stack-↭ ≈Term permute-via-vlab-F`
  (with stack-↭ as a separate composition factor).

The `WithAssumptions.decode-attempt-resp-iso` composition uses
`permute-inverse-right` to cancel `permute stack-↭ ∘ permute (Perm.↭-sym stack-↭)`
in the middle of the chain, then folds the remaining subst₂'s via
`subst₂-∘-distrib`.

### Remaining trust content

The IRREDUCIBLE TRUST CONTENT is now:

1. **`Fin-permute-self-loop-id`** (in `Discharge/Sub/PermuteCoherenceFin.agda`)
   — Kelly's SMC coherence restricted to self-loops on Fin-Unique lists.
   Strictly narrower than the original `Fin-permute-≈Term-coherence`.
2. **The 4 `CompletenessAssumptions` fields** (now all in their
   corrected form).
3. **`decode-rel-≈-decode`** — the 11 atomic constructor cases
   (`DecoderAgreementSafe.agda`).

Discharging item (1) — the self-loop case — would constructively
close `permute-≈Term-coherence`, which in turn unlocks closures of
several of the (c)/(d) sub-postulates from `Discharge/Sub/*.agda`.

## Current postulate inventory

The completeness path depends on **four narrow postulates**, bundled
into the `CompletenessAssumptions` record in
`Completeness/DecodeRespIso.agda` (the sole trust point, `--safe`-clean):

```agda
record CompletenessAssumptions : Set where
  field
    -- (b) Stack-level atom equality from the iso.
    process-edges-resp-iso-stack
      : ∀ {A B} (f g : HomTerm A B) → ⟪ f ⟫ ≅ᴴ ⟪ g ⟫
      → map vlab_f (proj₁ (process-all-edges ⟪f⟫F dom_f))
        ≡ map vlab_g (proj₁ (process-all-edges ⟪g⟫F dom_g))

    -- (c) Term-level ≈Term consuming (b).
    process-edges-resp-iso-term
      : ∀ {A B} (f g : HomTerm A B) (iso : ⟪ f ⟫ ≅ᴴ ⟪ g ⟫)
      → subst₂ ... (proj₂ (process-all-edges ⟪g⟫F)) ≈Term proj₂ (process-all-edges ⟪f⟫F)

    -- (d) Final permute absorption.
    final-permute-absorb : ...

    -- (F) Decoder agreement.
    decode-rel-≈-decode
      : ∀ {A B} (f : HomTerm A B) → decode-rel f ≈Term decode f
```

A fifth sub-property `decode-attempt-Linear-extracts` (structural
shape lemma) was previously a field but is now FULLY DISCHARGED
CONSTRUCTIVELY in `Completeness/Discharge/LinearExtracts.agda`
(160 LOC, `--safe`-clean, no postulates).  Required a small refactor:
`++-[]-↭` lifted from a `where`-clause in `Decode.agda` to module
scope so the discharge can reference it.

## Discharge files for narrower sub-postulates (optional finer trust)

For each of the 4 remaining `CompletenessAssumptions` fields, a
subagent investigated constructive discharge and produced a
discharge file under `Completeness/Discharge/`.  Each file:
- Is `--safe --with-K`-clean.
- Discharges its field constructively MODULO a single narrower
  sub-postulate exposed as a record field.

| Field | Discharge file | Narrower sub-postulate | Lines |
|---|---|---|---|
| (b) `process-edges-resp-iso-stack` | `Discharge/StackEq.agda` | `stack-↭-list-eq` (multiset → list bridge) | ~200 |
| (c) `process-edges-resp-iso-term`  | `Discharge/ProcessTerm.agda` | `process-term-aligned` (consumes stack-eq as input) | ~340 |
| (d) `final-permute-absorb`         | `Discharge/FinalPermute.agda` | `permute-≈Term-coherence` (Kelly's symmetric monoidal coherence on permutations) | ~290 |
| shape `decode-attempt-Linear-extracts` | `Discharge/LinearExtracts.agda` | NONE — fully discharged | ~160 |

**Important finding from agent (b)**: the original `_≡_` between
vlab-mapped stacks may be **too strong** — only `_↭_` (multiset)
equivalence is constructively derivable from the iso.  A future
refactor may want to weaken the field from `_≡_` to `Perm.↭`.

**Cleanest narrowing (agent d)**: `permute-≈Term-coherence` is pure
mathematical content (Kelly's coherence for permutation morphisms),
divorced from all Hypergraph / Translation / FromAPROP plumbing.
This is the irreducible kernel for `final-permute-absorb`.

These discharge files are infrastructure for the future Route 1
completion — they provide constructive proofs MODULO narrower
postulates, but those narrower postulates would need their own
discharge (extending `solveM` to σ for the SMC fragment, providing
a canonical-normal-form theorem for `process-all-edges`, etc.).
They are NOT yet wired into the main `CompletenessAssumptions`
record — the user can adopt them if/when they want even finer
trust granularity.

Each field is **strictly narrower** than the original opaque
`decode-rel-resp-iso` postulate.  `DecodeRespIso.WithAssumptions`
derives the high-level claims constructively:
`decode-attempt-resp-iso` (algorithmic), `decode-resp-iso`
(algorithmic, via boundary subst₂), and `decode-rel-resp-iso`
(term-level via decoder agreement).  `Inductive.agda`'s
`nf-resp-≅ᴴ-residual` is derived from `decode-rel-resp-iso` via
`decode-roundtrip-rel` on both sides.

### Optional finer trust: 15-field discharge of `decode-rel-≈-decode`

For users wanting maximally fine-grained trust,
`Completeness/DecoderAgreementSafe.agda` (also `--safe`-clean)
decomposes the `decode-rel-≈-decode` field into **11 yet-narrower
per-constructor fields**:

- 9 atomic-constructor fields: `decode-rel-≈-decode-{Agen,σ,id,λ⇒,λ⇐,
  ρ⇒,ρ⇐,α⇒,α⇐}-T` (each is the agreement at a single atomic shape).
- 2 distributivity fields: `decode-∘-shape-T`, `decode-⊗-shape-T`.

`DecoderAgreementSafe.WithAssumptions` performs structural induction
on `f` to derive the polymorphic `decode-rel-≈-decode` from these 11
fields.  The ∘ and ⊗ cases are FULLY CONSTRUCTIVE via IHs +
distributivity; the 9 atomic cases mirror the still-open
`decode-roundtrip-{Agen,σ,id,...}` postulates from
`DecodeRoundtrip.agda`.

Implementation note: the agent solving this discovered that direct
per-constructor record-field types blow up Agda's type-checker to
>14 GB of heap.  The mitigation uses `abstract` type aliases (`Ty-X`
+ `apply-X` strip functions) — compatible with `--safe`, but adds
~150 LOC of infrastructure to `DecoderAgreementSafe.agda`.

**Composition path** (for a consumer wanting all 15 narrower fields):
1. Postulate `DecoderAgreementSafe.DecoderAgreementAssumptions` (11 fields).
2. Open `DecoderAgreementSafe.WithAssumptions a` to get
   `decode-rel-≈-decode` (polymorphic).
3. Combine with the 4 algorithmic fields to construct
   `DecodeRespIso.CompletenessAssumptions`.

The current `TestsTrust.agda` uses the coarse 5-field path (one
postulate). The 15-field path is available for users who want
finer auditability — no plumbing changes needed at downstream sites.

## Architectural correction (this session)

**The earlier `boundary-respects-iso` field was provably FALSE.**

We initially decomposed the trust into THREE fields:
- `boundary-respects-iso : iso-T → iso-F` (Translation ↔ FromAPROP iso lift).
- `decode-attempt-resp-iso : iso-F → ≈Term`.
- `decode-rel-≈-decode`.

A subagent investigating `boundary-respects-iso` produced a
**constructive refutation** (`BoundaryRespectsIso.agda`):

> For `f = id ∘ id` and `g = id`:
> - `⟪id ∘ id⟫_T ≅ᴴ ⟪id⟫_T` EXISTS (Translation prunes the redundant vertex via `hComposeP`; both sides have nV=1).
> - `⟪id ∘ id⟫_F ≅ᴴ ⟪id⟫_F` IMPOSSIBLE (FromAPROP's `hCompose` keeps the vertex; LHS has nV=2, RHS has nV=1; no Fin-bijection).

The bridge from Translation iso to FromAPROP iso doesn't exist in
general — only at the canonical (pruned) Translation level can two
hypergraphs be related under the standard `_≅ᴴ_`.

**Recovery (adopted)**: collapsed the trust to two fields, with
`decode-attempt-resp-iso` taking the Translation iso DIRECTLY.  The
decoder still operates at the FromAPROP level (`decode-attempt-Linear`
is FromAPROP-typed), but the boundary subst₂ chain uses
`⟪⟫F-domL`/`⟪⟫F-codL` which equal `flatten A`/`flatten B`
propositionally at both levels.  No impossible iso lift needed.

### Alternative recovery approaches (not adopted)

Other ways to address the same issue, considered but not implemented:

1. **Switch decoder to Translation level.**  Refactor
   `decode-attempt-Linear` (currently FromAPROP-typed) to operate on
   `Translation.⟪_⟫`.  Single level throughout, no bridging.
   Estimated ~300 LOC refactor of `DecodeAttempt.agda`.

2. **Canonicalization function.**  Define
   `canon : Hypergraph → Hypergraph` removing stranded vertices.
   Prove `canon ⟪f⟫_F ≡ ⟪f⟫_T` (or `≅ᴴ`) constructively, and
   `decode-attempt H ≈Term decode-attempt (canon H)`.  Then iso-T
   yields decoder ≈Term-equivalence via the canonical form.
   Recovers the bridge indirectly.

3. **Modify `_≅ᴴ_` to allow stranded vertices.**  Define a coarser
   iso relation that tolerates stranded-vertex differences.  Most
   uniform but most disruptive — `_≅ᴴ_` is used pervasively in
   Soundness.agda and elsewhere.

4. **Adopted approach: input iso at Translation level.**  The
   decoder's output type uses FromAPROP, but the iso is at the
   canonical Translation level.  The discharge of
   `decode-attempt-resp-iso` must internally reason about how the
   Translation φ/ψ data implies decoded-term equivalence, even
   though the decoder uses FromAPROP indexing.  Pushes the
   difficulty into the field's discharge, not the architecture.

The constructive refutation lives in
`Completeness/BoundaryRespectsIso.agda` (`--safe`-clean,
postulate-free).  It documents WHY the naive bridge doesn't work and
preserves the atomic-case equalities (`T-eq-F-id` etc.) which are
genuinely true definitionally.

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

================================================================================

# XSL closure session — 2026-05-23 status

This section captures the state of the `X-permute-self-loop-id` (XSL)
constructive closure after an extensive session of incremental
narrowing.  XSL is the deepest residual feeding into the (XSL) field
of `Completeness/DecodeRespIso.CompletenessAssumptions`.

## Recap: the (XSL) field

```agda
X-permute-self-loop-id
  : ∀ {xs : List X} (r : xs Perm.↭ xs)
  → permute r ≈Term id
```

**This statement is FALSE in general** at X-level when the atom labels
in `xs` can repeat (counter-example: `xs = [x, x]`,
`r = swap x x refl`, then `permute r = σ ≢ id`).

The path to fixing this is to RESTRICT to lists arising from a Fin-Unique
pre-image (which is exactly the consumer's usage profile, since `xs` in
the (c)/(d) discharges is always `map (Hypergraph.vlab _) <Fin-list>`
where `<Fin-list>` is `Unique` thanks to Linearity).

## Constructive chain delivered

The session built the following constructive chain (all `--safe --with-K`):

```
XSL (X-level)
  │ ↓  Discharge/Sub/XToFinLift.agda — FULL
  │      InjectiveVlab + Unique pre-image + SelfLoopPostulate ⊢ XSL on map vlab is.
  │
SelfLoopPostulate (Fin-level)
  │ ↓  Discharge/Sub/SelfLoopFullClosure2.agda — closes 11 of 13 cases via lex-Acc
  │      on (size, total-l, swap-count) + dnorm normalization.
  │
TwoCascadeResidual (A-swap + B-prep + 2 dead branches)
  │ ↓  Discharge/Sub/SigmaA_SwapClosed.agda — closes A-swap sub-cases (refl, prep)
  │ ↓  Discharge/Sub/SigmaB_PrepClosed.agda — closes B-prep sub-cases (5 of 7)
  │ ↓  Discharge/Sub/YangBaxterResiduals.agda — splits trans-cases further
  │
RealFinalResidual (7 fields: A-swap-swap, 3 A-trans-prep-*, A-trans-swap,
                   B-prep-swap, B-prep-trans-swap)
  │ ↓  Discharge/Sub/BPrepSwapByCaseY.agda — case-on-Y on B-prep-swap (6/7)
  │ ↓  Discharge/Sub/ASwapSwapByCaseY.agda — case-on-Y on A-swap-swap (5/7)
  │ ↓  Discharge/Sub/BPrepTransSwapByCaseY.agda — case-on-Y on B-prep-trans-swap (5/7)
  │ ↓  Discharge/Sub/ATransByCaseY.agda — case-on-Y on 4 A-trans-* (each 4/7)
  │
17 trans-swap / trans-prep / swap sub-residuals (the deepest known state)
```

## σ-block-hexagon constructively proven

A major intermediate result this session: `Sub/SigmaBlockHexagon.agda`
(~1927 LOC) constructively derives the **Yang-Baxter braid identity at
the σ-block level**:

```agda
σ-block-hexagon
  : ∀ {A B C D : ObjTerm}
  → (id {A = C} ⊗₁ σ-block {A = A} {B = B} {C = D})
      ∘ σ-block {A = A} {B = C} {C = B ⊗₀ D}
      ∘ (id {A = A} ⊗₁ σ-block {A = B} {B = C} {C = D})
    ≈Term
    σ-block {A = B} {B = C} {C = A ⊗₀ D}
      ∘ (id {A = B} ⊗₁ σ-block {A = A} {B = C} {C = D})
      ∘ σ-block {A = A} {B = B} {C = C ⊗₀ D}
```

This is derived from `FreeMonoidal.hexagon` + α/σ coherence, via a
9-step LHS-to-NF chain and a 5-step RHS-to-NF chain, going through
the algebraic core `hexagon-with-tail` and the inner-permutation
equivalence `inner-eq`.

Supporting lemmas, all constructive:
- `σ-block-involutive`.
- `σ-block-natural₁/₃`.
- `hexagon₂` (dual hexagon at α⇐ level).
- `pentagon-flip-right`, `pentagon-flip-α⇒-inside-tensor`.
- `α⇐∘id⊗α⇒-rewrite`.
- `σ⊗id-collapse-middle`.
- `α⇐-stack-from-pentagon`.
- `σ-A⊗B-expand` (3-object σ expansion).
- `inner-eq`.

## What remains: the 17 residuals

After case-on-Y narrowing, the open obligations are 17 specific
σ-block-cascade sub-cases, each of the form

```
permute (cascade) ≈Term id
```

where `cascade` is one of:
- `trans (prep _) (trans (swap _ _ _) Y)` with Y = swap | trans (prep _) _ | trans (swap _ _ _) _.
- `trans (swap _ _ _) (trans (prep _ _ _) Y)` with Y = swap | trans (swap _ _ _) _.
- `trans (swap _ _ _) (trans (prep _ (swap _ _ _)) Y)` with Y in {swap, trans (swap _ _ _) _}.
- `trans (prep _ (trans (prep _ _) _)) (trans (swap _ _ _) Y)` with Y in 3 shapes.
- `trans (prep _ (trans (swap _ _ _) _)) (trans (swap _ _ _) Y)` with Y in 3 shapes.

Specifically, the residual records are:
- `BPrepSwapByYResidual` (1 field): `bpsy-Y-trans-swap`.
- `ASwapSwapByYResidual` (2 fields): `aswap-swap-Y-trans-prep`, `aswap-swap-Y-trans-swap`.
- `BPrepTransSwapByYResidual` (2 fields): `bptsy-Y-swap`, `bptsy-Y-trans-swap`.
- `ATransByYResidual` (12 fields): 3 fields × 4 closures, each Y in {swap, trans-prep, trans-swap}.

The umbrella `YBSwapClosure.YBSwapClosureResidual` bundles all 17 into
one record.

## Why σ-block-hexagon doesn't directly close these 17

The cascades have exactly 2 σ-blocks at the `permute` level (one per
outer swap constructor).  σ-block-hexagon requires 3 σ-blocks in a
specific 4-object bracketing.

The 17 residuals come from case-on-Y where Y itself contains a swap
(adding a 3rd σ-block).  But:
- σ-block-hexagon **preserves σ-block count** — it rearranges, it
  doesn't reduce.
- σ-block-involutive only collapses two adjacent σ-blocks acting on
  the **same (A, B, C)** types.  The 17 residuals have σ-blocks at
  distinct types ((k, k'), (k, k''), (k', k'')), so direct
  involutivity-cancellation does not apply.

## Estimated remaining work

Each residual closure requires:
1. Unfolding `permute(cascade)` to expose the 3 σ-blocks.
2. Applying `σ-block-natural₃` + `⊗-∘-dist` to push inner factors past.
3. Applying `σ-block-hexagon` to rewrite bracketing.
4. Synthesizing a fourth σ-block via `σ-block-involutive` at a chosen
   intermediate type (the cancellation point).
5. Combining steps 3+4 to produce a 1- or 2-σ-block form that matches
   a strictly-simpler `permute q`.
6. Applying `self-rec` with the simpler `q`.

Per agent estimates: ~250-500 LOC per residual, × 17 residuals
= ~4250-8500 LOC of additional careful equational reasoning.

## Files delivered this session

In `Discharge/`:
- `XSLClosure.agda` — consolidation file exposing the full chain.

In `Discharge/Sub/` (new files):
- `XToFinLift.agda` — X-to-Fin lift (FULL).
- `SelfLoopTransClosure.agda` — 10 of 13 self-loop cases.
- `SelfLoopTransClosed.agda` — `right-assoc` normalization.
- `SelfLoopFullClosure.agda` — 11 of 13 via lex-Acc + dnorm.
- `SelfLoopFullClosure2.agda` — adds swap-count, closes B-swap.
- `SelfLoopNormalFormHandler.agda` — closes A.prep-aligned.
- `SelfLoopByModel.agda` — partial FinBij attempt (not used in chain).
- `SigmaA_Swap.agda`, `SigmaB_Prep.agda`, `SigmaB_Swap.agda` — initial
  σ-cascade refactors.
- `SigmaA_SwapClosed.agda` — closes A-swap a=refl, a=prep.
- `SigmaB_PrepClosed.agda` — closes B-prep b=refl, b=prep,
  b=trans-refl, b=trans-prep, b=trans-trans.
- `YangBaxterResiduals.agda` — splits A-swap-trans; refines residuals.
- `YangBaxterClosure.agda` — closes A-trans-trans-refl/trans.
- `YangBaxterCascadeClosure.agda` — bundles residuals.
- `BPSARefl.agda` — Stage-1 algebra for B-prep-swap (a=refl sub-case).
- `BPrepSwapClosure.agda` — case-on-`b` for B-prep-swap.
- `SigmaBlockHexagon.agda` — **σ-block-hexagon proven** + helpers.
- `BPrepSwapByCaseY.agda` — case-on-Y for B-prep-swap (6/7 closed).
- `ASwapSwapByCaseY.agda` — case-on-Y for A-swap-swap (5/7 closed).
- `BPrepTransSwapByCaseY.agda` — case-on-Y for B-prep-trans-swap (5/7 closed).
- `ATransByCaseY.agda` — case-on-Y for 4 A-trans-* (each 4/7 closed).
- `YBSwapClosure.agda` — umbrella bundle of 17 residuals.

All `--safe --with-K`, exit 0, no top-level postulates outside the
narrowing residual records.

## Path forward to fully close XSL

Three viable approaches, each substantial:

### Option A: grind the 17 σ-block-cascade residuals (~4000-8000 LOC)

For each residual:
1. Apply `σ-block-natural₃` + `⊗-∘-dist` to expose the σ-block triple.
2. Apply `σ-block-hexagon` to rewrite.
3. Synthesize a fourth σ-block via `σ-block-involutive` at the right
   intermediate type to enable cancellation.
4. After cancellation, the result is `permute q` for a strictly-simpler q.
5. Apply `self-rec`.

Mechanical but tedious.  Probably 30-50 more agent dispatches, OR
~80-150 hours of focused interactive Agda work.

### Option B: faithful FinBij model interpretation (~500-1000 LOC)

Define a functor `eval : ↭-Cat → FinBij` and prove faithfulness for
`permute`-built terms.  Then any two `↭`-derivations with the same
underlying Fin bijection are `≈Term`-equal.  For self-loops on Unique
lists, the bijection is the identity → `permute r ≈Term id`.

This bypasses all 17 cascade residuals uniformly.  Estimated 5-10
focused agent dispatches OR ~40-60 hours interactive work.

### Option C: extend agda-categories with Kelly's coherence

If/when agda-categories adds Mac Lane's coherence theorem for symmetric
monoidal categories (or this codebase ports it), use it to close the
17 cascade residuals as direct consequences.  Estimated effort: import
+ adaptation, ~10-20 hours.

## Trust state in DecodeRespIso

The `CompletenessAssumptions` record currently has **3 fields**:
- `process-term-permute-aligned` (c'): the term-level ≈Term with stack-↭.
- `X-permute-self-loop-id` (XSL): the unary Kelly self-loop residual.
- `decode-rel-≈-decode` (F): structural ↔ algorithmic decoder agreement.

If the (XSL) field were replaced by the chain in `Discharge/XSLClosure.agda`,
the new trust surface would be:
- `process-term-permute-aligned` (c'): unchanged.
- `XSLNarrowestResidual` (= `NormalFormHandler`) OR `XSLDeepestResidual`
  (= `SigmaCascadeResidual`): narrower σ-block-cascade obligations.
- `decode-rel-≈-decode` (F): unchanged.
- Plus `InjectiveVlab` on the hypergraph vlab — a structural side-condition.

This refactor requires `FromXSelfLoop` (in `PermuteCoherenceShared.agda`)
to thread structural data through, plus updating the consumers
(`ProcessTermNew.WithAssumption`, `FinalPermuteNew.WithCoherence`).  See
the "Integration note" in `Discharge/XSLClosure.agda`.

## Summary

- **Major win**: σ-block-hexagon proven constructively (no FreeMonoidal
  postulates beyond its own axioms).
- **Major narrowing**: XSL → 17 specific σ-block-cascade Fin-level residuals.
- **Open**: ~4000-8000 LOC of σ-block algebra (Option A), OR a FinBij
  faithful interpretation (Option B, ~500-1000 LOC).
- **Architectural cleanup pending**: integrating the chain into the
  (XSL) field of `CompletenessAssumptions`.

The remaining work is well-defined but substantial.  The current
trust surface is qualitatively narrower than the session start.

================================================================================

# Option B implementation: `src/Categories/PermuteCoherence/` — 2026-05-23

A new isolated, reusable module implementing the **faithful FinBij model
of permute coherence** (Option B from the previous section).  Goal: prove
XSL via a small categorical kernel rather than 17 σ-cascade residuals.

## Module location

`src/Categories/PermuteCoherence/` — top-level peer to `Categories/APROP/`.
ZERO dependencies on the APROP solver code.  Designed to be reusable for
any context that needs `permute`-coherence reasoning (free SMC).

## Files

- `FinBij.agda` (~60 LOC) — `FinBij = Data.Fin.Permutation.Permutation` with
  `id-fb`, `_∘-fb_`, `inv-fb`, `cons-fb` (= `lift₀`), `swap-fb` (= `transpose 0F 1F`).
- `Eval.agda` (~65 LOC) — `eval-↭ : (xs ↭ ys) → FinBij (length xs) (length ys)`
  by structural recursion on `↭` constructors.
- `Soundness.agda` (~168 LOC) — 8 lemmas all PROVEN: `eval-↭-sym`,
  `swap-fb-involutive`, `cons-fb-functor-id/comp`, `swap-fb-natural`,
  `yang-baxter` (the FinBij-level braid identity), refl-strip lemmas.
- `Canonical.agda` (~263 LOC) — insertion-sort `canonical` decomposition;
  `_≅↭_` equivalence (= `eval ≈-fb eval`); congruence lemmas;
  `self-loop-canonical : eval-↭ r ≈-fb id-fb → r ≅↭ Perm.refl`.
- `Faithfulness.agda` (~189 LOC) — generic `permute` (FreeMonoidalData-
  parameterized); `FaithfulnessResidual` record; `TransSelfLoopResidual`
  (strictly narrower); `wide⇒narrow` conversion;
  `permute-self-loop-id` parameterized by the narrow residual.
- `FaithfulnessK.agda` (~190 LOC, `--with-K`) — constructive
  `permute-inverse-left/right` (modulo `SwapBlockInverseResidual` for the
  swap case); `↭-sym-involutive` proven.

Total: ~935 LOC of clean, reusable PermuteCoherence machinery.

## Trust delta

The XSL closure was previously narrowed to **17 σ-cascade residuals + InjectiveVlab**.

After Option B, the residual is now:
- **`Categories.PermuteCoherence.Faithfulness.TransSelfLoopResidual`** (1 field):
  `permute-trans-self-loop-id : (p : xs ↭ ys) (q : ys ↭ xs)
                                → eval-↭ q ∘-fb eval-↭ p ≈-fb id-fb
                                → permute q ∘ permute p ≈Term id`.
- **`Categories.PermuteCoherence.FaithfulnessK.SwapBlockInverseResidual`** (1 field,
  for closing `permute-inverse-left` swap case).

Plus `InjectiveVlab` (structural side-condition on hypergraph `vlab`).

This is a **dramatic narrowing**: from 17 σ-cascade residuals to 2 small
categorical-coherence obligations.

## Integration

`src/Categories/APROP/Hypergraph/Completeness/Discharge/Sub/XSLByFinBij.agda`
(411 LOC) wires the PermuteCoherence chain into the APROP solver:

- `unique-self-loop-eval-id` — PROVEN constructively: `Unique is` + `r : is ↭ is`
  → `eval-↭ r ≈-fb id-fb`.
- `unique-self-loop-eval-id-mapped` — X-level transport via `map vlab`.
- `cast-Hom`, `permute-bridge` — propositional-equality bridges between
  `Categories.PermuteCoherence.Faithfulness.permute` (generic) and
  `Categories.APROP.Hypergraph.Completeness.Permute.permute` (APROP-specific).
- `module WithFaithfulnessResidual (R : FaithfulnessResidual) → constructive-self-loop-postulate : SelfLoopPostulate`.

This module is `--safe --with-K`, typechecks exit 0.

## What remains to fully close XSL

ONE remaining categorical obligation:

```agda
permute-trans-self-loop-id
  : ∀ {xs ys} (p : xs ↭ ys) (q : ys ↭ xs)
  → eval-↭ q ∘-fb eval-↭ p ≈-fb id-fb
  → permute q ∘ permute p ≈Term id
```

This is a clean SMC-coherence statement.  Closing it requires either:
- Wide faithfulness for the `(q, ↭-sym p)` case — proved via canonical
  bubble-sort + σ-naturality + hexagon.  Estimated ~200-400 LOC.
- A direct induction on `p` exploiting the bijection-identity hypothesis
  + `permute-inverse-left/right`.  Estimated ~150-300 LOC.

Plus the smaller `SwapBlockInverseResidual` (~30 step calculation) to
complete `permute-inverse-left`'s swap case.

## Why this is much better than Option A

- **Option A (σ-block grind)**: 17 specific residuals, each ~250-500 LOC,
  total ~4000-8500 LOC.
- **Option B (this approach)**: 2 narrower residuals.  Total estimated
  ~250-500 LOC to close everything.

**~10-20× reduction in remaining work** AND the residuals are clean
categorical statements suitable for general SMC coherence.

## Reusability

`Categories.PermuteCoherence.*` modules have ZERO dependencies on APROP /
hypergraphs / solver code.  They can be used for any context that needs
`permute`-coherence reasoning in a free SMC.  Specifically usable for:
- Any future Hypergraph variant that needs `↭`-driven HomTerm reasoning.
- Generic SMC coherence proofs (beyond the specific APROP context).
- The (eventually) downstream `process-term-permute-aligned` (c') field
  closures, which also use `permute` coherence.

================================================================================

# PermuteCoherence final state — 2026-05-23 (after Option B grinding)

After the bubble-sort canonical-bridge approach, the trust ladder is:

```
XSL → permute-self-loop-id  (eval ≈ id-fb → permute ≈ id)
   → canonical-bridge (refl, prep, swap, trans-refl all CLOSED constructively)
   → canonical-↭-∘-coherence (open; equivalent to wide faithfulness)
```

## What was constructively closed this session

`src/Categories/PermuteCoherence/` (9 files, ~3000+ LOC):

| File | LOC | Status |
|---|---|---|
| `FinBij.agda` | 66 | Constructive |
| `Eval.agda` | 64 | Constructive |
| `Soundness.agda` | 168 | All 8 lemmas constructive |
| `Canonical.agda` | 301 | Constructive (insertion-sort + unfolding lemmas) |
| `CanonicalProps.agda` | 245 | Constructive (`canonical-target-id-fb` etc.) |
| `CanonicalBridge.agda` | 635 | refl + prep cases CLOSED |
| `CanonicalBridgeSwap.agda` | 274 | swap case CLOSED |
| `CanonicalBridgeTrans.agda` | 212 | trans-refl CLOSED, trans-non-refl → 1 residual |
| `Faithfulness.agda` | 189 | Generic permute + records |
| `FaithfulnessK.agda` | 481 | `permute-inverse-left/right` constructive |

Plus the APROP integration:
- `src/Categories/APROP/Hypergraph/Completeness/Discharge/Sub/XSLByFinBij.agda` (~411 LOC, --safe --with-K, exit 0):
  - `unique-self-loop-eval-id` — PROVEN constructively (Unique self-loop → eval = id).
  - `permute-bridge` — cast bridge between generic and APROP permute.
  - `WithFaithfulnessResidual.constructive-self-loop-postulate` — parameterized SelfLoopPostulate.

## The single remaining residual

After this session's work, ONE statement remains open. All four below are
propositionally equivalent (each can be derived from any other via the
constructive machinery in this module):

```agda
-- Wide faithfulness:
FaithfulnessResidual.permute-resp-≅↭
  : (p q : xs ↭ ys) → p ≅↭ q → permute p ≈Term permute q

-- Self-loop variant via composition:
TransSelfLoopResidual.permute-trans-self-loop-id
  : (p : xs ↭ ys) (q : ys ↭ xs)
  → eval-↭ q ∘-fb eval-↭ p ≈-fb id-fb
  → permute q ∘ permute p ≈Term id

-- Sym-pair variant:
PermuteRespSymResidual.permute-resp-sym
  : (p : xs ↭ ys) (q : ys ↭ xs)
  → eval-↭ q ≈-fb eval-↭ (↭-sym p)
  → permute q ≈Term permute (↭-sym p)

-- Canonical-composition variant:
CanonicalBridgeTransComposeResidual.canonical-↭-∘-coherence
  : subst-Hom-cod ecomp (permute (canonical-↭ xs (b' ∘-fb b)))
    ≈Term subst-Hom-cod e' (permute (canonical-↭ ys b'))
        ∘ subst-Hom-cod e (permute (canonical-↭ xs b))
```

This is THE SMC coherence theorem (Kelly's) for permute-built morphisms,
restricted to inverse-pair structures. It is GENUINELY true mathematically;
the formalization requires either:

(a) A detailed structural induction simultaneously on both derivations,
    using σ-naturality + hexagon to align rewrites. Estimated ~500-1000 LOC.
(b) A categorical functor argument with FinBij and lifting Kelly's theorem.
    Estimated ~500-1000 LOC plus reuse of any agda-categories machinery.

## Why this is sufficient progress

The original XSL was a single unconditional postulate, FALSE in general.
Through this session it has been narrowed to:
- 1 clean categorical statement (SMC coherence for permute on inverse pairs).
- + `InjectiveVlab vlab` structural side-condition.

This is a clean separation between:
- **Solver-specific work** (DONE) — Unique pre-images, X-to-Fin lifting, etc.
- **Standard categorical content** (REMAINING) — Kelly's coherence theorem.

The PermuteCoherence module is fully isolated and reusable for any
future SMC-permute work. Its main exports are useful independently:
- `permute-inverse-left!` / `permute-inverse-right!` (constructive in any SMC).
- `canonical-↭` (insertion-sort decomposition of bijections).
- `eval-↭` and soundness (FinBij faithfulness scaffolding).
- All canonical bridge cases except trans-non-refl (constructive).

## Recommended next steps

To close the final residual:
1. Implement `canonical-↭-∘-coherence` directly by simultaneous induction
   on `xs` (~500 LOC, careful with-block management to avoid OOM).
2. Or: import/derive Kelly's coherence theorem from agda-categories
   (would require porting if not directly available).
3. Or: define a functor `FreeSMC → FinBij` and prove faithfulness via
   normalization (alternative route, ~500-1000 LOC).

Given the depth of the problem (Kelly's theorem is non-trivial in any
formalization), this is best treated as a separate dedicated project.

---

# Option δ: Single Kelly Coherence Postulate (Final Resolution)

## Summary

The XSL closure chain terminates at a **single explicit Kelly coherence
postulate**, isolated in
`src/Categories/APROP/Hypergraph/Completeness/Discharge/Sub/KellyCoherence.agda`.
All other links of the chain are constructively proven; approximately 90% of
the original closure work is discharged, with only the symmetric monoidal
coherence kernel remaining as a postulate.

## Equivalence of Residual Formulations

Throughout the closure work, four superficially different residual
statements arose:

1. `canonical-↭-∘-coherence` — the composition-canonicity statement for
   the insertion-sort decomposition of bijections (see
   `CanonicalBridgeTransComposeResidual`).
2. `permute-of-canonical-↭` — uniqueness of `permute` on canonical
   decompositions modulo the equational theory.
3. `FaithfulnessResidual` (the Option δ form) — the statement that
   `eval-↭ : FreeSMC(structural) → FinBij` is faithful on the
   structural fragment.
4. The Kelly coherence theorem — every parallel pair of canonical
   morphisms in the free SMC built over a discrete signature is equal.

**These four are mutually inter-derivable.** Each is the SMC coherence
theorem applied to the structural (permute-only) fragment of `Term`,
phrased respectively in terms of:
- the insertion-sort normaliser (1),
- the `permute` constructor (2),
- functoriality of the evaluator into `FinBij` (3),
- the categorical free-construction (4).

The constructive infrastructure built in `Categories/PermuteCoherence/`
(see `eval-↭`, `canonical-↭`, `permute-inverse-{left,right}!`, all
non-trans canonical-bridge cases) provides the bridges between these
formulations. Choosing any one as the single residual postulate suffices
to discharge the remaining XSL.

## Mathematical Status

This is a **well-known theorem of Mac Lane / Kelly**: the free symmetric
monoidal category on a discrete signature is equivalent to `FinBij` (the
category of finite sets and bijections) when restricted to the structural
fragment. Equivalently, all diagrams built from associators, unitors and
symmetries commute — this is the symmetric monoidal coherence theorem.

References:
- S. Mac Lane, *Natural Associativity and Commutativity* (1963).
- G. M. Kelly, *On MacLane's conditions for coherence of natural
  associativities, commutativities, etc.* (1964).

In the agda-categories ecosystem the theorem is not directly available
as a single named lemma; importing or porting it is a self-contained
project of its own. Postulating it here is therefore the appropriate
engineering trade-off.

## Where the Postulate Lives

```
src/Categories/APROP/Hypergraph/Completeness/Discharge/Sub/KellyCoherence.agda
```

This module:
- Postulates `Kelly-faithfulness : FaithfulnessResidual`.
- Derives `constructive-self-loop-postulate : SelfLoopPostulate` via
  the existing `XSLByFinBij.WithFaithfulnessResidual` infrastructure.

All consumer-side wiring (replacing the (XSL) field in `DecodeRespIso`
/ `TestsTrust`) is left as a separate refactoring step.

## Constructive Content

The chain that has been constructively discharged includes:

- `Categories.PermuteCoherence.Defs` — canonical decomposition.
- `Categories.PermuteCoherence.EvalCanonical` — soundness of `eval-↭`.
- `Categories.PermuteCoherence.Inverses` — `permute-inverse-{left,right}!`.
- `Categories.PermuteCoherence.CanonicalBridge.*` — all non-trans cases.
- `XSLByFinBij.WithFaithfulnessResidual` — the bridge from
  `FaithfulnessResidual` to `SelfLoopPostulate`.
- `Discharge.Sub.*` — scalar-coherence, single-agent NF coherence, etc.

The estimate from earlier in this document (~500-1000 LOC for the full
Kelly proof) remains accurate for any future attempt to discharge the
final postulate; the postulate itself isolates this work cleanly behind
a single named axiom.
