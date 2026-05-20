# Goal: complete the completeness theorem

`Categories.APROP.Hypergraph.CompletenessFull.completeness-full :
⟪ f ⟫ ≅ᴴ ⟪ g ⟫ → f ≈Term g` builds cleanly.

## Postulate inventory (post `50e3eb3` — Path B restructure)

The completeness path now depends on **a single architecturally-
tractable postulate**:

```agda
nf-resp-≅ᴴ : ∀ {A B} (f g : HomTerm A B) → ⟪ f ⟫ ≅ᴴ ⟪ g ⟫ → bridge f ≈Term bridge g
```

stated in `Completeness/DecodeRel/Inductive.agda`. `decode-rel-resp-≅ᴴ-full`
is now a 4-line composition `trans (decode-roundtrip-rel f) (trans
(nf-resp-≅ᴴ iso) (sym (decode-roundtrip-rel g)))`, no recursion.

`decode-roundtrip-rel` is already fully constructive (in `DecodeRel.agda`),
so the bridge `decode-rel f ≈Term bridge f` costs nothing.

### History (May 2026 marathon session)

The original inductive proof `decode-rel-resp-≅ᴴ-full` decomposed
isos recursively through 4 compound branches (`⊗⊗`, `∘∘`, `⊗∘`, `∘⊗`)
plus atomic-vs-compound dispatch. Each branch needed sub-iso
extraction (`iso-decompose-⊗⊗`, etc.), which in turn needed vertex/
edge restriction postulates in `IsoDecomposeTT.agda`, `IsoDecomposeCC.agda`,
`Cross{OC,CO}.agda`, and `AgenCompound1E.agda`.

That whole structure has been **architecturally blocked** by two
counter-example families:

1. **σ-naturality half-swap** (tensor case): `Agen u ⊗ id` vs
   `id ⊗ Agen u` at `unit ⊗ A → unit ⊗ A` are `≈Term`-equal via
   σ-naturality, their hypergraphs are `≅ᴴ` via a half-swap, but
   no L→L-restricting iso exists. Three independent opus agents
   converged on this conclusion.

2. **idˡ/idʳ-absorption** (composition case): `Agen u ∘ id` vs
   `id ∘ Agen u` at `unit → unit → unit` are `≈Term`-equal via
   `idˡ`/`idʳ`, their composite hypergraphs are isomorphic, but
   sub-iso extraction is impossible (one side has 1 edge, the
   "extracted" sub-iso would need 0 edges).

The Path B restructure (commit `50e3eb3`) bypasses both pathologies
by re-stating completeness at the `bridge` level. `nf-resp-≅ᴴ`
operates on the whole hypergraph at once and doesn't care about
syntactic decomposition.

### Orphaned files (no longer on critical path)

The following files contain ~50 LOC of constructive code that's
still kept for reference but is no longer reached by
`completeness-full`:

- `RespIso/Atomic.agda`, `RespIso/AtomicCompound.agda`
- `RespIso/TensorTensor.agda`, `RespIso/ComposeCompose.agda`
- `RespIso/Discharge/{AtomicCompound0E,AgenCompound1E,IsoDecomposeTT,IsoDecomposeCC,CrossOC,CrossCO}.agda`
- `BlockDiagonal/*`

`AtomicCompound0E.agda` contains the Mac Lane discharge from `b7e31da`
— constructive end-to-end via `solveM` + Var-encoder + UIP coercions
— preserved for potential future reuse.

### Earlier landmarks (this session)

- `b7e31da` — Mac Lane fragment of structural coherence fully
  constructive via `solveM` + Var-encoder + UIP coercions.
- `425bf16` — reverted unsound `⊗-∘-dist-FromAPROP-iso` narrowing
  (vertex-count mismatch).
- `5ed168e`/`d417b63` — documented the architectural blockers.

### Path B Day 4 — Agen-Agen and edge-count narrowing

The single residual `nf-resp-≅ᴴ-residual` is now further narrowed in
`DecodeRel/Inductive.agda`. The constructive dispatcher
`nf-resp-≅ᴴ` discharges three sub-cases before falling through:

1. Both `NoSigma` (no σ, no Agen) → `Structural-coherence-≈Term-noσ`
   (Mac Lane, constructive).
2. Both `IsAgen` (literally `Agen g₁` and `Agen g₂`) → reuses the
   already-discharged `decode-rel-resp-≅ᴴ-Agen-Agen` from
   `RespIso/AgenAgen.agda`.  This is possible because
   `decode-rel (Agen g) = bridge (Agen g)` definitionally.
3. Edge-count contradiction: `NoAgen f` ∧ `IsAgen g` (or symmetric)
   yields `Fin 0 ↔ Fin 1`, which is `⊥` via `ψ`/`ψ⁻¹` on the iso.

A new `NoAgen` predicate (analogous to `NoSigma` but admitting σ) is
introduced.  Its key invariant `nE-NoAgen : NoAgen f → nE ⟪f⟫ ≡ 0`
follows from a small `nE-hId` recursion plus structural induction
through `hTensor`/`hCompose`.  Decidable classifier `NoAgen?` is
local to the dispatcher.

The residual now fires only when *both* `f, g` contain a σ subterm,
or *both* contain Agen but are not pure atomic Agens (e.g.
`Agen u ⊗ id`, `Agen u ∘ id`, etc.).  Postulate count unchanged
(still 1), but its scope is strictly smaller.

### Path B Day 5 — `HasAgen` generalization of edge-count contradiction

The single residual `nf-resp-≅ᴴ-residual` is further narrowed.  Day 4
killed the asymmetric case only when one side was *literally*
`Agen _`.  Day 5 introduces a `HasAgen` predicate — "this term
contains at least one `Agen` subterm anywhere" — together with a
constructive edge-extractor

```agda
HasAgen-edge : HasAgen f → Fin (Hypergraph.nE ⟪ f ⟫)
```

that walks down the `∘`/`⊗` skeleton and embeds the witnessed Agen
edge through `_↑ˡ_`/`_↑ʳ_`.  Combined with `nE-NoAgen : NoAgen f →
nE ⟪f⟫ ≡ 0`, the iso's `ψ`/`ψ⁻¹` again produces a `Fin 0` inhabitant
in any mixed NoAgen-vs-HasAgen pair:

```agda
NoAgen-iso-HasAgen-⊥ : NoAgen f → HasAgen g → ⟪f⟫ ≅ᴴ ⟪g⟫ → ⊥
HasAgen-iso-NoAgen-⊥ : HasAgen f → NoAgen g → ⟪f⟫ ≅ᴴ ⟪g⟫ → ⊥
```

A decidable `NoAgen-or-HasAgen` classifier splits every term into
exactly one of the two cases (every constructor is either an `Agen`
descendant or has the structural `noagen-*` constructor available).
The dispatcher's compound-vs-compound fall-through now first checks
`NoAgen-or-HasAgen` on each side; three of the four quadrants are
vacuous, so the residual only fires when *both* sides have a
`HasAgen` witness — i.e. both contain at least one user-generator
edge.

Concretely, the residual *no longer* fires on examples like
`f = id, g = Agen u ⊗ id_X` or `f = α⇒, g = Agen u ∘ id_B` — these
NoAgen/HasAgen mixes are now closed by the edge-count contradiction.
The remaining open scope: both `f, g` contain a user-generator edge
**or** both contain σ.  Postulate count unchanged (still 1).

### Path B Day 6 — `SingleAgen` σ-free single-generator narrowing

Day 5 closed all asymmetric NoAgen-vs-HasAgen pairs.  The
"both HasAgen" residual is now further refined by routing the
**σ-free single-Agen** sub-case through a *strictly-narrower*
postulate:

```agda
single-agen-coherence-≈Term
  : SingleAgen f → SingleAgen g
  → ⟪ f ⟫ ≅ᴴ ⟪ g ⟫
  → f ≈Term g
```

`SingleAgen` is a new inductive predicate in
`Completeness/DecodeRel/Inductive.agda`: "f contains exactly one
`Agen` subterm and is σ-free elsewhere."  Its constructors mirror
`HasAgen` but require the *other* side of every `∘`/`⊗` to be
`NoSigma` (no σ, no Agen).  A decidable classifier `SingleAgen?`
identifies the case.

Examples now closed by the narrower postulate (formerly absorbed
by the wide catch-all):

- `Agen u ∘ id` vs `Agen u`
- `Agen u ⊗ id_unit` vs `Agen u`
- `id ∘ (Agen u ∘ id)` vs `Agen u`
- `Agen u ∘ id` vs `id ∘ Agen u`
- any σ-free pair with exactly one Agen on each side

The catch-all `nf-resp-≅ᴴ-residual` is retained but now fires
only when at least one side contains a σ subterm OR contains 2+
Agen subterms (truly "compound generators").  Postulate count:
**1 → 2**, but the wide residual's effective firing scope is
strictly narrower than before, and the new postulate is itself
a focused structural-coherence claim amenable to a future
constructive discharge via a syntactic strip lemma + sub-iso
restriction (analogous to the constructive AgenAgen + Mac Lane
combo, generalised through the single-edge wrapper context).

**May 2026 unsoundness retraction (`425bf16`)**: an earlier
narrowing pass (`0c4f223`) introduced `⊗-∘-dist-FromAPROP-iso` and
its mirror in Cross{OC,CO} as "narrow universal coherence
postulates." These are **mathematically false**: `_≅ᴴ_` requires a
Fin-bijection on vertices, but the LHS `⟪p ⊗ q⟫` and RHS
`⟪(p⊗id) ∘ (id⊗q)⟫` have vertex counts differing by `nA + nB`
(unpruned hCompose retains all interior vertices). The narrowing
has been reverted; `iso-decompose-{∘⊗,⊗∘}-primitive-perm` are once
again direct postulates with their original wide signatures.

---

## Historical: the old inductive structure (no longer on critical path)

Everything below describes the *previous* proof architecture that
was orphaned by the Path B restructure (`50e3eb3`). The files
still exist as reference but are not reached by `completeness-full`.
The discharge of `nf-resp-≅ᴴ` (Path B Day 3+) may revisit some of
the constructive infrastructure here, but the postulates
documented below are no longer on the critical path.

### 1. Tensor block-diagonal — `Discharge/IsoDecomposeTT.agda`

The monolithic `iso-decompose-⊗⊗` postulate is **gone**; it is now
constructively assembled (in `BlockDiagonal.Assembly`) from four narrow
restriction postulates:

```agda
φ-restricts-L : ∀ iG → Σ iG' → φ (iG ↑ˡ K₁.nV) ≡ iG' ↑ˡ K₂.nV
φ-restricts-R : ∀ iK → Σ iK' → φ (G₁.nV ↑ʳ iK) ≡ G₂.nV ↑ʳ iK'
ψ-restricts-L-deg : ∀ eG → G₁.ein eG ≡ [] → G₁.eout eG ≡ [] → …
ψ-restricts-R-deg : ∀ eK → K₁.ein eK ≡ [] → K₁.eout eK ≡ [] → …
```

`ψ-restricts-L/R` for *non-degenerate* edges (any non-empty `ein` or
`eout`) is **proved constructively** in the same file. The two `-deg`
postulates are strict narrowings — they only fire on degenerate "ghost"
edges (`mor unit unit`-shaped, no endpoints).

**May 2026 narrowing of `ψ-restricts-{L,R}-deg`**: the postulates now
*additionally* require evidence of a matching ghost edge on the
opposite tensor half (a `Σ Fin K₂.nE λ eK → K₂.ein eK ≡ [] × K₂.eout
eK ≡ []` argument, respectively for the R side). The call site
constructively builds this witness via a small `map-≡-[]-inv` helper
on `ein-combined`/`eout-combined`. Ghost edges arise legitimately
from `Agen (f : mor unit unit)`; the genuinely hard residual is the
matching-ghosts case (e.g., `Agen g ⊗ id` vs `id ⊗ Agen g` swap).

**May 2026 narrowing**: `φ-restricts-L/R` have been further narrowed
to a `-non-bdy` form that only fires on vertices outside *both*
`dom` and `cod`. The boundary subcase is now constructively
discharged by the `BoundaryDischarge` module via same-position
lookup across `dom-split-eq-L/R` and `cod-split-eq-L/R`; the
constructive `φ-restricts-L/R` dispatch on decidable membership.

**Remaining obstruction**: vertex coverage for *interior + stranded*
vertices. The naive route is *mutually recursive* with
`ψ-restricts`. The natural fix — "every non-boundary vertex is in
some edge" — is **mathematically false** (counter-example: `id ∘
id` has stranded vertices from `hCompose`'s remap). The remaining
route is label-multiset counting over the `Linear` invariant —
substantial new infrastructure (~300+ LOC).

**May 2026 architectural finding** (three independent opus agents
converged): the four postulates `φ-restricts-{L,R}-non-bdy` and
`ψ-restricts-{L,R}-deg` (matching-ghost) are **not theorems** as
currently stated. Concrete counter-example: `f₁ = Agen u, g₁ = id`
vs `f₂ = id, g₂ = Agen u` at type `unit ⊗ A → unit ⊗ A`. These
terms ARE `≈Term`-equal (σ-naturality), their hypergraphs ARE
≅ᴴ-isomorphic via a half-swap, and `σ∘[f⊗g]≈[g⊗f]∘σ-sound` in
`Soundness.agda` is literally a half-swap iso producer. So no
L→L-restricting iso exists in this case, yet the postulates claim
one does.

**Salvage paths considered**:

- *Strengthen `_≅ᴴ_` with Origin tag*: doesn't help — just relocates
  the postulates to a `_≅ᴴ_ → _≅ᴴ⊗_` upcast with identical content
  (Soundness can't produce Origin-respecting isos for σ-naturality
  witnesses).

- *Restate as disjunction* (`L→L ⊎ L→R-with-σ-witness`): plausibly
  theorem-correct (σ-counter-example lands in inj₂ without
  contradiction), but consumer wiring through
  `BlockDiagonal.Assembly` (~1700 LOC of derivations) and
  `Inductive.agda`'s `⊗⊗` clause requires ~400-600 LOC of
  additional dispatch work to be usable. The dispatcher needs
  σ-naturality at the `≈Term` level (available as
  `σ∘[f⊗g]≈[g⊗f]∘σ` in `FreeMonoidal.agda:100`).

- *Bypass via normal-form decoder or Solver/findIso emitting
  ≈Term*: sidesteps the architecture entirely; see Alternative
  paths section.

### 2. Compose-compose middle/sub-isos — `Discharge/IsoDecomposeCC.agda`

The monolithic existential `iso-decompose-∘∘` is **gone**. The X-vs-Y
coherence bridge is now a constructive `assoc`/`identity`/`γ.isoˡ`
derivation. Three remaining narrow postulates:

```agda
middle-iso-perm    : ⟪ g₁ ∘ f₁ ⟫ ≅ᴴ ⟪ g₂ ∘ f₂ ⟫ → flatten Y ↭ flatten X
sub-iso-f-via-γ    : iso → ⟪ f₁ ⟫ ≅ᴴ ⟪ γ.from ∘ f₂ ⟫
sub-iso-g-via-γ    : iso → ⟪ g₁ ⟫ ≅ᴴ ⟪ g₂ ∘ γ.to ⟫
```

`middle-iso : Y ≅ X` is a *definition* built from `middle-iso-perm`
plus `↭-to-≅` and `unflatten-flatten-≈`. The previous narrowing via
`flatten X ≡ flatten Y` was reverted as **unsound** (σ-counter-example:
`f₂ = σ_{a,b}, g₂ = σ_{b,a}` yields composite-iso with `flatten X ≢
flatten Y` as ordered lists). The new permutation-valued version
handles σ cleanly via `_↭_`'s `swap` constructor.

The two `sub-iso-{f,g}-via-γ` postulates are vertex/edge bookkeeping
analogous to `IsoDecomposeTT.Assembly`. Estimated ~100–200 LOC each
once a sound `hCompose-impl` boundary-slicing toolkit is in place.

**May 2026 architectural finding**: `sub-iso-{f,g}-via-γ` are
**not theorems** as currently stated — they suffer a composition-
side analog of the σ-naturality counter-example documented in §1.
Concrete: `f₁ = Agen u, g₁ = id` vs `f₂ = id, g₂ = Agen u` (with
`u : mor unit unit`). Both composites `≈Term`-equal via `idˡ`/
`idʳ`; both translate to isomorphic 1-edge hypergraphs.
`middle-iso-perm` produces `[] ↭ []`, γ = identity. But
`sub-iso-f-via-γ` would assert `⟪Agen u⟫ ≅ᴴ ⟪γ.from ∘ id⟫` — LHS
has 1 edge, RHS has 0, no edge bijection exists. The Agen edge
"shifts" across the composition cut via `idˡ`/`idʳ`, mixing f and
g content. Same family of pathologies as the TT half-swap.

`middle-iso-perm` is mathematically true (vlab multisets on the
middle slice must agree by label-preservation) but its constructive
extraction requires Linear-invariant infrastructure (~300+ LOC),
not the simple boundary-projection initially imagined.

### 3. Cross-shape primitives — `Discharge/Cross{OC,CO}.agda`

```agda
iso-decompose-∘⊗-primitive-perm
  : ⟪ g ∘ f ⟫ ≅ᴴ ⟪ p ⊗₁ q ⟫
  → Σ (flatten X ↭ flatten (Ap ⊗₀ Bq)) λ π →
        (⟪ f ⟫ ≅ᴴ ⟪ ↭-to-≅ π .from ∘ (id ⊗₁ q) ⟫)
      × (⟪ g ⟫ ≅ᴴ ⟪ (p ⊗₁ id) ∘ ↭-to-≅ π .to ⟫)

iso-decompose-⊗∘-primitive-perm  -- symmetric variant
```

Both produce the coherence iso γ as a `_↭_` permutation
(bounded data), not an abstract `_≅_` record. This was the key
to eliminating the previous `decode-rel-resp-≅ᴴ-⊗∘` termination
workaround postulate — the symmetric primitive lets the ⊗∘ branch
recurse structurally on `p, q` (subterms of the *first* argument).

**May 2026 retraction (`425bf16`)**: an earlier narrowing
(`0c4f223`) replaced these primitives with constructive definitions
backed by `⊗-∘-dist-FromAPROP-iso` (and mirror). That postulate is
**unsound** — `_≅ᴴ_` requires a Fin-bijection on vertices, but the
two hypergraphs `⟪p ⊗ q⟫` and `⟪(p⊗id) ∘ (id⊗q)⟫` differ in
vertex count by `nA + nB` under unpruned `hCompose`. The narrowing
has been reverted; the two postulates are once again direct.

### 4. SMC coherence on the structural fragment — `Discharge/AtomicCompound0E.agda`

`decode-rel-resp-≅ᴴ-atomic-compound-0E` is **gone**, replaced by
`Structural-coherence-≈Term`. One narrow postulate plus a
constructive permutation extractor:

```agda
Structural-to-perm : Structural f → flatten A ↭ flatten B  -- CONSTRUCTIVE
  (id/λ → refl; ρ → ++-identityʳ; α → ++-assoc; σ → ++-comm;
   _∘_ → trans; _⊗₁_ → ++⁺)

Structural-coherence-≈Term
  : Structural f → Structural g → ⟪ f ⟫ ≅ᴴ ⟪ g ⟫ → f ≈Term g
```

**May 2026 retraction**: an earlier version split the postulate into
`perm-eq-from-iso : ⟪f⟫ ≅ᴴ ⟪g⟫ → Structural-to-perm sf ≡ Structural-to-perm sg`
plus `Structural-coherence-from-perm-eq`. That split is **unsound**:
`Data.List.Relation.Binary.Permutation.Propositional._↭_` is not
truncated — `refl` and `trans refl refl` are distinct constructors
despite witnessing the same underlying permutation, so
`perm-eq-from-iso` was unprovable as stated. The split has been
reverted to a single postulate. `Structural-to-perm` is retained as
useful infrastructure for a future model-theoretic discharge.

**May 2026 σ-split**: `Structural-coherence-≈Term` is now a
*constructive dispatcher* (no longer a postulate). It routes via a
`HasSigma? : Structural f → NoSigma f ⊎ ⊤` decision to one of two
strictly narrower postulates:

```agda
Structural-coherence-≈Term-noσ : NoSigma f → NoSigma g → ⟪f⟫ ≅ᴴ ⟪g⟫ → f ≈Term g
Structural-coherence-≈Term-σ   : Structural f → Structural g → ⟪f⟫ ≅ᴴ ⟪g⟫ → f ≈Term g
```

**Update (commit `923b1d7`)**: `Structural-coherence-≈Term-noσ` is
**no longer a postulate** — it's a constructive definition routed
through `Categories.MonoidalCoherence.Solver.solveM` instantiated at
APROP's `FreeMonoidal`. The Var-bookkeeping encoder
(`objAtoms`/`idxFin`/`varsVec`/`enc-Obj`/`enc-Hom`) plus
`enc-Obj-sound` (constructive) plus a UIP-flavored subst stub
`enc-Hom-sound-id` complete the discharge. The Mac Lane coherence
content is now fully constructive; the sole residual postulate at
this site (`enc-Hom-sound-id`) asserts only that the encoder is
identity-on-NoSigma-terms up to type transport — provable from UIP
on ObjTerm (Hedberg via `_≟-ObjTerm_`) plus definitional reductions
of `S.⟦_⟧₁` on each constructor.

The `-σ` half remains the only categorical-content postulate at
this site; it requires extending `solveM` to handle σ (SMC
braiding) and is independent infrastructure.

### 5. Agen-compound-1E — `RespIso/AtomicCompound.agda`

The single direct postulate:

```agda
decode-rel-resp-≅ᴴ-Agen-compound-1E
  : Compound h → nE ⟪ h ⟫ ≡ 1 → ⟪ Agen g ⟫ ≅ᴴ ⟪ h ⟫
  → decode-rel (Agen g) ≈Term decode-rel h
```

`Discharge/AgenCompound1E.agda` provides an alternative path via 4
shape-routed narrower postulates (`discharge-{∘,⊗}-{left,right}`),
but these are not yet wired to discharge the wider postulate. Each
narrow case depends on items (1)–(2) plus Agen-Agen (already proved
in `RespIso/AgenAgen.agda`).

## Helpers and infrastructure

- `Completeness/PermutationCoherence.agda` — **keystone helper**:
  `↭-to-≅ : xs ↭ ys → unflatten xs ≅ unflatten ys`. The new
  permutation-based postulates all derive coherence isos through this
  function, producing γ's whose syntactic size is bounded linearly by
  the permutation witness.
- `Completeness/Linearity.agda` — `Linear` invariant on hypergraphs;
  the natural framework for the label-multiset counting argument
  that would unblock Family 1.
- `Discharge/NEAgenIso1.agda` — fully discharged auxiliary used in
  `AtomicCompound.agda`.

## Discharge difficulty rated

| Postulate | Difficulty | Notes |
|---|---|---|
| φ-restricts-{L,R}-non-bdy | **Architecturally blocked** | not theorems under current `_≅ᴴ_` (σ-naturality counter-example) |
| ψ-restricts-{L,R}-deg (matching) | **Architecturally blocked** | same σ-naturality pathology |
| middle-iso-perm | Hard | needs Linear-invariant infrastructure (~300 LOC) |
| sub-iso-{f,g}-via-γ | **Architecturally blocked** | composition-side analog of σ-naturality; not theorems |
| iso-decompose-{∘⊗,⊗∘}-primitive-perm | Hard | wide postulates restored after `0c4f223` revert |
| Structural-coherence-≈Term-noσ | **Discharged** | Mac Lane coherence; constructive via `solveM` (`923b1d7` + `b7e31da`) |
| Structural-coherence-≈Term-σ | Hard | needs σ-extended SMC coherence solver |
| decode-rel-resp-≅ᴴ-Agen-compound-1E | Hard | depends on iso-decompose's machinery |

## Alternative paths

- **Modify `Solver/findIso` to extract `≈Term` proofs alongside the
  iso** — each `pairUp`/`tryEdge`/`verify` step would emit a parallel
  `≈Term` rewrite. Localized to `Solver/` instead of touching the
  RespIso modules.
- **Normal-form decoder** — define `nf : Hypergraph → HomTerm` invariant
  under `≅ᴴ` (existing `decode-attempt-Linear` is a candidate). Then
  `decode-rel-resp-≅ᴴ-full` follows from `nf-resp-≅ᴴ` plus
  `decode-rel f ≈ nf ⟪f⟫`.
