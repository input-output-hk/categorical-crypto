# Goal: complete the completeness theorem

`Categories.APROP.Hypergraph.CompletenessFull.completeness-full :
⟪ f ⟫ ≅ᴴ ⟪ g ⟫ → f ≈Term g` builds cleanly. What's left is a small set
of **narrow postulates** of two flavours: vertex/edge bookkeeping and
permutation-equality coherence.

## Postulate inventory

The completeness path now depends on **12 narrow postulates** across
6 files. Every original wide postulate has been narrowed; many were
replaced outright by constructive definitions backed by a narrower
postulate. As of `b7e31da`, the entire Mac Lane fragment of
structural coherence (`Structural-coherence-≈Term-noσ` and its
encoder-soundness residual) is **fully constructive end-to-end**
via `solveM` + Var-encoder + UIP coercions.

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

**May 2026 narrowing**: both primitives are now *constructively
defined* from narrower universal coherence postulates. CrossOC
introduces a single `⊗-∘-dist-FromAPROP-iso : ⟪ p ⊗₁ q ⟫ ≅ᴴ
⟪ (p ⊗₁ id) ∘ (id ⊗₁ q) ⟫` (no iso input, no existential content),
then transports through it and invokes
`IsoDecomposeCC.middle-iso-perm` + `sub-iso-{f,g}-via-γ`. CrossCO
introduces a mirror coherence iso plus a small `⊗∘-decode-rel-bridge`.
Net: 2 wide existentials → 3 narrow universals; the existential /
permutation / sub-iso content is now derived. A FromAPROP-side
bridge `⟪f⟫_FromAPROP ≅ᴴ ⟪f⟫_Translation` was ruled out: pruning
strictly removes stranded K-side dom vertices, so universal
unpruned→pruned is mathematically impossible.

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
| φ-restricts-{L,R}-non-bdy | Hard | needs label-multiset counting (boundary case discharged) |
| ψ-restricts-{L,R}-deg (matching) | Hard | matching-ghosts case; needs label-multiset counting |
| middle-iso-perm | Medium | extract permutation from boundary preservation in hCompose |
| sub-iso-{f,g}-via-γ | Medium | vertex/edge bookkeeping over hCompose-impl |
| ⊗-∘-dist-FromAPROP-iso, mirror, ⊗∘-decode-rel-bridge | Medium | universal coherence isos for cross-shape primitives |
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
