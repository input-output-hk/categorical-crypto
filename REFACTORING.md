# Goal: complete the completeness theorem

`Categories.APROP.Hypergraph.CompletenessFull.completeness-full :
⟪ f ⟫ ≅ᴴ ⟪ g ⟫ → f ≈Term g` builds cleanly. What's left is a small set
of **narrow postulates** of two flavours: vertex/edge bookkeeping and
permutation-equality coherence.

## Postulate inventory

The completeness path now depends on **12 narrow postulates** across
6 files. Every original wide postulate has been narrowed; many were
replaced outright by constructive definitions backed by a narrower
postulate.

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

**Obstruction**: vertex coverage. The naive route to discharge
`φ-restricts-L/R` (case-split + ψ-restricts contradiction) is
*mutually recursive* with ψ-restricts. The natural fix —
"every vertex of ⟪f⟫ is in dom/cod/some edge" — is **mathematically
false** (counter-example: `id ∘ id` has stranded vertices from
`hCompose`'s remap). The remaining route is label-multiset counting
over the `Linear` invariant — substantial new infrastructure
(~300+ LOC).

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

### 4. SMC coherence on the structural fragment — `Discharge/AtomicCompound0E.agda`

`decode-rel-resp-≅ᴴ-atomic-compound-0E` is **gone**, replaced by
`Structural-coherence-≈Term` which is now a definition. Two narrow
postulates plus a constructive permutation extractor:

```agda
Structural-to-perm : Structural f → flatten A ↭ flatten B  -- CONSTRUCTIVE
  (id/λ → refl; ρ → ++-identityʳ; α → ++-assoc; σ → ++-comm;
   _∘_ → trans; _⊗₁_ → ++⁺)

perm-eq-from-iso
  : ⟪ f ⟫ ≅ᴴ ⟪ g ⟫ → Structural f → Structural g
  → Structural-to-perm sf ≡ Structural-to-perm sg

Structural-coherence-from-perm-eq
  : Structural f → Structural g
  → Structural-to-perm sf ≡ Structural-to-perm sg
  → f ≈Term g
```

The residual SMC coherence content is now stated against `_≡_` on
propositional permutations — a clearly-bounded decidable problem,
no Mac Lane solver extension needed.

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
| φ-restricts-L/R | Hard | needs label-multiset counting (no vertex-coverage) |
| ψ-restricts-{L,R}-deg | Hard | requires iso-canonicalization for ghost edges |
| middle-iso-perm | Medium | extract permutation from boundary preservation in hCompose |
| sub-iso-{f,g}-via-γ | Medium | vertex/edge bookkeeping over hCompose-impl |
| iso-decompose-{∘⊗,⊗∘}-primitive-perm | Medium | similar to middle-iso-perm |
| perm-eq-from-iso | Easy | 0-edge hypergraph IS its permutation |
| Structural-coherence-from-perm-eq | Medium | mac Lane-style coherence on `_↭_` |
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
