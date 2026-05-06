# Goal: complete the completeness theorem

The immediate objective is to discharge the single remaining postulate
blocking `Categories.APROP.Hypergraph.Completeness.completeness`:

```agda
decode-rel-resp-≅ᴴ
  : ∀ {A B} (f g : HomTerm A B)
  → ⟪ f ⟫ ≅ᴴ ⟪ g ⟫
  → decode-rel f ≈Term decode-rel g
```

(in `Completeness/DecodeRel.agda`).  See the roadmap below.

## Current state (after refactors A, B, C)

The completeness theorem now depends on **a single postulate** —
`decode-rel-resp-≅ᴴ` above.  All other postulates that were on the
critical path have been discharged.

### How we got here

| Path postulate count | After |
|---|---:|
| Original (indexed Hypergraph, algorithmic decode) | 9-10 (transitively) |
| After refactor B (de-index Hypergraph) | unchanged on this axis |
| After refactor A step 1 (decode-rel concrete) | 5 |
| After Agen/σ → bridge | 3 |
| After all atomic → bridge | **1** |

The simplification that collapsed 5→1 was: define `decode-rel f = bridge f`
for every atomic constructor (id, λ, ρ, α, σ, Agen).  Each per-atom
roundtrip lemma then becomes `≈-Term-refl`, severing the chain that had
previously routed through `DR.{ρ,α}-coherence` (which depended on the
postulated `bridge-α⇒-form-⊗-⊗` and `c-iso-assoc-from-cons`).  The
α-coherence postulates remain in `DecodeRoundtrip.agda` for the algorithmic
decode pipeline but are no longer reached from `Completeness.completeness`.

### Difficulty of the remaining postulate

`decode-rel-resp-≅ᴴ` is essentially the completeness theorem itself —
"two terms with isomorphic hypergraphs decode to ≈Term-equal terms."
Discharging it requires the genuine categorical content (this is
the heart of the symmetric-PROP completeness theorem).

The Solver/* directory provides a *decision procedure* `findIso` that
returns `_≅ᴴ_` records for every `_≈Term_` equation form (verified
empirically by `Solver/Tests.agda`), but it doesn't produce ≈Term proofs.
Bridging "iso found" → "≈Term derivation" is the mathematical content
that's still missing.

Realistic estimates for full discharge:
- **Modify Solver to extract ≈Term proofs alongside iso**: 2-4 weeks,
  ~600-1000 LOC of new proof-tracking code.
- **Direct induction on the iso's structure** (vertex/edge bijections):
  2-4 weeks, similar scale.
- **Normalization to a canonical iso-invariant form**: 2-3 weeks,
  needs new infrastructure.
- **Restricted-signature first, then extend**: 1-2 weeks for the
  restricted case (atomic-vs-atomic), then per-extension cost.

The recommended next step is the restricted-signature variant — see
the `Categories.APROP.Hypergraph.Completeness.DecodeRel.RespIso` work
in progress (atomic-only sub-cases of `decode-rel-resp-≅ᴴ`).

### Lessons from the restricted-variant prototype

`Completeness/DecodeRel/RespIso.agda` attempts the atomic-case proof
of `decode-rel-resp-≅ᴴ`.  Status of the 81 atomic-vs-atomic pairs:

- **Same-constructor trivial cases** (8 of 9): `≈-Term-refl`.  Both
  sides are syntactically identical because the ObjTerm parameters
  are forced by the type signature.  9th case is Agen, where the
  underlying `mor` value can differ.
- **Cross-pair Agen-vs-non-Agen impossibilities** (7 + symmetric):
  discharged via `Agen-nonAgen-absurd : G.nE ≡ 1 → K.nE ≡ 0 → G ≅ᴴ K
  → ⊥`, which extracts `Fin 0` from the iso's edge bijection.
  Mechanical pattern.
- **Agen-Agen (different generators)**: requires `flat-injective`,
  which needs UIP-on-ListX (available with `APROPSignatureDec` via
  Hedberg's theorem).  ~1-2 days to finish.
- **Genuinely non-trivial cross-pairs at unit-only types** (e.g.,
  `λ⇒ {unit}` vs `ρ⇒ {unit}` — both translate to `hEmpty`, both have
  type `HomTerm (unit ⊗ unit) unit`): require categorical coherence
  lemmas like Kelly's `coherence₃` (`λ⇒ {unit} ≈ ρ⇒ {unit}`).
  Each such pair is a 5-15 line proof using existing infrastructure.
  Estimated 5-10 such pairs in total.

**Atomic case completion estimate**: ~1 week (consistent with the
earlier estimate).

**The harder remaining work** is the inductive cases of
`decode-rel-resp-≅ᴴ`: when `f` or `g` is compound (∘ or ⊗), the iso's
structure must be DECOMPOSED to match sub-terms.  This requires
understanding how `hComposeP` and `hTensor` interact with iso —
specifically, how to extract sub-isos from a composite iso, and how
to thread α-coherence and σ-naturality to bridge syntactic
differences.  This is the genuine 2-3 weeks of categorical work.

### Concrete roadmap to discharge `decode-rel-resp-≅ᴴ`

Ordered by difficulty / leverage:

**Phase 1 — Atomic case (~1 week)**

1. *Mechanical extension of cross-pair impossibilities* (~half a day):
   complete the symmetric direction (X-vs-Agen for X ∈ {λ⇒, λ⇐, ρ⇒, ρ⇐,
   α⇒, α⇐}).  Each is a one-liner using `sym-≅ᴴ` + the existing
   `Agen-nonAgen-absurd` helper.
2. *Agen-Agen case under `APROPSignatureDec`* (~1-2 days): bring the
   proof under decidable equality, derive `flat-injective` via
   `Verify.UIP-ListX`, pattern-match `flat g₁ ≡ flat g₂` to extract
   `g₁ ≡ g₂`, then `cong Agen`.
3. *Genuine non-trivial cross-pairs at unit-only types* (~2-3 days):
   enumerate the 5-10 atomic-cross pairs whose iso is non-trivial (e.g.
   `λ⇒ {unit}` vs `ρ⇒ {unit}`, `id {A ⊗ A}` vs `σ {A}{A}` for unit-only
   `A`, etc.).  Each uses Kelly's coherence (`coherence₃` etc.) plus
   the existing `bridge-X-is-id` lemmas.
4. *Assemble the atomic-case dispatcher* (~half a day): wrap the
   per-pair lemmas into a single `decode-rel-resp-≅ᴴ-atomic` that
   pattern-matches on `f, g : HomTerm A B` ruled to be atomic, with
   absurd cases discharged automatically by Agda's coverage checker.

**Phase 2 — Inductive case (~2-3 weeks)**

5. *Iso decomposition lemmas* (~1 week): given `⟪g₁ ∘ f₁⟫ ≅ᴴ
   ⟪g₂ ∘ f₂⟫`, extract sub-isos `⟪f₁⟫ ≅ᴴ ⟪f₂'⟫` and `⟪g₁⟫ ≅ᴴ ⟪g₂'⟫`
   for some related `f₂', g₂'`.  Same for `⊗`.  This requires deep
   engagement with `hComposeP`'s pruning mechanics: a sub-iso between
   composites doesn't trivially restrict to sub-isos between
   components — it could permute compositions via assoc.
6. *Thread α/σ-naturality* (~1 week): once the sub-isos are extracted,
   the inductive hypothesis gives `decode-rel f₁ ≈ decode-rel f₂'` and
   similarly for g.  Combining with structural equalities (assoc, σ-nat,
   α-comm) gives `decode-rel (g₁ ∘ f₁) ≈ decode-rel (g₂ ∘ f₂)`.  This
   may transitively reach the still-postulated soundness lemmas
   (`hexagon`, `α-comm`, `pentagon`, etc.) — discharging those is
   the genuine remaining work.
7. *Final assembly and audit* (~few days): compose all the per-case
   lemmas, prove the full induction, verify all 44 files build.

**Total: ~3-4 weeks of focused expert work** to fully discharge
`decode-rel-resp-≅ᴴ` and complete the completeness theorem.

### Alternative paths

- **Modify `Solver/findIso` to extract ≈Term proofs**: rather than
  pattern-matching on the iso, modify the decision procedure to track
  ≈Term moves alongside the iso construction.  Each `pairUp`,
  `tryEdge`, and `verify` step gets a parallel ≈Term-emitting variant.
  Same time estimate but more localized to one module.
- **Build a normal-form decoder**: define `nf : Hypergraph → HomTerm`
  invariant under `≅ᴴ`.  The existing `decode-attempt-Linear` is a
  candidate (it walks the hypergraph in a deterministic Fin order).
  Then `decode-rel-resp-≅ᴴ` follows from `nf-resp-≅ᴴ` plus
  `decode-rel f ≈ nf ⟪f⟫`.  Same time estimate.

All three paths are roughly equivalent in effort.  The
restricted-variant approach is the most incremental and produces
visible progress.
