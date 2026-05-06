# Refactoring plan: completeness proof simplifications

This document records three independent simplifications discovered while
auditing `string-diagram-solver-completeness`.  Each was prototyped end-to-end
in this worktree and the prototypes type-check.  They stack: applying all
three eliminates ~1000-1500 LOC and 4-5 of the postulates currently blocking
the completeness theorem.

## Status

### Refactor B — IMPLEMENTED across the completeness pipeline + Solver + structural soundness (32 / 42 files pass)

32 of 42 files in `src/Categories/APROP/Hypergraph/` type-check with
the de-indexed Hypergraph.  This includes the entire completeness
pipeline, the Solver (Phase 4a — `findIso` decision procedure), and
the structural infrastructure underlying soundness (Core, FromAPROP,
Iso, IsoSimple, Translation, PrunedCompose, Invariant, Prune,
HomTermInvariant, CoherenceHelpers).

```
Hypergraph/Completeness.agda
Hypergraph/Core.agda
Hypergraph/Core2.agda                            (experiment)
Hypergraph/FromAPROP.agda
Hypergraph/FromAPROP2.agda                       (experiment)
Hypergraph/Invariant.agda
Hypergraph/Iso.agda                              (-44 LOC of subst₂ projection lemmas)
Hypergraph/IsoSimple.agda
Hypergraph/Prune.agda
Hypergraph/Completeness/CoherenceSolver.agda     (experiment)
Hypergraph/Completeness/Decode.agda              (subst₂ HomTerm boundary wrap eliminated)
Hypergraph/Completeness/DecodeAttempt.agda       (-66 LOC, decode-attempt-subst₂ machinery gone)
Hypergraph/Completeness/DecodeProperties.agda
Hypergraph/Completeness/DecodeRel.agda           (experiment)
Hypergraph/Completeness/DecodeRoundtrip.agda
Hypergraph/Completeness/Decoder.agda
Hypergraph/Completeness/Linearity.agda           (-19 LOC, Linear-subst₂ removed)
Hypergraph/Completeness/Permute.agda
Hypergraph/Completeness/Unflatten.agda
Hypergraph/Solver/PBij.agda
Hypergraph/Solver/Signature.agda
Hypergraph/Solver/Totals.agda
```

`subst₂ (Hypergraph FlatGen)` count in the completeness pipeline:
**101 → 0** (the only 2 remaining references are inside comments).

The 10 files still failing form the **soundness chain** — Pentagon,
Triangle, AlphaCommSound, SoundnessAxioms, SoundnessProved,
CoherenceReductions, SigmaNat, Soundness, Congruence, CongruenceP.
These prove statements of the form `⟪ LHS ⟫ ≅ᴴ ⟪ RHS ⟫` where the
LHS/RHS previously involved `subst₂ Hypergraph` from the indexed
translation; the proofs were structured around peeling those substs.

Now that the translation is de-indexed, the `subst₂ Hypergraph` is
gone — these proofs need to be reformulated, not just mechanically
migrated.  This is real proof work (a few hours per file, more
for Pentagon).  An attempt to migrate `SoundnessProved.agda` showed
that each `hCompose-hId-{R,L}-iso-generic` export and each
ρ⇐∘ρ⇒/α⇐∘α⇒ proof requires careful threading of the new runtime
`bdy-eq` argument; the boundary equation that was previously a
type-level subst now needs to be supplied at each `hComposeP` call
site, including with `cong unflatten` lifts.

### Refactor A (decode-rel) and Refactor C (solveM)

Prototyped in the experimental files
`src/Categories/APROP/Hypergraph/Completeness/{DecodeRel,CoherenceSolver}.agda`,
both type-check.  Not yet integrated into the main pipeline.

### `decode-{ρ⇒,ρ⇐,α⇒,α⇐}-shape` shape lemmas

Postulated in DecodeRoundtrip.agda.  In the de-indexed setting they
are propositional consequences of:

  * `cong-trans : cong f (trans p q) ≡ trans (cong f p) (cong f q)`,
  * `subst₂-trans-{cod,dom}`: `subst₂ P a (trans b c) x ≡ subst (P _) c (subst₂ P a b x)`,
  * `subst₂-refl-{dom,cod}-≡`: `subst₂ refl c y ≡ subst (P _) c y`.

A proof attempt is sketched in the file but Agda's implicit-argument
inference doesn't pick it up cleanly — explicit instantiations would
make it work but become verbose.  Left as follow-up.

## Scope

Files affected (current LOC):

```
Pentagon.agda                                        451
AlphaCommSound.agda                                  211
SoundnessAxioms.agda                                 198
CoherenceHelpers.agda                                146
CoherenceReductions.agda                              85
PrunedCompose.agda                                   274
SoundnessProved.agda                                1431
HomTermInvariant.agda                                  -
Triangle.agda                                        137
FromAPROP.agda                                       554
Translation.agda                                       -
Completeness/Linearity.agda                         1324
Completeness/DecodeAttempt.agda                     1276
Completeness/DecodeRoundtrip.agda                   1981
Completeness/DecodeProperties.agda                   649
Completeness/Decode.agda                             219
```

Total `subst₂ (Hypergraph FlatGen)` occurrences across these files: **101**.
Of these, **99 vanish** under refactor B (de-indexing).

## Refactor B — de-index `Hypergraph`

### Change

```agda
-- Before
record Hypergraph {X} (Gen : List X → List X → Set) (As Bs : List X) : Set where
  field
    nV : ℕ
    vlab : Fin nV → X
    nE : ℕ
    ein : Fin nE → List (Fin nV)
    eout : Fin nE → List (Fin nV)
    elab : (e : Fin nE) → Gen (map vlab (ein e)) (map vlab (eout e))
    dom : List (Fin nV)
    cod : List (Fin nV)
    dom-ok : map vlab dom ≡ As
    cod-ok : map vlab cod ≡ Bs

-- After
record Hypergraph {X} (Gen : List X → List X → Set) : Set where
  field
    nV : ℕ
    vlab : Fin nV → X
    nE : ℕ
    ein : Fin nE → List (Fin nV)
    eout : Fin nE → List (Fin nV)
    elab : (e : Fin nE) → Gen (map vlab (ein e)) (map vlab (eout e))
    dom : List (Fin nV)
    cod : List (Fin nV)

domL : Hypergraph Gen → List X
domL H = map (vlab H) (dom H)

codL : Hypergraph Gen → List X
codL H = map (vlab H) (cod H)
```

`dom-ok` / `cod-ok` are gone.  The boundary atom lists are *computed* from
the Fin data via `domL` / `codL`.

### Why this kills 99% of the `subst` plumbing

The type `Hypergraph Gen` no longer depends on `As Bs`, so
`subst₂ (Hypergraph Gen) eq₁ eq₂ H` reduces (definitionally, since the
indices the subst lives on don't appear in the type) to `H`.  Every
construction of the form `subst₂ (Hypergraph FlatGen) eq₁ eq₂ <expr>` —
all 99 of the eliminable occurrences — collapses.

Boundary equations don't disappear; they become *propositional facts about
`domL` / `codL`*, used at the API surface (e.g. when wrapping the algorithm's
output in the user-facing `HomTerm (unflatten (flatten A)) (unflatten (flatten B))`
type) rather than threaded through every algorithmic step.

### Concrete examples

#### `⟪ ρ⇒ {A} ⟫` translation

```agda
-- Before (FromAPROP.agda:540-541):
⟪ ρ⇒ {A} ⟫ = subst₂ (Hypergraph FlatGen)
              refl (++-identityʳ (flatten A)) (hId (A ⊗₀ unit))

-- After:
⟪ ρ⇒ {A} ⟫ = hId (A ⊗₀ unit)
```

The propositional fact `++-identityʳ (flatten A)` moves to a separate boundary
lemma `⟪⟫-codL-ρ⇒ A : codL ⟪ρ⇒ {A}⟫ ≡ flatten A` (one line).

#### `decode-attempt-Linear (ρ⇒ {A})`

```agda
-- Before (DecodeAttempt.agda:1242-1244):
decode-attempt-Linear (ρ⇒ {A}) =
  decode-attempt-subst₂ (hId (A ⊗₀ unit)) refl (++-identityʳ (flatten A))
    (decode-attempt-hId (A ⊗₀ unit))

-- After:
decode-attempt-Linear (ρ⇒ {A}) = decode-attempt-hId (A ⊗₀ unit)
```

The entire `decode-attempt-subst₂` machinery (the function plus its
private helpers `subst₂-Maybe-of-HomTerm-just`, `decode-attempt-resp-subst₂`,
and the projector `decode-attempt-subst₂-proj₁`) — about 50 LOC in
DecodeAttempt.agda — disappears.

#### `Linear-subst₂` and the ρ/α cases of `⟪⟫-Linear`

```agda
-- Before (Linearity.agda:990-1020):
Linear-subst₂ : ...                                  -- 5 lines
⟪⟫-Linear (ρ⇒ {A}) =
  Linear-subst₂ refl (++-identityʳ (flatten A))
    (hId (A ⊗₀ unit)) (Linear-hId (A ⊗₀ unit))      -- 3 lines × 4 cases
...

-- After:
⟪⟫-Linear (ρ⇒ {A}) = Linear-hId (A ⊗₀ unit)         -- 1 line × 4 cases
```

`Linear-subst₂` deleted, ρ/α cases shrink ~12 → 4 lines.  Net ~17 LOC saved in
Linearity.agda.

### Distribution of `subst₂ (Hypergraph FlatGen)` occurrences

| File                     | uses |
|--------------------------|-----:|
| Pentagon.agda            |   50 |
| AlphaCommSound.agda      |    9 |
| SoundnessAxioms.agda     |    9 |
| CoherenceHelpers.agda    |    7 |
| CoherenceReductions.agda |    4 |
| FromAPROP.agda           |    4 |
| SoundnessProved.agda     |    4 |
| Translation.agda         |    4 |
| PrunedCompose.agda       |    3 |
| Completeness/DecodeAttempt.agda |    2 |
| HomTermInvariant.agda, Triangle.agda, Linearity.agda | 1 each |

Pentagon.agda alone has 50; together with its surrounding `subst-trans` /
`subst₂-cong` shuffling helpers, it is by far the largest beneficiary of
this refactor.

### Net LOC saved by refactor B alone

Conservative: **300-500 LOC** across the codebase.

### Smart-constructor signature changes

`hCompose` and any other constructor that needs source/target boundary
agreement now takes a propositional argument instead of relying on shared
indices:

```agda
-- Before
hCompose : ∀ {As Bs Cs} → Hypergraph Gen As Bs → Hypergraph Gen Bs Cs
         → Hypergraph Gen As Cs

-- After
hCompose : (G K : Hypergraph Gen) → codL G ≡ domL K → Hypergraph Gen
```

For `⟪ g ∘ f ⟫ = hCompose ⟪ f ⟫ ⟪ g ⟫ <bdy-eq>`, the `<bdy-eq>` is built
from per-constructor boundary lemmas (mechanical induction on the term).

### Hypergraph isomorphism

`_≅ᴴ_` currently lives at `Hypergraph Gen As Bs → Hypergraph Gen As Bs → Set`.
After de-indexing it becomes `Hypergraph Gen → Hypergraph Gen → Set` plus
witnesses that `domL`/`codL` agree.  Equivalent expressivity, no change to
the iso bijection data.

## Refactor A — `decode-rel` (definitional shape lemmas)

### Change

Define `decode` directly by structural recursion on the term, mirroring the
output shape of each `decode-attempt-h*`:

```agda
decode-rel : ∀ {A B} (f : HomTerm A B)
           → HomTerm (unflatten (flatten A)) (unflatten (flatten B))
decode-rel (Agen g)         = proj₁ (decode-attempt-hGen g)
decode-rel (id {A})         = proj₁ (decode-attempt-hId A)
decode-rel (g ∘ f)          = decode-rel g ∘ decode-rel f          -- definitional!
decode-rel (f ⊗₁ g)         = c-to ∘ (decode-rel f ⊗₁ decode-rel g) ∘ c-from
                                                                    -- definitional!
decode-rel (λ⇒ {A})         = proj₁ (decode-attempt-hId A)
... etc.
```

### Payoff

```agda
decode-rel-∘-shape : decode-rel (g ∘ f) ≡ decode-rel g ∘ decode-rel f
decode-rel-∘-shape g f = refl                    -- ✓ verified

decode-rel-⊗-shape : decode-rel (f ⊗₁ g) ≡ c-to ∘ (decode-rel f ⊗₁ decode-rel g) ∘ c-from
decode-rel-⊗-shape f g = refl                    -- ✓ verified
```

Both are postulated (`decode-∘-shape`, `decode-⊗-shape`) in
DecodeRoundtrip.agda:222-232 — TODO.org calls them "the hardest unknowns".
Under `decode-rel` they are `refl`.

### `decode-roundtrip-{∘,⊗}` collapse

```agda
decode-roundtrip-∘ g f IH-g IH-f = begin
  decode-rel (g ∘ f)   ≡⟨⟩
  decode-rel g ∘ decode-rel f   ≈⟨ ∘-resp-≈ IH-g IH-f ⟩
  bridge g ∘ bridge f  ≈⟨ bridge-∘ g f ⟨
  bridge (g ∘ f)       ∎
```

The current chain in DecodeRoundtrip.agda:246-255 has to first invoke
`decode-∘-shape` (a postulate); under `decode-rel` that step is gone.

### Net LOC saved by refactor A

~150-180 LOC in DecodeRoundtrip.agda, **2 postulates eliminated**.

## Refactor C — `MonoidalCoherence.Solver.solveM` (drops `--without-K`)

### Change

The in-tree `Categories.MonoidalCoherence` provides:

- `CoherenceThm.all-Comm`: Mac Lane's theorem mechanised — any two parallel
  morphisms in a free monoidal category over generators-only-`⊥` are equal.
- `Solver.solveM`: lifts `all-Comm` to any target monoidal category via the
  free functor.

Currently blocked from use because `MonoidalCoherence.agda` is `--with-K`
(its `ι` functor pattern-matches on `Discrete` morphisms via `refl`).
Dropping `--without-K` from the completeness files unlocks it.

### Two passing solveM demos (CoherenceSolver.agda)

```agda
test-α-iso : α⇒ {Var a} {Var b} {Var c} ∘ α⇐ ≈Term id
test-α-iso = solveM (α⇒' ∘' α⇐') id'                 -- 1 line

test-pentagon-instance : <pentagon equation>
test-pentagon-instance = solveM <LHS> <RHS>          -- 5 lines
```

### What it discharges

- **`bridge-α⇒-form-⊗-⊗`** postulate (DecodeRoundtrip.agda:1429,
  "100-150 chain steps").
- **`c-iso-assoc-from-cons`** postulate (DecodeRoundtrip.agda:1196,
  "~30 chain steps").
- The constructive bridge-form proofs for the unit/Var base cases of α/ρ
  (~50 LOC each, currently chains).
- The Layer-1 `bridge-∘`, `bridge-⊗-decompose`, `bridge-⊗` chains.
- The `subst-cod-cons`, `subst-dom-cons`, `subst₂-refl-cod`,
  `subst₂-refl-dom` helpers (used only inside the bridge-form chains).

For *parametric* statements (universal `A B C`), `solveM` requires
structural induction on the parameters, but each leaf is a one-line
solver call instead of a 25-line equational chain.

### Net LOC saved by refactor C

~600-900 LOC in DecodeRoundtrip.agda, **both remaining α-coherence
postulates discharged**.

## Combined estimate

| Refactor | LOC saved | Postulates eliminated |
|----------|----------:|----------------------:|
| A: `decode-rel`               |   150-180 | 2 (∘-shape, ⊗-shape)        |
| B: De-indexed Hypergraph      |   300-500 | (subst plumbing extinct)    |
| C: `solveM` (drops `--without-K`) | 600-900 | 2-3 (α-coherence chain)     |
| **Combined**                  | **1000-1500** | **4-5**                  |

Out of ~19000 LOC total in the project.

## Recommended order

1. **De-index Hypergraph (refactor B)** — first, because it touches more
   files but each change is local.  Removes the `subst₂` plumbing the
   other two refactors otherwise inherit.
2. **`decode-rel` (refactor A)** — small, self-contained.  Discharges
   `decode-∘-shape` / `decode-⊗-shape` immediately.
3. **`solveM` (refactor C)** — last, because it requires dropping
   `--without-K`.  Discharges the residual α-coherence postulates.

The three are largely orthogonal.  After all three, the remaining
work toward completeness is genuinely combinatorial:
`decode-attempt-h{Tensor,Compose}` (already done) and `decode-resp-≅ᴴ`
(unaffected by these refactors).

## Prototypes in this worktree

- `src/Categories/APROP/Hypergraph/Core2.agda` — de-indexed Hypergraph type.
- `src/Categories/APROP/Hypergraph/FromAPROP2.agda` — de-indexed translation,
  ρ/α subst-free.
- `src/Categories/APROP/Hypergraph/Completeness/DecodeRel.agda` —
  definitional shape lemmas.
- `src/Categories/APROP/Hypergraph/Completeness/CoherenceSolver.agda` —
  `solveM` demonstration (drops `--without-K`).

All four type-check.
