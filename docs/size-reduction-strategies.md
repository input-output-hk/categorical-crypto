# Strategies for shrinking the APROP soundness development

The `src/Categories/APROP/Hypergraph` subtree is **36,748 LOC across 89 files**. This
note catalogues the levers for cutting it substantially, ranked by payoff, and
separates *accidental* complexity (bookkeeping the informal proof never does) from
*essential* complexity (the mathematical content, which the informal proof also pays
for). It closes with two more radical options that reach further but **change what is
proved**.

The yardstick is the informal proof (`docs/soundness-proof.typ`), which classifies every
step into three ingredients:

| Ingredient | What it is | Status |
|---|---|---|
| **K** | braiding / permutation coherence (Kelly); the `permute`/`eval`/FinBij word problem | the one *deep* ingredient; "out of scope", bottoms out in the symmetric-group word problem |
| **M** | non-symmetric monoidal coherence: α/λ/ρ + bifunctoriality + naturality of the coherence isos, possibly *around opaque box generators* | "the bulk of the formalization", "chased per positional case — no canonical-form solver in the symmetric fragment" |
| **S** | finite combinatorics: linearity/monogamy, connectivity, linear extensions, count bookkeeping | light on paper |

The headline finding: **M is accidental and largely automatable; K and S are mostly
essential.** Almost all the size lives in M and its transport tax.

---

## Where the bulk is

```
Soundness/Discharge/Sub      18,549   (half the tree)
Soundness/Discharge           7,024
Soundness                     5,084
.  (top-level)                5,172
Solver                          919
```

Largest single files: `DecodeTensorShape` 4451, `BoxKernel` 1650, `BlockNFNf2` 1337,
`Linearity` 1158, `DecodeAgenSigmaShape` 1086, `BlockNFBraid` 1036, `DecodeAttempt` 1026,
`SigmaBlockHexagon` 975, `CompletenessProved` 888.

The dominant *cost category* is the **transport tax**: tree-wide ~2,134 `subst`, ~2,143
`sym`, ~1,505 `trans`, ~1,740 `cong` lines; in `DecodeTensorShape` alone 1,134 of 4,451
lines (25%) are transport. Most of it exists only because `++`/`unflatten` reassociation
is not definitional — i.e. it is pure M-plumbing.

---

## Lever 1 — a monoidal coherence solver *with morphism generators* (biggest lever)

**Estimate: ~5,000–6,500 LOC absorbable; ~3,000–4,500 net eliminated (~8–12% of the tree).**
Confidence: medium.

### The gap

- `Categories.MonoidalCoherence.Solver.solveM` decides equality of *parallel structural
  morphisms* in the free monoidal category on a signature with **`mor = ⊥`** — only
  `id, ∘, ⊗₁, α, λ, ρ`, **no opaque boxes**. Used in 5 files / ~26 sites, **0× in
  `DecodeTensorShape`** — because every M-goal there reassociates coercions *around*
  opaque `Agen g ⊗ id` boxes, which `solveM` structurally rejects.
- `Categories.Tactic.Category` handles opaque morphisms but only for `∘`/`id` — no `⊗`.

The missing tool is the **union**: decide equality of morphism expressions in the free
**non-symmetric** monoidal category on a full polygraph — `id/∘/⊗₁/α/λ/ρ` *plus* opaque
box atoms `g : A→B`. This is exactly the **M** ingredient the doc names as the bulk.

### Feasibility boundary (load-bearing)

It must stay **non-symmetric**. Morphism equality in the free non-symmetric monoidal
category is decidable by MacLane strictification extended to morphisms — non-circular.
But equality in the free *symmetric* monoidal category = string-diagram equality =
hypergraph faithfulness = **the soundness theorem itself**. So the solver owns **M**;
**K** (braiding) stays in its separate kernel. (A safe sweetener: include σ as an opaque
iso *with naturality only* — moving a box past a fixed σ, no hexagon/symmetry axiom — is
non-circular and absorbs more of the σ-conjugation *framing* on the K-side.)

### Where the absorbable mass is (measured)

| File | LOC | M-absorbable | Note |
|---|---|---|---|
| `Sub/DecodeTensorShape` | 4451 | ~1960 (44%) | G-side box-suffix/prefix framing + its `++`-assoc/`unflatten` transport. The other ~35% (Sin/Sout/box-braid/kfac) is σ-conjugation = **K**, untouchable |
| `Sub/BoxKernel` | 1650 | ~930 (56%) | BlockTensor/BoxAssoc/BlockBoxSuffix framing; ~35% box-braid = K |
| `Discharge/BridgeAlphaFormCompound` | 797 | ~735 (92%) | the α-case — *already calls `solveM` for helpers but can't finish* the box-framed goal |
| `Discharge/CIsoAssocFromCons` | 375 | ~340 (90%) | pure α-pentagon chase over `unflatten-++-≅` |
| `Sub/BlockNFNf2` | 1337 | ~645 (48%) | fire-mid/box-suffix framing; rest σ-band + locating |
| `Sub/DecodeComposeShape` | 677 | ~150 (22%) | mostly S + K; the doc overstates M here |
| SwapValidity / SwapStep / IsoTransport / StackEquivariance | ~2580 | ~190 | substs carry *real* content (label/order agreement), **not** absorbable |

~4,940 of ~11,870 LOC (~42%) in the M-heavy files; ~5,000–6,500 tree-wide.

### What it does *not* touch, and the gross-vs-net gap

- Does **not** touch K (σ-block family ~3,969; part-(II) reshuffle) or S (`Linearity`
  1158; connectivity; `Invariant` 544).
- Absorbable ≠ deleted: residual scaffolding (inductions, well-founded recursion) stays,
  and goals must be **reflected into solver syntax** — the main build risk. The α-case is
  already close; `DecodeTensorShape` needs a reflection layer for `permute`/`unflatten`/box
  terms.
- The solver itself (~500–1,500 LOC of reusable infra) belongs in `Categories/Tactic` and
  does **not** count against the APROP subtree.

The two micro-tactics in `docs/proposed-tactics.md` (the `subst₂`/list-append *framing
solver* and the `⊗`-regroup combinators) are the incremental, hand-rollable seeds of this
solver — worth doing first as a proving ground even if the full solver is never built.

### Validation findings (2026-06-07)

- **The infrastructure is already started.** `src/Categories/FreeStrictMonoidal.agda` (262 LOC,
  `--safe` disabled, 4 postulates, imported nowhere) already defines the right normal form
  `HomTermⁿ` — a list of `(offset, box)` pairs, i.e. the **planar non-symmetric string-diagram
  normal form** — plus an interchange rewrite `_→ʳ_`/`_→ʳ*_`. The open hard part is its
  **confluence/normalization + `≈Term`-soundness/completeness** (and discharging the 4
  prefix-arithmetic postulates). That completeness proof is the genuine, unbuilt cost — so the
  "medium" confidence is right, leaning slightly optimistic on solver-construction effort.
- **Why `solveM` structurally can't be reused as-is:** it normalizes via a functor into the
  *Discrete* category on `List X` (every morphism `refl`), which forces `mor = ⊥`. With opaque
  boxes the normal-form target must be the free *strict* monoidal category on the polygraph
  (non-trivial morphisms), which is exactly what `FreeStrictMonoidal.HomTermⁿ` is.
- **M-share is, if anything, *understated*.** The doc's table marked "box-braid = K,
  untouchable", but `BoxKernel.box-braid` and `DecodeTensorShape` contain **zero `hexagon`** (the
  deep-K axiom lives only in `SigmaBlockHexagon`/`BlockNFBraid`/`SigmaBlockCommRaw`); their
  box-braid uses only one-box σ-naturality (`σ∘[f⊗g]≈[g⊗f]∘σ`, `σ∘σ≈id`) + α-coherence —
  absorbable under the "σ-as-opaque-iso-with-naturality" sweetener. *Caveat:* `DecodeTensorShape`
  still has genuine K (it calls `permute-via-vlab-≈Term-coherence-K`/`FaithfulnessResidual`), so
  part of its non-M is real K, not absorbable.
- **Confirmed solver-amenable:** `BridgeAlphaFormCompound` is ~100% M (zero σ/permute);
  `solveM` is *already* called there for the two atom-free helpers, and the ~145 lines of
  remaining hand-chasing are exactly the opaque-coercion-atom goals an extended solver absorbs.

---

## Lever 2 — go *pruned-only*: delete the unpruned `hCompose` universe (biggest non-`Sub` lever)

**Estimate: ~900 LOC net, VALIDATED (~2.5%); a further ~914 gated behind Lever 3.** Confidence: high
for the validated part. Orthogonal to Lever 1.

> **Validated by spike (2026-06-07).** Wrote `DirectBridgeSpike.agda` (228 LOC) proving
> `decode-rel f ≈Term decodeP f` *directly* — `--safe`, EXIT 0, zero postulates — re-pointed the
> live consumer `DecodeRelRespIsoWired` at it (one-line import swap), and `SoundnessFullWired`
> rebuilt green. As a hard check, physically deleting `DecodeComposeShape` (677),
> `DecodeRelDecodeP` (309), and `DecodeShape` (81, an orphan the original analysis missed) kept
> `SoundnessFullWired --safe` green. All 9 atomic `decodeP X ≡ decode X` are `refl` (the central
> claim holds).
>
> **Split verdict:**
> - **Tier A — validated deletable now: ~1,137 gross − 228 spike = ~909 net.** The 3 orphaned
>   files above + the orphaned `Assemble`/`DecodePShapeResiduals` glue in `ProcessEdgesTermShape`.
>   Real, mechanical, a one-file replacement.
> - **Tier B — ~914 more (`decode-attempt-hCompose` 95 + `Linearity.Linear-hCompose` block ~654 +
>   `FromAPROP.hCompose` ~165) is BLOCKED for Lever 2 alone.** The unpruned `decode` survives
>   because `DTS.decode-⊗-shape-inner`, `DecodeAgenSigmaShape`, and `DecodeRoundtripAgenSigma`
>   consume `decode` over the *unpruned* translation at arbitrary sub-terms; since
>   `decode-attempt-Linear` must stay total, its `∘`-case keeps `decode-attempt-hCompose →
>   Linear-hCompose → FromAPROP.hCompose` alive. Deleting Tier B = migrating `decode`/`bridge`
>   off the unpruned translation, which is **Lever 3**, not Lever 2.
> - **Two corrections:** the `Linearity` block was **undercounted** (the earlier ~280–490 missed
>   the 217-line `hCompose-Linear-utils` + the `remap-core` block; true ~654). And `DecodeShape`
>   (81) is a third orphaned file not previously listed.
>
> So Lever 2 proper banks **~900 net**; the full ~1,800+ needs Lever 2 + Lever 3 together. Both
> "NOT deletable" claims (DTS reused by the pruned tensor; `Congruence.hCompose-resp` already
> gone) were re-confirmed.

Two cospan-composition operators differ **only** in the composite's vertex count
(`hCompose` nV = `G.nV + K.nV` vs `hComposeP` nV = `G.nV + count-non K.dom`, which drops the
glued/cut vertices; same edges, same Fin order). `hComposeP` is a **standalone** construction
(built directly from `Prune.remap`/`count-non`, *not* "`hCompose` then prune"), and the
pruned proof files (`LinearHComposeP`, `DecodeAttemptLinearP`, `DecodeComposePruned`,
`CongruenceP`) re-prove their lemmas directly — they reference the unpruned versions only in
comments ("Mirrors …"), never as load-bearing calls. So the two sides are siblings, not a
dependency chain.

### Why both currently exist (and why it is *not* fundamental)

Tracing `SoundnessFullWired.soundness-full-wired`:

- It takes `⟪f⟫ ≅ᴴ ⟪g⟫` with `⟪_⟫` = the **pruned** `Translation.⟪_⟫`. The whole live path is
  pruned.
- **Part (I)** (round-trip `f ≈ decode-rel f`, via `decode-roundtrip-rel`) is **pure
  structural recursion on the term** (`DecodeRel.agda`: `decode-rel (g∘f) = decode-rel g ∘
  decode-rel f`; shape lemmas are `refl`). It **never references any `⟪_⟫` or composition
  operator** — so it is trivial *regardless of pruning*. The feared "Part (I) becomes hard if
  we drop unpruned" cost is **zero**.
- The unpruned `hCompose`/`decode`/`DecodeComposeShape` survive **only** as the *middle hop* of
  the agreement bridge `DecodeRelDecodeP`, which is assembled as `decodeP → decode →
  decode-rel` (it calls `DCS.decode-∘-shape-inner` *and* `DCP.decodeP-∘-shape`, ~lines
  184/211). The unpruned chain is a **shared trust anchor reused from pre-existing proofs**,
  not a necessity.

### What deleting unpruned buys (and what stays)

Deletable: `Sub/DecodeComposeShape` (677), the `Linearity.Linear-hCompose` block (~280–490 of
1158), `DecodeAttempt.decode-attempt-hCompose` (~92), `FromAPROP.hCompose` + unpruned `⟪_⟫`
`∘`-case (~40), and the bridge's middle-hop glue (`ProcessEdgesTermShape.Assemble` +
`decodeP-≈-decode` recursion + unpruned residual wiring, ~150–250). Gross ≈ 1,250–1,550.
**Minus** ~150–300 LOC to re-target the decoder-agreement dispatcher straight at `decodeP`
(prove `decode-rel ≈ decodeP` directly, dropping the unpruned middle hop). **Net ≈
1,000–1,300.**

**Not deletable** (corrects the naive "2,737 mirror LOC" tally): `Sub/DecodeTensorShape`
(4451) is generic and **reused by the pruned tensor** (`DecodeTensorPruned`) — tensor is
never pruned, so it stays in full; and `Congruence.hCompose-resp-≅ᴴ` is **already gone**
(`Congruence.agda` now defines only `hTensor-resp-≅ᴴ`). No essential consumer of unpruned
`hCompose`/`⟪_⟫` exists outside the bridge (the Completeness/`Triangle` path is already
pruned-only; `IsoTransport` imports `FromAPROP` only for `FlatGen`/`range`).

**Verdict:** pruned-only is a **net win, mechanical not conceptual** — the only real work is
re-plumbing the `decode-rel ≈ decodeP` bridge to drop its unpruned middle hop. (An
alternative that keeps both behaviors — making `hCompose` generic over a vertex-count/remap
*policy* record and instantiating twice — saves a similar amount but is more design-work; go
pruned-only unless an unpruned consumer reappears.)

---

## Lever 3 — collapse the decode triple

**Estimate: ~100–300 LOC (<1%).** Confidence: low → very low. *(Revised down after validation — see below.)*

There are **three** decoders: the algorithmic `Maybe`-valued `decode-attempt`
(`Decode` 164 + `DecodeAttempt` 1026 + `DecodeProperties` 543 + `DecodeRoundtripSafe` 824), the
structural `decode-rel` (`DecodeRel.agda` 129 — *trivial*: shape lemmas are `refl`, round-trip
is `≈-Term-refl`; this is what the informal proof actually does), and the pruned `decodeP`. The
round-trip is proved three times and reconciled.

**Validation correction (2026-06-07):** the earlier framing was too optimistic and partly wrong.
(i) Iso-invariance runs on **`decodeOrd`** (the order-theoretic decoder), *not* `decodeP`;
`decodeP` is only the bridge `decodeP f ≡ decodeOrd ⟪f⟫ (range nE) (vrange f)`. (ii) `decode-rel`
is purely structural-on-the-term and has **no notion of edge order**, so it *cannot* drive
iso-invariance (which is fundamentally about reordering edges) — re-architecting onto it would
still need a `decode-rel ≈ decodeOrd` bridge carrying essentially today's content. (iii)
`extract-prefix` is **not** isolated recovery machinery: it is used in ~20 files
(`DecodeAttemptLinearP`, `StackUnique*`, `RunInterchangeEmptyTail`, `DecodeTensorShape`,
`SwapValidity`, …) and will not retire. The genuine dedup is only among the three round-trip
proofs (the structural one is already trivial) — realistically ~100–300 LOC, not 400–800.

---

## Smaller levers

- **`Linearity` count library** (~150–300 LOC, low): the `count v (map injL xs ++ map injR
  ys)` split pattern recurs ~4× (prod/cons × L/R); a reusable lemma would dedup it. Most of
  the 1158 LOC is the irreducible gap between "balance is obvious" and the formal
  `concat (tabulate …)` normalization.
- **Completeness hygiene** (<100 LOC, cosmetic): the `CompletenessProved` header still calls
  itself a "TEMPORARY POSTULATE STUB" but now has zero postulates and 888 LOC of real proof.

---

## Verified dead ends (do not retry)

- **σ-block family → K reroute: NO-GO (circular).** `SigmaBlockHexagon` (975) is an *input
  to* the K kernel (`FaithfulnessInductive` imports `σ-block-hexagon` for the `swap-braid`
  case); `SigmaBlockCommRaw`/`BlockNFBraid` state σ-vs-`permute` identities the kernel's
  `permute p ≈ permute q` (eval-equal) interface cannot accept. `DecodeAgenSigmaShape`
  already delegates its one braiding step. K-reroute saves ~0 LOC.
- **Object-only `solveM` inside `DecodeTensorShape`**: doesn't apply — 0 pentagon/unitor
  occurrences; the content is ∘-reassoc over *opaque* boxes + bifunctoriality (this is what
  Lever 1 fixes).
- **`⊗-∘-dist` at `≅ᴴ`** (decompose `f⊗g` as `(f⊗id)∘(id⊗g)`): mathematically false at the
  hypergraph-iso level (tensor = disjoint union adds no wires; composition adds wires).
  Tried and reverted (commit `425bf16`).

---

## Honest ceiling

Levers 1 + 2 + 3 + smaller ≈ **16–23% of the tree (~5,700–8,500 LOC)**. Lever 1 (in `Sub`)
and Lever 2 (outside `Sub`) are orthogonal and compose. **A 50% cut is not reachable by
taming accidental complexity alone**: once M collapses into a solver, what remains — the
braiding coherence (K) and the linearity/connectivity combinatorics (S) — is largely
essential, the same content the informal proof pays for in one-liners ("by K", "by
monogamy"). Reaching 50% requires one of the two options below, each of which **changes
what is proved**.

---

## Reaching further by changing what is proved

These two options target the *essential* residue. They are not refactors; each alters the
statement or the trust base of the development.

### Option A — a strict-monoidal stack representation (attacks M / the transport tax *at the source*)

**Root cause.** The decoder threads a *stack* (`List X` of wire labels) and produces terms
of type `unflatten(stack) → unflatten(stack')` in `FreeMonoidal`, the **non-strict** free
SMC on `ObjTerm`. But `unflatten(xs ++ ys)` is only *isomorphic* (not definitionally equal)
to `unflatten xs ⊗₀ unflatten ys` (the `unflatten-++-≅` coercion), and `++` reassociation
costs an associator. So every stack manipulation pays a `subst`/coercion — the entire
transport tax and the `BoxAssoc`/`box-suffix`/`box-prefix`/`unflatten-++-≅` machinery.

**The change.** Work over the free **strict** monoidal category on the signature: objects =
`List X` with `++` as tensor (definitionally associative and unital, `[]` = unit). Then
`unflatten` is the identity on objects, `unflatten(xs ++ ys) ≡ unflatten xs ⊗ unflatten ys`
holds by `refl`, `++-assoc` is `refl` at the object level, and the associator/unitor
coercions *vanish*. The transport tax becomes `refl`; `BoxAssoc` and friends largely
disappear — **gross elimination, with no residual reflection scaffolding** (unlike Lever 1,
which discharges the same coherence on demand and leaves the inductions).

**Why this is "changing what is proved".** Soundness is currently stated as `f ≈Term g` in
the *non-strict* `FreeMonoidal`. To bank the win you either (i) restate soundness over the
free strict SMC, or (ii) prove the strictification equivalence `FreeSMC ≃ FreeStrictSMC`
once and transport the result — paying the monoidal coherence **once, at the boundary**,
instead of per positional case across thousands of lines. This is exactly what MacLane
strictification is for.

**Relationship to Lever 1.** Option A and Lever 1 are two solutions to the *same* problem
(non-strict monoidal coherence). Strictification eliminates it by construction (coherence
never appears); the solver decides it on demand. Strictification potentially removes *more*
(the transport tax and its scaffolding both go), but costs a full re-statement plus the
strictification bridge, and it is the more invasive of the two. **They also share
infrastructure:** both want the strict normal form already drafted in
`src/Categories/FreeStrictMonoidal.agda` — so they are *not* independent build efforts, and the
same unbuilt confluence/completeness proof gates both.

**Validation note (2026-06-07).** The non-strictness is confirmed genuine and load-bearing:
`unflatten-++-≅` (`PermuteCoherence/Faithfulness.agda:80-85`) is a recursive chain of
`sym associator` (per cons) + `sym unitorˡ` (base) — definitively *not* `refl` — and every
`box-suffix`/`c-iso-assoc`/`subst₂ (cong unflatten …)` exists to conjugate boxes through it. So
the lever is real. But note the *current* `FreeStrictMonoidal.agda` draft only strictifies the
*objects* (`ObjTerm = List X`, `⊗₀ = ++`); it still keeps α/λ/ρ as honest `HomTerm`
constructors with `⊗₀-assoc = ++-assoc` propositional (TODO: "add strict equalities"), so an
object-level transport tax partially survives until that is finished.

**What it does *not* fix.** Strictification strictifies only the associator/unitor (the
**M** part). The **braiding (K)** is not strictified — the σ-block coherence survives intact.
So Option A and Lever 1 attack M; neither touches K.

**Risk.** Building the free strict SMC + the strictification equivalence in `--safe
--without-K` is itself substantial, and every downstream consumer of the soundness theorem
must accept the strict (or bridged) statement.

### Option B — accept more axioms (attacks K / S, which are otherwise essential)

LOC can also be cut by *postulating* hard lemmas rather than proving them — trading
verification guarantee for size. This is a spectrum:

- **Defensible (already the doc's stance).** Postulate the recognised-deep **K** kernel at
  its clean interface — `eval π ≡ eval π' → permute π ≈ permute π'`
  (`FaithfulnessResidual`). The doc *already* declares K "out of scope / treated elsewhere".
  K is currently a genuine **proof**: `Categories/PermuteCoherence/*` is **26 files / ~4,822
  LOC, zero postulates** (`faithfulness : FaithfulnessResidual` at `FaithfulnessInductive.agda:694`).
  Postulating the interface deletes that ~4,822 LOC — but it lives *outside* the
  APROP/Hypergraph subtree, so it shrinks the **project**, not the headline 36,748. *Inside* the
  subtree it additionally kills `SigmaBlockHexagon` (975, imported by the kernel for the
  `swap-braid` case) and likely `BlockNFBraid` (1036) + `SigmaBlockCommRaw` (872) that feed it —
  roughly **1,000–2,900 subtree LOC**, depending on how much σ-block algebra is reused elsewhere.
- **Aggressive.** Postulate the big composite shape lemmas — `decode-⊗-shape`
  (deletes `DecodeTensorShape`, 4451, ~12% in one stroke), `decode-∘-shape`, or the
  part-(II) per-swap commutation. This buys size fast, but the postulates are large,
  non-obvious theorems: you would be *asserting* the hard part rather than proving it. Only
  appropriate if those lemmas are independently trusted (proved on paper, or outside the
  intended trust boundary).

**The trade-off.** Each axiom removes its proof's LOC but weakens the guarantee by exactly
that lemma. The principled line is the doc's: postulate the one genuinely-deep,
separately-justified kernel (K); prove everything above it. Going further is a deliberate
trust/size trade, not a free win.

### Combined

Option A (strictification) can push the M/transport win well past Lever 1's ceiling;
Option B (axiomatising K, and optionally the shape lemmas) is the only way to remove the
essential K/S residue. Together they could approach 50% — but the resulting artefact proves
a *different* (strict, and/or more-postulated) theorem than the current one. Whether that is
acceptable depends entirely on what downstream trust the soundness theorem must carry.
