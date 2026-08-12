# Strictification map for part (II) — the iso-invariance chain

> **Repointing note (2026-08-10).** `Discharge/DepIrrefl` no longer exists: it was
> dissolved into `Discharge/FinOrderNoInv`, where its statement is exported as
> `NoSelfDep` (types byte-identical).  Read every `DepIrrefl` below as
> `FinOrderNoInv.NoSelfDep`.

> **Repointing note (2026-08-12).** `permˢ-K` is no longer threaded as a module
> parameter anywhere below `Perm/PermSupport` (the type's definition site):
> `Perm/PermK` discharges it axiom-free for every vertex set and every generator
> family, and `SwapCore`, `PermCalc.Kit`, the decoder shape lemmas and the
> ⊗-shape all take `PK.permˢ-K` / `PK.perm-rigidˢ` directly.  Read the
> "module parameter" passages below as a record of the discharge plan, not of the
> live wiring.

Status: reconnaissance over commit `2d2c8e5` ("Strictification phase 0").
Companion deliverables `Strict/PermAlgebra.agda` and `Strict/SwapCore.agda` (§4) are
DESIGNED here but not yet written.

Classification key:

* **(1) TERM-FREE** — order/stack/count combinatorics over `List (Fin nV)` / `List (Fin nE)`
  / `_↭_`.  The strict decoder (`Strict/Decoder.edge-stepˢ`) uses the **same**
  `extract-prefix` as the non-strict one, so all stack functions agree
  (`proj₁ (edge-stepˢ s e) ≡ proj₁ (edge-step H s e)` is definitional per branch; a 6-line
  `pe-stack-agree` bridge transfers `process-edges`-indexed facts).  Reusable AS-IS.
* **(2) TERM-LEVEL** — `≈Term` proofs that must be re-proven as `≈ˢ` in
  `FreeStrictSMC.Build`.  The non-strict Mac-Lane mass (associator chases, `unflatten-++-≅`
  conjugation, `subst₂ HomTerm` transport) collapses to the UIP-trivial `castˢ` kit.
* **(3) OBSOLETE** — content that exists *only* to manage non-strict bookkeeping
  (`unflatten-++-≅` re-bracketing, `α`-block algebra, `subst₂` calculus).  No strict
  counterpart needed beyond the `castˢ` kit / `σ-hexˢ` axiom.

The part-(II) spine (from `DecodeRelRespIsoWired`):

```
iso : ⟪f⟫ ≅ᴴ ⟪g⟫
  → EdgeDependency (Lemma A) → LinExt connectivity            [term-free]
  → IsoInvarianceWiring.PerHG (Order/Valid/decodeOrd, τ)      [spine]
  → IsoInvarianceConcrete (↝*⇒≈, order-invariant)             [assembly]
      swap-≈      ← SwapStep ← RunInterchange{EmptyTail,Tail} ← FireMid* ← BlockNF*/Sigma*
      swap-valid  ← SwapValidity                              [term-free]
      iso-transport ← IsoTransport ← EdgeStepNaturality
      NoInv-τ     ← WiringLemmas                              [term-free]
  → DecodeOrdBoundary (boundary subst₂ + final-permute K)
  → DecodeRelRespIsoWired (decodeP-resp-iso, decode-rel-resp-iso)
```

---

## 1. Per-module verdicts

### Category (1): term-free — reuse as-is

| module | LOC | reusable exports | verdict |
|---|---|---|---|
| `EdgeDependency` | 91 | `Dep`, `≺⇒ψ≺`, `ψ≺⇒≺`, `lemmaA`, `∈-mapφ⁺/⁻` | **Reuse as-is.** Pure membership combinatorics; H-generic. |
| `Sub/CountCombinatorics` | 270 | `↭⇒count`, `count-pos→∈`, `count-≤→extract-prefix`, `extract-prefix-just→count-≤`, `++-cancelˡ`, `count-concat-tabulate(-pair)-≤`, `count-cons-*`, `count-zero-empty` | **Reuse as-is.** Already a declared shared leaf. `++-cancelˡ` is used by the strict SwapCore to align the two residual lists. |
| `Sub/FireMidInterchangeComb` | 539 | `ein-ein-disjoint`, `eout-ein-disjoint`, `e'-fires-stable`, `e'-skips-stable`, `ein'-≤-r₁`, `extract-ein'`, `block-loc-e`, `post-swap-stack-↭`, `SimLoc`, `sim-loc` | **Reuse as-is.** Pure `_↭_`/`count`; the strict SwapCore consumes `extract-ein'` (residual location `q₁ : r₁ ↭ ein e' ++ R`), the two stability lemmas (mixed-firing impossibility), and `++-cancelˡ`-style cancellation. Zero `HomTerm` references. |
| `Sub/StackUnique` | 300 | `Unique-resp-↭`, `count≤1⇒Unique`, `residual-recon-unique`, `residual-recon`, `coh-fin-rigid`, `++-Unique-from-counts` | **Reuse as-is.** All eval-coincidence reasoning is at the `FinBij`/`_≅↭_` level (`Categories.PermuteCoherence.{Eval,Rigid,Canonical}` are `Set`-generic), independent of the term category. |
| `Sub/StackUniqueReach` | 273 | `reservoir`, `Reservoir≤1`, `Reservoir≤1⇒Unique`, `reservoir-split`, `reservoir-prefix`, `reservoir-resp-↭`, `dom-reservoir-prov` | **Reuse as-is** modulo the `pe-stack-agree` bridge: only `reservoir-split` mentions `process-edges` (through `proj₁`), and the strict stacks are propositionally equal. Everything else is count arithmetic. |
| `SwapValidity` | 424 | `pe-stack-resp-↭`, `two-edge-swap-stack-↭`, `front-swap-stack-↭`, `swap-validity` | **Reuse as-is.** 0 `HomTerm` hits: `Valid o = proj₁ (process-edges …) ↭ cod` is a stack statement; the strict `Validˢ` is the same proposition (same stacks). |
| `WiringLemmas` | 77 | `NoInv-τ` (Lemma 4) | **Reuse as-is.** Order theory over `Dep` only. |
| `DepIrrefl` | 257 | `dep-irrefl-⟪⟫` | **Reuse as-is.** Structural induction over the *translation* (graph shape of `⟪f⟫`); its `HomTerm` mentions are only the induction motive `f`, not decoder terms. |
| `FinOrderNoInv` | 458 | `fin-order-NoInv-⟪⟫` | **Reuse as-is.** Same situation as `DepIrrefl`: `NoInv (range nE)` is `AllPairs (¬ Dep)`. |
| `Sub/PermutationTransport` (top half) | ~200 of 349 | `subst₂-↭-irr`, the `map⁺ f`-vs-combinator commutation lemmas, `↭`-constructor/`subst₂` algebra | **Partially reusable.** The generic `Set`-polymorphic `_↭_`/`subst₂` algebra survives wherever the strict port still moves permutations across propositional list equalities (it does: `permuteˢ-subst` consumes exactly this). The `map⁺ vlab` X-level *lift* lemmas lose their main consumer (see §3): the strict `permuteˢ` lives at the **vertex** level natively, so most `map⁺`-lift plumbing is no longer needed. |

### Category (2): term-level — must be ported to `≈ˢ`

| module | LOC | what it proves | strict port estimate / which mass vanishes |
|---|---|---|---|
| `IsoInvarianceWiring` | 164 | Spine: `PerHG.Order/Valid/decodeOrd`, cross-iso `τ`, `τ↭range`, `domL-iso/codL-iso`, `range≡tabulate` bridges. | **~150.** Everything except `decodeOrd` (3 lines) is term-free and reusable verbatim. Strict twin: `decodeOrdˢ o p = castˢ … (permuteˢ p) ∘ˢ proj₂ (process-edgesˢ o dom)` — one `map-++`-free cast (`map vlab cod = codL` is definitional). |
| `IsoInvarianceConcrete` | 162 | `↝*⇒≈` (Star induction over swaps), `order-invariant`, `decode-ord-resp-iso`. | **~160 (1:1).** Pure `≈Term`-transitivity plumbing; renames to `≈ˢ`. No Mac-Lane content to lose. |
| `SwapStep` | 453 | `process-edges-++-≈`, `decodeOrd-factor` (with `coe-cod` subst-threading), `FrontSwap.final-permute-coh` (K), `box-interchange` (N kernel), `RunInterchange` record, `front-swap-≈`, `swap-≈`. | **~250.** `coe-cod`/`coe-vanish` subst-naturality becomes `castˢ`+`pe-resp` (already prototyped in `Strict/Decoder`). `final-permute-coh` = `perm-rigidˢ` (`permˢ-K` + the generic `eval-rigid`), **3 lines vs ~45** — the `eval-map⁺`/`subst₂-FinBij-≈` X-level transport disappears because `permuteˢ` is vertex-level. `box-interchange` = `box-commute-ˢ` (already 4 lines in `FreeStrictSMC`). |
| `EdgeStepRelation` | 117 | `EdgeStepR` view + `box-of`/`fire-mid`/`fire-term`. | **~60.** Strict twin `EdgeStepRˢ` (done in `SwapCore`). The fired layer in S is `castˢ ((genˢ ⊗ˢ idˢ) ∘ˢ castˢ (permuteˢ p))` — `box-of`'s `unflatten-++-≅` conjugation and `box-of-cong`'s `subst₂` vanish. |
| `Sub/RunInterchangeEmptyTail` | 363 | Four-way firing split (`build`), reservoir→`Unique` sourcing, `run-interchange₀`. | **~300 (mostly 1:1).** The skeleton (case split, stability eliminations, `pin` just-injectivity) is term-independent; the per-case `≈` algebra is `idˡ/idʳ`. Ported in `SwapCore.agda` (this work). |
| `Sub/FireMidInterchange` | 477 | `BlockNF`/`BlockNFResidual` frames + assembly of `fire-mid-interchange` from `nf₁/nf₂/vin-coh/vout-coh` + `box-interchange`. | **~200 total in S** (and folded directly into `SwapCore.fire-mid-interchangeˢ`): the four-equation scaffolding is unnecessary because the located normal form is derived in one pass — see §4. The `unflatten-++-≅` view frames (`view-in≅`/`view-out≅`) have no strict counterpart (the "views" are `castˢ` of `map-++`/`++-assoc`). |
| `Sub/FireMidEquivariant` | 408 | FIRE-box naturality under a residual permutation; crux `permute-++⁺ˡ-slide` (associator-naturality list induction) + iso-pair cancellation + K self-loop. | **~40 in S** (`PermAlgebra.permuteˢ-frameˡ` + one `interchangeˢ`): the slide-through-`unflatten-++-≅` induction, the `from∘to` cancellations and the K-based `permute-inv-right` all vanish; in S `permuteˢ (++⁺ˡ ks ℓ) ≈ˢ idˢ ⊗ˢ permuteˢ ℓ` is a direct induction (prep clauses are definitional) and box naturality is one `interchangeˢ`. **This is the largest single collapse in the chain (10×).** |
| `Sub/StackEquivariance` | 534 | `process-edges-equivariant`: run on a permuted stack = run sandwiched between boundary permutes. Parts: `pvv-trans/inverse-{left,right}`, `fire-stable-{just,nothing}` (term-free), `residual-recon` (≅↭, term-free), `map⁺-lift-≅↭`, `edge-step(-fire)-equivariant`, the main induction. | **~250.** `fire-stable-*` and the `residual-recon` eval-reasoning are reusable as-is (category 1 inside a category-2 file). `pvv-trans` is definitional for `permuteˢ` (`trans ↦ ∘ˢ`); `pvv-inverse-*` = `permuteˢ-inv` (~25 lines). `map⁺-lift-≅↭` is **obsolete** (vertex-level `permuteˢ`). The main induction ports 1:1 over `EdgeStepRˢ` with `fire-mid-equivariant` shrunk per the row above. |
| `Sub/RunInterchangeTail` | 201 | Tail extension `RunInterchange ps [] → RunInterchange ps qs` via equivariance + telescoping. | **~150 (1:1).** Pure plumbing over the equivariance lemma; the definitional-prefix trick (`pe-stack qs A ≡ pe-stack (e ∷ e' ∷ qs) sp`) holds identically for `process-edgesˢ`. |
| `EdgeStepNaturality` | 259 | Cross-iso per-edge naturality (`edge-step-term-rel`) for Lemma 0: SKIP/SKIP by `objUIP`, FIRE/FIRE split into box (`box-of-cong`) + permute (K). | **~120.** In S: the box part is `genˢ`-constructor congruence over `castˢ` (UIP), the permute part is `perm-rigidˢ`; the `subst₂-∘-distrib` calculus vanishes. |
| `IsoTransport` | 756 | Lemma 0: decoder runs of `H` (order `τ`) and `J` (order `range`) agree across `Φ : H ≅ᴴ J` up to relabel transport. | **~350–400.** The induction structure (per-edge naturality + stack alignment `map φ`) survives; the `unflatten (map vlab …)` boundary `subst₂`s become `castˢ (cong (map vlab) …)`. The biggest single remaining category-2 item after the swap core. |
| `DecodeOrdBoundary` | 204 | (K₁) two `Valid` witnesses at `range` agree via `eval-rigid`+K; (K₂) boundary `subst₂` algebra with `objUIP`. | **~100.** K₁ = `perm-rigidˢ`. K₂'s `subst₂ HomTerm` algebra becomes `castˢ` algebra — but note this module sits at the **boundary with the free SMC** (`decodeP`), so its strict version belongs to the `Strict.Embed` phase, not to the in-S chain. |
| `Sub/SigmaBlockCommRaw` | 510 | `σ-block-comm-raw`: iterated two-block braiding = `permute (++-comm)`, at X-level, via `BraidBlock`/`BraidPermute` iteration. | **~130 in S** (`PermAlgebra`: `σ-singʳˢ` + `σ-singˡˢ` + `σ-permˢ`, plus `σ-unitˢ`): the strict hexagon `σ-hexˢ` decomposes σ directly with `castˢ`-only re-bracketing; the rotate/associator iteration machinery vanishes. |

### Category (3): obsolete under strictness

| module | LOC | why it exists | why it dies in S |
|---|---|---|---|
| `Sub/HomTermTransport` | 314 | `subst₂ HomTerm` cancellation/commutation/distribution; `pvv-relabel`; `decode-attempt-extract` | The `castˢ` kit (`cast-fuse`, `cast-irrel`, `∘-cast-split`, `cast-⊗-frame{ʳ}`, `cast-⊗ˡ`, `cast-resp`, `cast-id`) in `FreeStrictSMC` IS the strict replacement, 60 lines once and for all, derived by refl-matching + UIP. (`decode-attempt-extract`/`Linear⇒cod-Unique` are boundary utilities that survive where the boundary phase needs them, not part of the in-S chain.) |
| `Sub/BlockNFBraid` | 717 | σ-block-comm at vertex level via `map⁺`-transport bridge from the raw X-level lemma; `frame-ext` (++⁺ʳ framing through `unflatten-++-≅`) | `permuteˢ` is vertex-level: **no `map⁺ vlab` transport bridge exists to manage**. `frame-ext` = `permuteˢ-frame` (already proven, 25 lines, in `FreeStrictSMC.Perm′`). σ-block-comm = `PermAlgebra.σ-permˢ`. |
| `Sub/BlockNFNf2` | 1333 | `block-nf-generic` + `nf-bracket-proof`: single-order "located boxes = 3-block tensor" through `unflatten-++-≅` views (the Mac-Lane bracket chase) | The "views" `view-in≅/view-out≅` are coherence isos of right-associated `unflatten`; in S the 3-block object is literally `(A ++ A') ++ R̂` and the bracket identity is `⊗-assocˢ` + `⊗-id` (`box-suffix-ˢ` is 2 lines). The located normal form is derived directly in `SwapCore` (~150 lines for both orders). |
| `Sub/BlockNFVoutCoh` | 314 | `vin-coh`/`vout-coh`: σ-frame vs `permute` reconciliation via faithfulness | Folded into `SwapCore`'s Claim-C `perm-rigidˢ` uses; the σ-frame-to-permute step is `σ-permˢ` + `permuteˢ-frame`. |
| `Sub/SigmaBlockHexagon` | 975 | Lifts σ/hexagon/Yang–Baxter algebra to the *wrapped* σ-block pattern `α⇒ ∘ (σ ⊗ id) ∘ α⇐` that `permute (swap …)` produces in the right-associated world | In S, `permuteˢ (swap x y p) = σˢ [x] [y] ⊗ˢ permuteˢ p` — the bare σ with **no α-wrapping**. The hexagon is the `σ-hexˢ` axiom itself; Yang–Baxter cascades never arise because the located normal form never needs to re-associate. **Entire module has no strict counterpart.** |
| `Sub/PermutationTransport` (Monoidal half) | ~150 of 349 | `to/from-subst₂-≅`, `frame-transport` for `unflatten-++-≅` framing | `unflatten-++-≅` does not exist in S (`⊗ˢ = ++` on the nose); replaced by `cast-⊗-frame{ʳ}`. |

**Headline arithmetic.** The per-swap Mac-Lane mass — `FireMidEquivariant` (408) +
`FireMidInterchange` (477) + `BlockNFBraid` (717) + `BlockNFNf2` (1333) + `BlockNFVoutCoh`
(314) + `SigmaBlockCommRaw` (510) + `SigmaBlockHexagon` (975) + `HomTermTransport` (314) ≈
**5048 LOC** — is replaced in S by `PermAlgebra` (~430 LOC, one-off σ/permute algebra) +
the located-NF part of `SwapCore` (~330 LOC), i.e. roughly a **6–7× collapse**, on top of
the ~2050 LOC of category-(1) combinatorics that is reused unchanged.

---

## 2. Where K-faithfulness enters, and its strict analogue

`FaithfulnessResidual` (in `Categories.PermuteCoherence.Faithfulness`, field
`permute-resp-≅↭ : (p q : xs ↭ ys) → p ≅↭ q → permute p ≈Term permute q`, where
`p ≅↭ q = eval-↭ p ≈-fb eval-↭ q`) is threaded from `DecodeRelRespIsoWired` (bound to the
proven `FaithfulnessInductive.faithfulness`) into:

1. `SwapStep.FrontSwap.final-permute-coh` — reconcile the two final `Valid` permutes
   across the reshuffle (via `eval-rigid` on `Unique (cod H)`).
2. `Sub/FireMidEquivariant` — `permute-inv-right` self-loop cancellation.
3. `Sub/StackEquivariance.residual-recon` → `StackUnique` (`eval-rigid` on `Unique` stacks).
4. `Sub/BlockNF{Nf2,VoutCoh}` — `coh-in`/`coh-out` and the bracket keystone.
5. `EdgeStepNaturality.fire-perm-rel` → `IsoTransport` (cross-iso permute agreement).
6. `DecodeOrdBoundary` (K₁).
7. `DecodeRelDecodeP` (decoder agreement, outside part (II) proper).

**Pattern**: every single use is of the *rigid* form — two vertex-level derivations into a
codomain that is `Unique` (sourced from the `Reservoir≤1` invariant or `⟪⟫-cod-unique`),
identified by the generic, already-proven `Rigid.eval-rigid`, then K closes
`≅↭ ⇒ ≈Term`, with `eval-map⁺`/`subst₂-FinBij-≈` bridging the `map⁺ vlab` X-level lift.

**Strict analogue** (what the strict chain must provide):

```agda
permˢ-K : ∀ {xs ys : List (Fin nV)} (p q : xs ↭ ys) → p ≅↭ q → permuteˢ p ≈ˢ permuteˢ q
```

stated directly at the **vertex** level (no `map⁺ vlab` lift, no `subst₂-FinBij`
transport — `permuteˢ` is indexed by vertex lists).  All uses factor through

```agda
perm-rigidˢ : Unique ys → (p q : xs ↭ ys) → permuteˢ p ≈ˢ permuteˢ q
perm-rigidˢ u p q = permˢ-K p q (eval-rigid u p q)
```

`SwapCore` takes `permˢ-K` as a module parameter, mirroring how the non-strict chain
threads `K : FaithfulnessResidual`.  Discharge options (later phase): (a) re-run the
`FaithfulnessInductive` argument inside `HomS` (the induction is *simpler* in S: the
`permuteˢ` clauses have no α-wrapping, and `_≈ˢ_`'s σ axioms match the FinBij normal form
step for step); or (b) transport along the strictification functor `Strict.Embed` from the
proven free-SMC `faithfulness` (requires the embedding to be `≈`-reflecting on permute
images, which is the planned `Embed`-faithfulness obligation).

---

## 3. Structural deltas the port should exploit

* **Vertex-level `permuteˢ`.** `Perm′ (Fin nV) vlab` indexes `permuteˢ` by vertex lists;
  the entire `map⁺ vlab` lifting layer (`map⁺-lift-≅↭`, `eval-map⁺`, `pvv-relabel`,
  `BlockNFBraid`'s transport bridge) disappears.
* **`trans ↦ ∘ˢ`, `prep ↦ idˢ ⊗ˢ_` are definitional** for `permuteˢ`, so the
  `pvv-trans`-style lemmas of `StackEquivariance` cost zero, and structured derivations
  (`Perm.trans p q`) can be *chosen* and then swapped for the decoder's actual witnesses
  via one `perm-rigidˢ` each — the strict proofs never chase a specific derivation shape.
* **Casts are UIP-trivial.** All residual `subst₂`-management becomes the 8-lemma `castˢ`
  kit; cons/singleton-headed `++-assoc`/`map-++` casts reduce definitionally.
* **`Validˢ = Valid`.** Stack functions agree, so `SwapValidity`, `StackUniqueReach`,
  `FinOrderNoInv`, `DepIrrefl`, `WiringLemmas`, the connectivity theorem and the whole
  order-theory spine are shared between the two pipelines, not duplicated.

---

## 4. The strict per-swap core (deliverable B) — design

`Strict/SwapCore.agda` ports the substantive content of
`RunInterchangeEmptyTail.run-interchange₀`.  Architecture (see the module header for the
proof-level detail):

* `Strict/PermAlgebra.agda` — one-off `HomS`/`permuteˢ` algebra over `Build`:
  `⊗-unitˡˢ` (derived by the Kelly conjugation trick: `idˢ {[]} ⊗ˢ_` is σ-conjugation of
  the right-unitor cast, hence injective, and idempotent by `⊗-assocˢ`/`⊗-id`),
  `σ-unitˢ` (σ against `[]` is a cast of `idˢ`), `permuteˢ-inv`, `permuteˢ-frameˡ`
  (`++⁺ˡ` = left `idˢ ⊗ˢ_` frame), the singleton braidings `σ-singʳˢ`/`σ-singˡˢ`, the
  block braiding `σ-permˢ` (σ of two mapped blocks = `permuteˢ` of a structural
  block-comm derivation — the strict `σ-block-comm`), the box-slide lemmas, and
  `box-crossˢ` (the σ-naturality MID step).
* `SwapCore` per-H module, parameters `(H) (dih) (lin : Linear H) (permˢ-K)`:
  `EdgeStepRˢ` view; `fire-mid-interchangeˢ` (both-fire core) proved by deriving each
  order's run into the **located normal form**
  `permuteˢ w ∘ˢ castˢ ((genˢ g ⊗ˢ (genˢ g' ⊗ˢ idˢ)) ) ∘ˢ castˢ (permuteˢ λ)`
  using `extract-ein'`-sourced residual location, `perm-rigidˢ` to restructure the
  decoder's locating permutes, and `box-crossˢ`/`σ-permˢ` for the interchange; then the
  four-way `build` + `run-interchange₀ˢ` mirroring the non-strict skeleton with the
  `Reservoir≤1`-sourced `Unique` witnesses.

The remaining part-(II) work after `SwapCore` (in dependency order):
strict `StackEquivariance` port (~250) → `RunInterchangeTail` port (~150) →
`SwapStep`/`swap-≈` port (~250) → `IsoInvarianceConcrete` rename (~160) →
`EdgeStepNaturality`+`IsoTransport` port (~500) → boundary phase
(`DecodeOrdBoundary`-analogue against `Strict.Embed`) → discharge `permˢ-K`.
