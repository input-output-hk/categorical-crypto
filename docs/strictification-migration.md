# Strictification migration plan

Goal: re-base the soundness proof `soundness-full-wired : ⟪f⟫ ≅ᴴ ⟪g⟫ → f ≈Term g`
on a presented strict SMC `S`, collapsing the per-site Mac-Lane tax
(`unflatten-++-≅` conjugation + `subst₂` transport) into a one-time boundary.
The FINAL THEOREM STATEMENT IS UNCHANGED. Validated by three spikes
(commits `0d19e9f`, `e33915c`, `83b5f54`); projection: live closure
34.6k → ~22k LOC.

## Architecture

```
            st                         emb ∘ mapS  (= embF)
 HomTerm ───────► HomS[FlatGen] ─────────────────────────► HomTerm
   │                  ▲   │                                (between unflattens)
   ⟪_⟫                │   │ ≈ˢ-reasoning (parts Iˢ, IIˢ)
   ▼                  │   ▼
 Hypergraph ──► decodePˢ (strict decoder)
```

* `S = FreeStrictSMC.Build X _≟X_ mor`: objects `List X`, `⊗ˢ = ++`,
  `_≈ˢ_` with strict axioms; ALL casts are UIP-trivial equality transports
  handled by the derived cast kit (no cast axiom in `_≈ˢ_`).
* Two instances: `Strict.Core` (mor = `FlatGen`, where all graph reasoning
  happens) and `Strict.Embed`'s (mor = `morL` = HomTerms between unflattens,
  what `emb` embeds). `FreeStrictSMC.Map` is the homomorphism between them
  along `J-flat (flat g) = bridge (Agen g)`.

## Final assembly (target shape)

```
soundness: iso : ⟪f⟫ ≅ᴴ ⟪g⟫
  part (II)ˢ:  decodePˢ f ≈ˢ decodePˢ g          -- strict iso-invariance
  part (I)ˢ:   st f ≈ˢ decodePˢ f  (and for g)    -- strict roundtrip
  ⇒ st f ≈ˢ st g
  embF-resp-≈ˢ: embF (st f) ≈Term embF (st g)
  st-roundtrip: embF (st h) ≈Term bridge h
  ⇒ bridge f ≈Term bridge g
  bridge-cancel (existing, SoundnessFullWired) ⇒ f ≈Term g
```

K-faithfulness stays the single deep input: the proven non-strict kernel
(`FaithfulnessInductive.faithfulness`) is transported FORWARD through `st`
(st-resp-≈ on `permute-via-vlab p ≈Term permute-via-vlab q`, plus the glue
`st (permute-via-vlab p) ≈ˢ castˢ … (permuteˢ p)`) to discharge the strict
residual `permˢ-K : p ≅↭ q → permuteˢ p ≈ˢ permuteˢ q`, which phase-1
modules take as a module parameter.

## Phases

* **Phase 0 (DONE, `2d2c8e5`)**: spikes promoted —
  `Categories.FreeStrictSMC` (`Build` + `Map` + `Perm′`),
  `Soundness/Strict/{Core,Embed,Decoder}.agda`.
* **Phase 1 — term/boundary side DONE; decoder side partial.**
  1. `Strict/Boundary.agda` (DONE, `1527f34`): `J-flat`, `embF`/
     `embF-resp-≈ˢ`, `st`, `st-resp-≈` (all 24 `≈Term` axioms; hexagon
     derived in S from `σ-hexˢ` by inverse-uniqueness), `st-roundtrip :
     embF (st f) ≈Term bridge f` (reuses the existing atomic bridge
     lemmas).  This is the entire term-side of the strictification.
     Supporting: `σ-unitˢ` axiom + derived `σ-unitʳˢ`/`⊗-unitˡˢ` in
     `FreeStrictSMC` (`b16f058`); `Embed.σ-unit-case` boundary payment.
  2. `Strict/DecodeS.agda` (PARTIAL, `cbe8a8d`): the full strict decoder
     `decodePˢ` with totality TRANSFERRED from `decode-attempt-LinearP`
     via `stacks-agree` (strict/non-strict decoders branch on the same
     `extract-prefix` calls) + `extract-exact-total`.  **STILL TODO:** the
     shape lemmas — atomic (`decodePˢ atom ≈ˢ st atom`, K-laden via
     `perm-rigidˢ`), ∘-shape (port of `DecodeComposePruned`), and the
     ⊗-shape.
  3. `Strict/PermSupport.agda` (DONE, this phase): the deferred residual
     `permˢ-K` + `perm-rigidˢ` (the K-interface every decoder shape lemma
     and part (II)ˢ consumes; discharged once in phase 2).
  4. `Strict/Separability.agda` (DONE) — `permuteˢ-frameˡ` (left mirror via
     `++⁺ˡ`) + the left-frame `extract-elem`/`-prefix` skip-prefix family +
     `block-disjointˡ`.  **FINDING:** the naive left-frame *term* separability
     (`… ≈ˢ idˢ {L} ⊗ˢ …`) is FALSE — `edge-stepˢ` prepends fired outputs, so
     active edges on a suffix push outputs in front of the untouched prefix
     `L` (a *braided* form).  The right frame works only because the
     untouched region is a SUFFIX.  ⇒ the ⊗-shape's K-block reordering must be
     reconciled by the final permute (the σ/K content), not a clean 2nd frame.
  5. `Strict/DecodeShapes.agda` (DONE) — the 7 atomic structural shapes
     `decodePˢ atom ≈ˢ st atom` (id/λ/ρ/α; `hId`-shaped: `nE≡0`, `dom≡cod`),
     closed by `perm-rigidˢ` (sourcing `Unique` from `Linear⇒cod-Unique`) +
     `coe` algebra.  `permˢ-K` a poly module parameter.  σ/∘/⊗ shapes are the
     documented downstream remainder.
  6. `Strict/SwapCore.agda` (DONE) — the part-(II)ˢ per-swap ALGEBRA BRICKS:
     `EdgeStepRˢ` view, `permuteˢ-frameˡ`, `permuteˢ-inv-{left,right}`,
     `box-residual-split`, and `box-crossˢ` (the genuine located N-kernel =
     σ-conjugation lifted by `_⊗ˢ idˢ{R}`, replacing the non-strict
     `box-interchange`).  Remaining: `fire-mid-interchangeˢ` (SimLoc-driven
     located NF) + the four-way `build`/`run-interchange₀ˢ` skeleton (near-1:1
     term-free port).
  7. `Strict/PermDischarge.agda` (DONE — KEYSTONE) — `permˢ-K` discharged via
     route (i): reuse the term-free combinatorial kernel
     `FaithfulnessInductive.complete-proven` (`eval-≈ ⇒ ≅↭ⁱ`) directly at the
     vertex set + the strict mirror `permuteˢ-resp-≅↭ⁱ` (one `_≈ˢ_` axiom per
     `≅↭ⁱ` generator; strict swap cases SIMPLER — singleton frames make the
     `⊗-assocˢ` casts `refl`).  This sidesteps the non-faithful `embF`
     reflection entirely.  `permˢ-K` is fully constructed in
     `Discharge.Main (braidX : StrictBraid)` — the SOLE remaining residual is
     `StrictBraid`, ONE closed hypothesis-free equation (Yang-Baxter on 3
     singletons + tail; strict mirror of the proven `σ-block-hexagon`).
     `permˢ-K`'s universal+semantic quantification thus collapses to a single
     coherence goal.
* **Phase 2 (DONE — keystones + 3/4 shapes)**: `permˢ-K` DISCHARGED axiom-free
  (`Braid.agda` proves `StrictBraid` generic over `mor` via `st`-transport from
  the proven `σ-block-hexagon`; `PermK.agda` wires it at `FlatGen`).  Three
  shape lemmas COMPLETE: atomic (`DecodeShapes`), σ (`DecodeSigmaS` +
  `BlockSwapComm` — `bswap-σ` fully proven), ∘ (`DecodeComposeS3` —
  `decodePˢ-∘-shape` UNCONDITIONAL).  The K-side equivariance keystone
  `process-edges-equivariantˢ` PROVEN (`StackEquivS`).  Part-(II)ˢ per-swap
  `build`/`run-interchange₀ˢ` skeleton + both coherences `vin/vout-cohˢ` PROVEN.
  27 strict modules, all green, zero postulates, live root untouched.
* **Phase 2 remainder (2 box-braid-class residuals, all bricks present, fully
  mapped, NO new math)** — the two heaviest cast-threading chains:
  - `KBlockσ` (⊗-shape's last residual; `TensorBraidS` G-side ✓ →
    `TensorKBlock` box-slide bricks `box-block-slideˢ` ✓): the K-prepend
    box-braid (strict twin of non-strict `box-braid` ~2700).  Remaining:
    `fire-slideˢ` → `kblock-factorˢ` induction → equivariance → reconcile.
  - `fire-mid` `nf-eqˢ` (`FireMidS`/`S2`/`S3`/`Finish`: `cross-NFˢ`,
    `box-resid3ˢ`, `fire-locatedˢ`, `box-merge-σˢ`, `mid-rigid`, step-3
    `midD-σ` all ✓).  Remaining steps (1)+(4)+(5): box-order σ-conjugation
    (`g'⊗g→g⊗g'` via `box-crossˢ`) + 2 `perm-rigidˢ` absorptions into
    `Lin₁`/`Lout₁`.  Closing it ⇒ unconditional `run-interchange₀ˢ`.
* **Phase 3**: part (I)ˢ assembly `st f ≈ˢ decodePˢ f` (atomic+σ+∘ ✓, ⊗ pending
  `KBlockσ`); port part (II) wiring (`RunInterchangeTail` → `swap-≈` →
  `IsoInvarianceConcrete` → `EdgeStepNaturality` → `IsoTransport`) over the
  reusable term-free order theory; `decodePˢ-resp-iso`.
* **Phase 4**: re-point `SoundnessFullWired` at the strict assembly;
  full rebuild green; DELETE the orphaned non-strict chain
  (DecodeTensorShape 4.4k + BoxKernel + SigmaBlock*/BlockNF* term mass +
  RunInterchange*/FireMid* term mass + DecodeRelDecodeP middle hop, per the
  part-2 map's obsolete column) — the size win; update docs.

## Invariants (every phase)

* `--safe --without-K`, postulate-free, axiom-free everywhere; residuals are
  module PARAMETERS with a named discharge plan, never postulates.
* `Solver/Tests.agda`, `GConstruction.agda`, `Coherence/Symmetric/Test`,
  `CategoricalCrypto` stay green at every merge.
* Casts: keep cons/singleton frames (they reduce); state lemmas with
  abstract cast-proof arguments (`cast-irrel` absorbs them); never match on
  a cast proof in a statement-position with-function.

## OUTCOME (2026-06-14, complete)

**DONE.** `SoundnessFullWired.soundness-full-wired : ⟪f⟫ ≅ᴴ ⟪g⟫ → f ≈Term g`
is now proven entirely through the strictified pipeline — `--safe --without-K`,
**zero postulates**, axiom-free (the deep Kelly residual `permˢ-K` discharged
via the combinatorial kernel + the proven `StrictBraid`).  All consumers
unaffected (type unchanged): `Solver/{Tests,Interpret,Split}`, `GConstruction`,
`Coherence/{Symmetric/Test,DecodeSpike}`.

* Phase 0–3: the strict SMC `S`, boundary (`st`/`embF`/`st-roundtrip`), strict
  decoder, all shape lemmas (atomic/σ/∘/Agen/⊗), three deep keystones
  (`permˢ-K`, `bswap-σ`, `process-edges-equivariantˢ`), part (I)ˢ + part (II)ˢ,
  and the capstone `SoundnessStrict`.  45 files / ~15.8k LOC under
  `Soundness/Strict/`.
* Phase 4: re-pointed `SoundnessFullWired`; **deleted the orphaned non-strict
  chain** (commit `1adfe1f`): 22 files / **12,820 LOC** (incl.
  `DecodeTensorShape` 4392, `BlockNFNf2` 1333, `DecodeAgenSigmaShape` 1094,
  `IsoTransport` 756, …), via import-graph analysis (dead set closed under the
  importer relation, disjoint from the live closure).  File count 220 → 198.

**Honest LOC verdict.** The strict re-proof (~15.8k) is itself large — larger
than the deleted non-strict term-level chain (12.8k) — so strictification did
NOT deliver the original ~50% headline-LOC reduction on its own.  The win is
STRUCTURAL: the per-site Mac-Lane tax (`unflatten-++-≅` conjugation, `subst₂`
transport, BoxKernel brackets, `map⁺`-lift) is replaced by the one-time
boundary + the UIP-trivial `castˢ` kit; every strict module came out cleaner
and the σ-block/box-braid coherence is now a handful of named axioms
(`σ-hexˢ`/`σ-natˢ`/`σ-σˢ`) rather than thousands of chased lines.  The strict
pipeline is the better foundation for further reduction (e.g. a strict
coherence solver) — pursued separately.
