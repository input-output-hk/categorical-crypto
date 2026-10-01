# Post-reorg cleanup findings (2026-06-17)

> **Repointing note (2026-08-10).** `Soundness/Discharge/DepIrrefl.agda` no longer exists:
> it was dissolved into `Soundness/Discharge/FinOrderNoInv.agda`, where its statement is
> exported as `NoSelfDep` (types byte-identical).  Read every `DepIrrefl` below — including
> the file paths in the findings' `files:` lines — as `FinOrderNoInv`.

> **Repointing note (2026-09-02).** Two more paths in the findings' `files:` lines are gone:
> `Soundness/Discharge/BridgeAlphaFormCompound.agda` (Discharge-5, `:393-395`) was folded into
> `Soundness/Bridge/BridgeCoherence.agda`, and `Strict/Perm/PermSupport.agda` (Strict-8,
> `:448-451`) was dissolved into `Strict/Perm/PermK.agda`, which is where the `permˢ-K`
> discharge that finding asks to document now lives. Both findings' recommendations were
> overtaken by those moves; this is an archived corpus, read it as of 2026-06-17.

> **Repointing note (2026-09-02, round 12).** Three more claims below are overtaken:
> (a) `Invariant.hId-cod≡dom`, on the KEEP lists at `:47` and `:273`, has been DELETED —
> the seven structural atoms re-derive at the literal `hId`, so no `dom ≡ cod` lemma is
> needed at all; (b) Model-5's "the local copies are genuine stdlib reimplementations"
> (`:285`) no longer holds — `Invariant.inject+-inj`/`raise-inj` are the one-line
> delegations to `↑ˡ-injective`/`↑ʳ-injective` that finding recommended; (c) Discharge-3's
> "`StackUnique:74` already imports `CountCombinatorics sig`" (`:394`) is stale — the count
> leaf takes no signature parameter any more.

Produced by the `post-reorg-cleanup-discovery` workflow: one read-only auditor per major
subtree -> adversarial verification of every finding -> cross-cutting synthesis.
58 findings: 49 confirmed, 9 needs-care, 1 dropped as false-positive.

## Summary

The tree is in good shape post-restructure: the bulk of confirmed findings are low-risk dead-code and reexport/comment trims that are self-contained and verifiable. The biggest single wins are concentrated dead-code blocks — PermuteCoherence-1 (~210 LOC of unused permute-inverse machinery in FaithfulnessK), Strict-2 (~95 LOC verbatim pvv-relabelˢ duplicate), and several 24-55 LOC dead blocks in Model/SoundnessCore/Discharge. Two recurring cross-cutting patterns dominate: the ↑ˡ≢↑ʳ disjointness lemma is copied 5-6 times across Model/SoundnessCore/Discharge, and tiny just≢nothing/nothing≢just helpers are re-derived in several files; both warrant a single shared Fin/Maybe-util module. Save the genuine simplifications (Model-10, PermuteCoherence-7) for last — they are high-risk, perf/OOM-sensitive, and self-flagged for human review.

## Prioritized actions

### 1. FaithfulnessK: ~210 LOC of permute-inverse / residual-equivalence machinery is dead; only σ-block-self-inverse-direct is consumed
- subtree **PermuteCoherence** · kind `dead-code` · verdict **confirmed** · confidence high · ~210 LOC · risk **low**
- action: Delete the dead §1-4/§6-10 blocks plus the FinBij/Eval/EvalSoundness/TransSelfLoopResidual imports; keep σ-block-self-inverse-direct + its two private helpers (σ-block-involutive/σ-block-natural₃); rewrite the header. Sole importer FaithfulnessInductive:64 takes only σ-block-self-inverse-direct.

### 2. pvv-relabelˢ (+3 private helpers) verbatim-duplicated between TensorPVVRelabel and DecodeComposeAssembly
- subtree **Strict** · kind `duplicate` · verdict **confirmed** · confidence high · ~95 LOC · risk **medium**
- action: Import TensorPVVRelabel as PVV into DecodeComposeAssembly, delete the inline pvv-relabelˢ + 3 helpers (309-404), and repoint call sites 560/626 to PVV.pvv-relabelˢ. Drop-in verified: the shared mp/permuteˢ-X come from the same StackEquiv re-export chain.

### 3. UnflattenMonoidal §3 (to-uf-map-++/from-uf-map-++) and to-uf-cong/from-uf-cong helpers are unused
- subtree **SoundnessCore** · kind `dead-code` · verdict **confirmed** · confidence high · ~55 LOC · risk **low**
- action: Delete to-uf-cong/from-uf-cong (227-241) and §3 to-uf-map-++/from-uf-map-++ + banner (251-275); trim docstring bullets (17-21). All four importers use explicit using-lists naming none of these (folds with SoundnessCore-8 stale comment).

### 4. BridgeCoherence: dead decode-id-is-id-unit/Var and α⇒-coh-list/α⇐-coh-list
- subtree **SoundnessCore** · kind `dead-code` · verdict **confirmed** · confidence high · ~54 LOC · risk **low**
- action: Delete decode-id-is-id-unit/Var (+ comment 65-67) and the purely self-recursive α⇒-coh-list/α⇐-coh-list; then (SoundnessCore-4) delete the now-dead DecodeAttemptLinearP import block at lines 28-32.

### 5. bridge⁻¹ / bridge-cancel in capstone Soundness.agda are a dead unused copy of SoundnessParam's
- subtree **SoundnessCore** · kind `dead-code` · verdict **confirmed** · confidence high · ~46 LOC · risk **low**
- action: Delete the 'Inverse bridge + cancellation' section (lines 43/44-74) plus now-dead imports (flatten, unflatten/unflatten-flatten-≈, bridge, _≅_, FM/HomReasoning). CRITICAL per Strict-1: KEEP Model.Translation (⟪_⟫) — the surviving `soundness` signature still needs it. Strict-1 and SoundnessCore-1 are the same finding; do once.

### 6. hId-vlab-lookup subsystem in Invariant.agda is entirely dead
- subtree **Model** · kind `dead-code` · verdict **confirmed** · confidence high · ~144 LOC · risk **medium**
- action: Delete Invariant.agda:159-291 and :314-324 (KEEP range-++ :293-312, which has many external consumers; KEEP hId-cod≡dom :109). Drop the orphaned imports at :163-167. Note `length` (line 25, separate import) stays live.

### 7. Facade Soundness.agda carries dead bridge⁻¹ / bridge-cancel (capstone view, same as SoundnessCore-1/Strict-1)
- subtree **SoundnessCore** · kind `dead-code` · verdict **confirmed** · confidence high · ~0 LOC · risk **low**
- action: DUPLICATE of rank 5 (SoundnessCore-1 / Strict-1 describe the same capstone block). Resolve once; do not double-count LOC. Listed only to flag the overlap explicitly.

### 8. Four unused subst₂/⊗ transport helpers in HomTermTransport
- subtree **Discharge** · kind `dead-code` · verdict **confirmed** · confidence high · ~24 LOC · risk **low**
- action: Delete ⊗id-∘∘, pvl-refl, subst₂-cod-trans, subst₂-dom-trans from HomTermTransport (zero call sites tree-wide). KEEP ⊗id-∘ (live: SeparableStack:596).

### 9. FaithfulnessInductive.faithfulness and its sole helper permute-resp-≅↭ⁱ are unused
- subtree **PermuteCoherence** · kind `dead-code` · verdict **confirmed** · confidence high · ~24 LOC · risk **low**
- action: Delete faithfulness (658-660), then permute-resp-≅↭ⁱ (237-252) whose only user was faithfulness; trim header narration. PermDischarge imports only _≅↭ⁱ_/complete.

### 10. Boundary-fixed wrapper Hypergraphᵇ / mkHᵇ / forget is unused everywhere
- subtree **Model** · kind `dead-code` · verdict **confirmed** · confidence high · ~24 LOC · risk **low**
- action: Delete Core.agda:52-71 + header para :13-16 + the now-unused Data.Product import :24. Live domL/codL path (46-50) is independent.

### 11. Dead aliases objUIP-UIP, lemmaA/≺-resp-≅ᴴ, box-of-cong
- subtree **Discharge** · kind `dead-code` · verdict **confirmed** · confidence high · ~18 LOC · risk **low**
- action: Delete objUIP-UIP (ObjUIP:51-52), lemmaA + its alias ≺-resp-≅ᴴ (EdgeDependency:87-91), and box-of-cong (EdgeStepRelation:54-64). Live raw directions ≺⇒ψ≺/ψ≺⇒≺ and objUIP′ stay.

### 12. Three unused private subst₂ helpers in Iso.agda
- subtree **Model** · kind `dead-code` · verdict **confirmed** · confidence high · ~13 LOC · risk **low**
- action: Delete subst₂-≡, subst₂-refl, subst₂-subst₂-sym from Iso.agda's private block. KEEP subst₂-sym-subst₂ (220) and subst₂-trans (244/346).

### 13. flat-match (non-subst) and its private help-subst-eq are unused in Verify.agda
- subtree **Solver** · kind `dead-code` · verdict **confirmed** · confidence high · ~26 LOC · risk **low**
- action: Delete flat-match (160-177) and standalone help-subst-eq (105-112); reword the 3 narrative comments to cite flat-match-subst. KEEP help-subst-eq2 and UIP-ListX (live).

### 14. Dead public wrapper bridge-α⇒-form-⊗-⊗ in BridgeAlphaFormCompound
- subtree **Discharge** · kind `dead-code` · verdict **confirmed** · confidence high · ~10 LOC · risk **low**
- action: Delete the dead wrapper bridge-α⇒-form-⊗-⊗ (687-693) and its banner; the lone consumer (Boundary) calls BAFC.Worker.work directly.

### 15. shape-ok? in Match/Match.agda has zero callers
- subtree **Solver** · kind `dead-code` · verdict **confirmed** · confidence high · ~11 LOC · risk **low**
- action: Delete shape-ok? (Match.agda:54-64); tryEdge inlines the check to keep the proofs. KEEP local _≟L_ (used by tryEdge:92,94).

### 16. Four genuinely-dead helpers in Util/Prune.agda (corrected from refuted finding)
- subtree **Model** · kind `dead-code` · verdict **needs-care** · confidence high · ~30 LOC · risk **low**
- action: Delete ONLY index-∈-filter-irrelevant/subst-∈-filter-index/subst-lookup-nonMem/classify-lookup-nonMem (self-only, confirmed dead). Do NOT delete remap-inj₁/remap-inj₂/classify-inj₁-∈ — the original finding was refuted on those (live external consumers in LinearHComposeP/FinOrderNoInv).

### 17. deriveAtomEq byte-identical (mod aliases) in Verify.agda and Rewrite/SubMatch.agda
- subtree **Solver** · kind `duplicate` · verdict **confirmed** · confidence high · ~10 LOC · risk **low**
- action: Hoist one generic deriveAtomEq over two Hypergraphs + vertex map into Match/Totals.agda (already imported by both); import from Verify and Verify-Sub and delete the two copies.

### 18. count-mono-cons re-defined locally in StackUnique despite importing CountCombinatorics
- subtree **Discharge** · kind `duplicate` · verdict **confirmed** · confidence high · ~5 LOC · risk **low**
- action: Delete StackUnique's local copy (125-129) and add count-mono-cons to the existing CountCombinatorics using-list (line 74).

### 19. Private tabulate-+ helper duplicated verbatim in Linearity and LinearHComposeP
- subtree **SoundnessCore** · kind `hoist` · verdict **confirmed** · confidence high · ~6 LOC · risk **low**
- action: Make tabulate-+ non-private in Linearity, add it to LinearHComposeP's using-list (already imports a batch from Linearity), delete the LinearHComposeP copy.

### 20. just≢nothing / nothing≢just re-derived privately across Discharge and Strict Interchange files
- subtree **Discharge** · kind `duplicate` · verdict **confirmed** · confidence high · ~8 LOC · risk **low**
- action: Import just≢nothing from HomTermTransport in StackEquiv and DecodeCompose; drop the three local copies (Discharge-7). Independently, make SwapCore.nothing≢just non-private and delete SwapCoreRun's copy (Strict-5). Touching Strict/ needs coordination but proofs are trivial 2-liners.

### 21. Unused D⁺ = Soundness.Decode.Decode module alias (and its import) in Rewrite/Deep.agda
- subtree **Solver** · kind `dead-code` · verdict **confirmed** · confidence high · ~2 LOC · risk **low**
- action: Delete D⁺ alias (Deep.agda:78) and the supporting bare import (Deep.agda:61); body decodes via DL⁺/U⁺.

### 22. Several unused imports across Model files
- subtree **Model** · kind `reexport` · verdict **confirmed** · confidence high · ~4 LOC · risk **low**
- action: Drop ++-identityʳ/++-assoc and the yes/no line from FromAPROP; drop bare subst from Iso line 20; drop map-cong and bare subst from PrunedCompose lines 29/34.

### 23. UnflattenMonoidal re-exports c-iso-assoc-from-cons that no consumer uses
- subtree **SoundnessCore** · kind `reexport` · verdict **confirmed** · confidence high · ~1 LOC · risk **low**
- action: Drop c-iso-assoc-from-cons from the re-export using-list at line 38 (keep c-iso-assoc-from); the def stays in CIsoAssocFromCons.

### 24. Unflatten.agda imports unitorˡ and associator but uses neither
- subtree **SoundnessCore** · kind `reexport` · verdict **confirmed** · confidence high · ~1 LOC · risk **low**
- action: Reduce line 29 to `using (unitorʳ)`.

### 25. Unused co-located import IsoInvarianceConcrete as IC in DecodePRespIso
- subtree **Strict** · kind `reexport` · verdict **confirmed** · confidence high · ~1 LOC · risk **low**
- action: Delete line 60 (import ... as IC, never qualified-used).

### 26. Unused stdlib import Permutation.Propositional.Properties as PermProp in Separability
- subtree **Strict** · kind `reexport` · verdict **confirmed** · confidence high · ~1 LOC · risk **low**
- action: Delete line 69 (alias never used).

### 27. FaithfulnessK imports unflatten (and post-cleanup permute) it never uses
- subtree **PermuteCoherence** · kind `reexport` · verdict **confirmed** · confidence high · ~2 LOC · risk **low**
- action: Trim line 29 to `using (α⇐-comm)`; drop unflatten now, permute falls out with PermuteCoherence-1 (rank 1).

### 28. Faithfulness.faithfulness alias (rename of permute-resp-≅↭) is unused
- subtree **PermuteCoherence** · kind `dead-code` · verdict **confirmed** · confidence high · ~5 LOC · risk **low**
- action: Delete the faithfulness alias (154-158) and its docstring bullet (line 18). wide⇒narrow / permute-self-loop-id(-wide) and the residual records stay live.

### 29. Canonical.bubble-to-front defines the same suc-injective local helper twice
- subtree **PermuteCoherence** · kind `duplicate` · verdict **confirmed** · confidence high · ~6 LOC · risk **low**
- action: Replace both ℕ-level copies (Canonical:66-67, 72-73) with Data.Nat.Properties.suc-injective import (or hoist one copy).

### 30. Interface labeling vlab-c and its lemmas copy-pasted across FromAPROP boundary functions
- subtree **Model** · kind `hoist` · verdict **confirmed** · confidence high · ~45 LOC · risk **medium**
- action: Introduce one shared module holding vlab-c/vlab-inL/vlab-inR/lem-L/lem-R (parallel to existing hTensor-impl); open from hGen/hSwap and their 4 boundary lemmas, preserving result types (many Soundness consumers depend on them).

### 31. Kahn topological-sort block duplicated between Rewrite/Deep.agda and Rewrite/DeepProv.agda
- subtree **Solver** · kind `duplicate` · verdict **confirmed** · confidence high · ~28 LOC · risk **medium**
- action: Hoist remove1/consume + a generic findReady/kahn over an edge type with ins/outs : E → List (Fin nV) into a shared Rewrite/Kahn.agda; instantiate from Build (Edge) and BuildO (EdgeO). A shared generic kahn structurally enforces the load-bearing identical edge order.

### 32. List-equality deciders ≡-dec _≟X_ repeated as local one-liners across Match-pipeline files
- subtree **Solver** · kind `hoist` · verdict **confirmed** · confidence high · ~3 LOC · risk **low**
- action: Optionally fold `_≟LX_ = ≡-dec _≟X_` into the shared helper created for deriveAtomEq (rank 17) and reuse from Verify/Match/Deep; skip if not co-bundled (low value).

### 33. Cross-subtree: ↑ˡ≢↑ʳ disjointness lemma copied 5-6 times — consolidate via Model.Invariant
- subtree **SoundnessCore** · kind `hoist` · verdict **confirmed** · confidence high · ~18 LOC · risk **low**
- action: Hoist ↑ˡ≢↑ʳ (+ ↑ʳ≢↑ˡ flip) into Model.Invariant (already exports inject+-inj/raise-inj/disj-L-R; no import cycle). Import in DecodeProperties + Linearity and delete the private copies; covers SoundnessCore-5 and Discharge-1's DepIrrefl/FinOrderNoInv/LinearHComposeP sites in one move. See cross-cutting note.

### 34. inject+-inj / raise-inj / ↑ˡ-inj / ↑ʳ-inj re-implement stdlib ↑ˡ-injective / ↑ʳ-injective
- subtree **Model** · kind `duplicate` · verdict **needs-care** · confidence high · ~30 LOC · risk **medium**
- action: Make Invariant.inject+-inj/raise-inj thin wrappers over stdlib ↑ˡ-injective/↑ʳ-injective; point Prune at them. Cross-subtree (touches Soundness call sites) and must adapt implicit/explicit args — flag for human.

### 35. ↑ˡ/↑ʳ disjointness lemma exists in 5 places; Prune's copy has a spurious parameter
- subtree **Model** · kind `duplicate` · verdict **needs-care** · confidence medium · ~16 LOC · risk **medium**
- action: Consolidate to one clean lemma but plan for Prune's module-param entanglement (m is a module param) and Prune's own 3-explicit-arg call sites at 320/321; note 5 copies not 3. Overlaps rank 33; flag for human.

### 36. subst₂-resp-≈Term general form (HomTermTransport) subsumes the List-X-specialised BridgeCoherence copy
- subtree **Discharge** · kind `duplicate` · verdict **needs-care** · confidence medium · ~7 LOC · risk **medium**
- action: Optionally drop the BridgeCoherence specialisation and call the general HomTermTransport one with `cong unflatten` threaded through; adds a BridgeCoherence→HomTermTransport import edge, so verify index shapes at each call site first.

### 37. SigmaBlockHexagon is a generic free-SMC coherence module misplaced under APROP/Discharge
- subtree **Discharge** · kind `misplaced` · verdict **confirmed** · confidence high · ~0 LOC · risk **medium**
- action: Relocate to Categories.FreeSMC (or Categories.PermuteCoherence) and update the ~6 importers; removes the library→application upward dependency. No content change; verify no new cycle (Faithfulness does not import it).

### 38. ⟦v⟧ record + FreeFunctorHelper/⟦_⟧₀ derivation duplicated between Frontend.ObjInterp and Frontend.Solver telescopes
- subtree **Solver** · kind `simplify` · verdict **needs-care** · confidence medium · ~8 LOC · risk **medium**
- action: Have a human/agda check whether `open ObjInterp C ⟦_⟧ᵖ₀ using (⟦_⟧₀)` typechecks inside Solver's parameter telescope before de-duplicating; ⟦_⟧₀ is needed at line 120 and is only re-exported via `open Go ... public`. Small (~8 LOC) saving.

### 39. Single-atom test scaffolding duplicated across four Test configurations
- subtree **Coherence** · kind `hoist` · verdict **confirmed** · confidence low · ~12 LOC · risk **low**
- action: Optional: add a parameterized `module Atoms1 (A : C.Obj)` (small shared Test helper, mirroring Atoms3) and open it in the four single-atom configs; watch the a/a₀ rename (Rewrite.agda) and that Atoms3 does not export _⊗₀_. Marginal value.

### 40. Symmetric.agda interface comment omits the rewriteDeepProv* tool family the showcase uses
- subtree **Coherence** · kind `stale-comment` · verdict **confirmed** · confidence high · ~6 LOC · risk **low**
- action: Add a rewriteDeepProv(ₙ/To)! bullet to the Symmetric.agda palette comment, noting they are the carve-provenance-guided gate-#1 variants the Frobenius showcase uses.

### 41. Test.agda palette and Frobenius.agda header narrate rewriteDeep! but code uses rewriteDeepProvTo!
- subtree **Coherence** · kind `stale-comment` · verdict **confirmed** · confidence high · ~8 LOC · risk **low**
- action: Update Frobenius.agda:16 and Test.agda:37-51 to name rewriteDeepProvTo! for the Frobenius steps, retarget the rewriteDeepTo! pointer to Test.Deep only, and add a rewriteDeepProv* palette entry.

### 42. Wiring re-exports focFrame with zero users anywhere
- subtree **Coherence** · kind `reexport` · verdict **confirmed** · confidence high · ~1 LOC · risk **low**
- action: Drop focFrame from the Wiring re-export using-list at Symmetric.agda:92 (keep deepFrame, which is consumed); skip if an out-of-repo client relies on it.

### 43. ExtractPrefix.agda and FreeSMC/Steps.agda cite nonexistent module Discharge.APROPMacLaneFromSMC
- subtree **SoundnessCore** · kind `stale-comment` · verdict **confirmed** · confidence high · ~4 LOC · risk **low**
- action: Update both docstrings to keep the definitional-sharing reason and drop the dead APROPMacLaneFromSMC / process-steps-maybe reference.

### 44. Comments use deprecated stdlib names inject+ / raise instead of _↑ˡ_ / _↑ʳ_
- subtree **Model** · kind `stale-comment` · verdict **confirmed** · confidence high · ~8 LOC · risk **low**
- action: Targeted comment edits (NOT blind search-replace — 'raise' over-matches English) in the cited Invariant/FromAPROP/PrunedCompose lines; Invariant:181 is moot if the Model-2 dead region (rank 6) lands.

### 45. UnflattenMonoidal docstring falsely claims §3/box-of bridges consume to-uf-map-++ via Decode.mid'
- subtree **SoundnessCore** · kind `stale-comment` · verdict **confirmed** · confidence high · ~3 LOC · risk **low**
- action: Remove the §3 narration with the dead defs (folds into rank 3 / SoundnessCore-2) and drop the cf.-mid' provenance; mid' uses inline subst₂.

### 46. PartI header says 'two in-progress shapes' but only decodePˢ-⊗ remains a parameter
- subtree **Strict** · kind `stale-comment` · verdict **confirmed** · confidence high · ~4 LOC · risk **low**
- action: Reword the PartI header + line 62 to one parameter (decodePˢ-⊗); note decodePˢ-Agen is now concrete via DecodeGen.

### 47. Capstone Strict/Soundness.agda header narrates a 'SINGLE remaining residual pending' that is now discharged
- subtree **Strict** · kind `stale-comment` · verdict **confirmed** · confidence high · ~6 LOC · risk **low**
- action: Note decodePˢ-⊗ is now supplied unconditionally by TensorKBlockFinal.decodePˢ-⊗-concrete and the capstone is already re-pointed; module stays correctly parametric.

### 48. PermSupport claims permˢ-K is discharged via Strict.Embed; actual route is PermDischarge+Braid
- subtree **Strict** · kind `stale-comment` · verdict **confirmed** · confidence high · ~3 LOC · risk **low**
- action: State permˢ-K is discharged axiom-free in Strict.Perm.PermK via PermDischarge + Braid.Generic.strict-braid (not Strict.Embed, which is not even imported there).

### 49. SwapCore header describes a pre-split combined architecture (build/run-interchange₀ˢ live elsewhere now)
- subtree **Strict** · kind `stale-comment` · verdict **confirmed** · confidence high · ~8 LOC · risk **low**
- action: Retitle SwapCore to its real role (strict EdgeStepRˢ algebra bricks) and move the build/run-interchange₀ˢ bullets to SwapCoreRun/FireMid.

### 50. TensorReconcile labels braidˢ a 'REMAINING RESIDUAL NOT discharged'; it is discharged by TensorBraid
- subtree **Strict** · kind `stale-comment` · verdict **confirmed** · confidence high · ~6 LOC · risk **low**
- action: Reword the residual section: braidˢ is the parameter discharged downstream by Strict.Tensor.TensorBraid (via KBlockσ), making the ⊗-shape unconditional (TensorKBlockFinal has zero postulates).

### 51. Provenance narration about a removed insert postulate in InsertProof / Word
- subtree **PermuteCoherence** · kind `stale-comment` · verdict **confirmed** · confidence high · ~4 LOC · risk **low**
- action: Reword InsertProof:5-6 and Word:386 to describe the current insert-thm dependency without the removed postulate (Word:457-458 is accurate, leave it).

### 52. Mirror permute-slide lemmas (++⁺ˡ vs ++⁺ʳ) split across FireMidEquivariant / BlockNFBraid
- subtree **Discharge** · kind `simplify` · verdict **needs-care** · confidence medium · ~0 LOC · risk **medium**
- action: Optional/low-value: the shared subst₂ core (frame-transport) is ALREADY factored in PermutationTransport; only co-locate the two directional slide statements if a human judges it worthwhile. estLOC 0 — no concrete saving. Flag for human.

### 53. hTensor-impl and hComposeP-impl share a near-identical edge-routing + reduction-lemma skeleton
- subtree **Model** · kind `duplicate` · verdict **needs-care** · confidence medium · ~80 LOC · risk **high**
- action: Do NOT execute blindly. The abstraction must also parameterize vlab + vertex-count + the map-via lemma (not just the router); ~12 external consumers make names/types load-bearing and it is perf/OOM-sensitive. Leave as documented future work; measure typecheck memory before/after.

### 54. BringToFrontAdjL / BringToFrontAdjR are mirror-image proofs of the two adjacency cases
- subtree **PermuteCoherence** · kind `simplify` · verdict **needs-care** · confidence high · ~60 LOC · risk **high**
- action: Leave as-is unless a human confirms a safe orientation-parameterised merge; the Fin-arithmetic differs in a load-bearing (non-textual-mirror) way and a merge risks these proofs / typecheck cost.

## Cross-cutting patterns

### ↑ˡ≢↑ʳ disjoint-injection lemma copied 5-6 times across the tree
- subtrees: Model, SoundnessCore, Discharge
- The same splitAt-↑ˡ/splitAt-↑ʳ case-absurd disjointness proof recurs as: Model.Invariant-adjacent + Util.Prune:296 (spurious param), Soundness.Decode.DecodeProperties:79, Soundness.Linearity.Linearity:123, and three Discharge copies (DepIrrefl:69, FinOrderNoInv:107, LinearHComposeP:461). The clean consolidation target is Model.Invariant (already exports inject+-inj/raise-inj/disj-L-R, imports no Soundness layer, so no cycle). One hoist there covers SoundnessCore-5 and Discharge-1 simultaneously. Separately, inject+-inj/raise-inj themselves reimplement stdlib ↑ˡ-injective/↑ʳ-injective (Model-5) and Prune's disjointness has a spurious module/explicit param (Model-6) — these stdlib-rewrap and de-param moves are the needs-care, cross-subtree tail of the same cluster and should be flagged for human.

### Tiny Maybe-discrimination helpers (just≢nothing / nothing≢just) re-derived in many files
- subtrees: SoundnessCore, Discharge, Strict
- HomTermTransport exports just≢nothing but it is re-declared privately in StackEquiv and twice in DecodeCompose (Discharge-7), while nothing≢just is re-derived privately in SwapCore and SwapCoreRun (Strict-5). All are byte-identical 2-liners. Import from HomTermTransport / un-private the SwapCore copy. Touching Strict/ files needs build coordination but the proofs are trivial; bundle with the Fin-util consolidation as a 'shared trivial-lemma' pass.

### Capstone bridge⁻¹ / bridge-cancel dead block reported from two subtree vantage points
- subtrees: SoundnessCore, Strict
- SoundnessCore-1 and Strict-1 describe the SAME dead 'Inverse bridge + cancellation' block in the single capstone src/Categories/APROP/Hypergraph/Soundness.agda (the live copy lives in Strict/SoundnessParam.agda). Resolve once. The load-bearing caveat from Strict-1: when deleting the dead imports, KEEP Model.Translation (⟪_⟫) — the surviving `soundness` signature still needs it. Do not double-count the ~46 LOC.

### Stale tool-palette/provenance comments after the rewriteDeepProv* and strictification refactors
- subtrees: Coherence, Strict, SoundnessCore, PermuteCoherence
- A broad documentation-drift pass: the Coherence Symmetric/Test palettes still say rewriteDeep! where the Frobenius showcase uses rewriteDeepProvTo! (Coherence-1/2); several Strict headers narrate already-discharged residuals or pre-split module layouts (Strict-6/7/8/9/10); SoundnessCore-7/8 and PermuteCoherence-6 cite removed/nonexistent modules and postulates. All are low-risk, no-code-change edits totaling ~50 LOC of comments; worth doing together as a single 'doc reconciliation' commit so the post-restructure narration matches the current module graph. Use targeted edits, not blind search-replace (Model-9: 'raise' over-matches English prose).

### Generic free-SMC module SigmaBlockHexagon sitting under the APROP application layer
- subtrees: Discharge, PermuteCoherence
- SigmaBlockHexagon (Discharge-2) is parameterized only by FreeMonoidalData and imported by Categories.FreeSMC.* and Categories.PermuteCoherence.FaithfulnessInductive — a library reaching up into the application package. Relocating it to Categories.FreeSMC or Categories.PermuteCoherence removes the upward dependency and is content-neutral. Related: PermutationTransport's map⁺-↭-reflexive duplicates FinBijSubst's (Discharge-8) but pulling it in would ADD a new APROP→PermuteCoherence edge, so leave that one alone — the dependency-direction tradeoffs in this cluster cut opposite ways and need per-case judgement.

## Per-subtree verified findings (full evidence)

### Model

- **Model-1 Boundary-fixed wrapper Hypergraphᵇ / mkHᵇ / forget is unused everywhere** — `dead-code`, confirmed/high, ~24 LOC, risk low
    - files: src/Categories/APROP/Hypergraph/Model/Core.agda
    - verify: `rg -nw 'Hypergraphᵇ|mkHᵇ|forget' src spikes` returns ONLY Core.agda lines 14/53/57/59/68/70/71 — all definitions/comments inside the defining file, zero external importers. Read Core.agda: Hypergraphᵇ(57), constructor mkHᵇ(59), forget(70-71) form a self-contained block (52-71). The live code path (domL/codL at 46-50) is independent. `rg -nw 'Σ-syntax|_,_|_×_'` over Core.agda shows the Data.Product import (line 24) is used ONLY on its own import line — dead once the wrapper goes.
    - rec: Delete Core.agda:52-71 + header para :13-16 + the now-unused Data.Product import :24.
- **Model-2 hId-vlab-lookup subsystem in Invariant.agda is entirely dead** — `dead-code`, confirmed/high, ~144 LOC, risk medium
    - files: src/Categories/APROP/Hypergraph/Model/Invariant.agda
    - verify: Tree-wide `rg -nw` shows hId-vlab-lookup, cast-inject+-cong₂, cast-raise-cong₂ are self-only; hId-nV≡len-flatten appears only at 169-174 and inside hId-vlab-lookup's where-blocks (227-288); hId-dom≡range only self-recursive (317-324). The finding's KEEP list is verified live: range-++ has external consumers in CruxSpike/DecodeAttempt/TensorKBlockFinal/TensorBraid/FinOrderNoInv/DecodeComposeAssembly/DecodeAttemptLinearP; hId-cod≡dom used at line 109 (NOT in delete range :43-49); inject+-inj/raise-inj/disj-L-R/range-Unique all live. Orphaned imports confirmed: `lookup`(163)/`cast`(164)/`length-++`(165 used only in dead region + line 174 which IS deleted)/`+-suc`(166)/`[_,_]′`+`_⊎_`(167) used only inside the deleted block; CAVEAT: `length` (line 25, separate import) stays live (139/147).
    - rec: Delete Invariant.agda:159-291 and :314-324 (keep range-++ :293-312); drop orphaned imports at :163-167.
- **Model-3 Five unused helpers in Util/Prune.agda** — `dead-code`, needs-care/high, ~30 LOC, risk low
    - files: src/Categories/APROP/Hypergraph/Util/Prune.agda
    - verify: REFUTED IN PART. Tree-wide `rg -nw` shows 3 of the 7 named helpers ARE live with external consumers: remap-inj₁ (LinearHComposeP.agda:23 import, :203), remap-inj₂ (LinearHComposeP.agda:23 import, :542), classify-inj₁-∈ (FinOrderNoInv.agda:69 import, :330). Deleting them as the finding states would break the build, and the finding's own KEEP list omits them — contradicting the import graph. The other 4 (index-∈-filter-irrelevant:109, subst-∈-filter-index:122, subst-lookup-nonMem:132, classify-lookup-nonMem:163) are confirmed self-only and genuinely dead.
    - rec: Delete ONLY index-∈-filter-irrelevant/subst-∈-filter-index/subst-lookup-nonMem/classify-lookup-nonMem; KEEP remap-inj₁/remap-inj₂/classify-inj₁-∈ (live external consumers).
- **Model-4 Three unused private subst₂ helpers in Iso.agda** — `dead-code`, confirmed/high, ~13 LOC, risk low
    - files: src/Categories/APROP/Hypergraph/Model/Iso.agda
    - verify: `rg -nw` within Iso.agda: subst₂-≡ only at 28/32, subst₂-refl only at 35/37, subst₂-subst₂-sym only at 46/49 — never applied. Live ones confirmed: subst₂-sym-subst₂ used at 220, subst₂-trans at 244/346. All five are in a `private` block (line 25) so no external use is possible.
    - rec: Delete subst₂-≡, subst₂-refl, subst₂-subst₂-sym from Iso.agda's private block.
- **Model-5 inject+-inj / raise-inj / ↑ˡ-inj / ↑ʳ-inj re-implement stdlib ↑ˡ-injective / ↑ʳ-injective** — `duplicate`, needs-care/high, ~30 LOC, risk medium
    - files: src/Categories/APROP/Hypergraph/Model/Invariant.agda, src/Categories/APROP/Hypergraph/Util/Prune.agda
    - verify: Confirmed triplicate. Invariant.agda:56-74 (inject+-inj/raise-inj, implicit i/j, external consumers HomTermInvariant:28/57/113, FinOrderNoInv:59/182, DecodeProperties:19/155/231). Prune.agda:275-293 (↑ˡ-inj/↑ʳ-inj, private, used only at 317/331). stdlib `/nix/store/.../standard-library-2.3/src/Data/Fin/Properties.agda:148` ↑ˡ-injective and :161 ↑ʳ-injective exist with `∀ n (i j : Fin m)` and are ALREADY used directly by Linearity.agda:36/106/115, TensorBraid.agda:76/140/178, DepIrrefl.agda:47/138/141. So the local copies are genuine stdlib reimplementations. Refactor is cross-subtree (touches Soundness call sites) and must adapt implicit/explicit args, hence needs-care not a clean confirm.
    - rec: Make Invariant.inject+-inj/raise-inj thin wrappers over stdlib ↑ˡ-injective/↑ʳ-injective; point Prune at them; cross-subtree, flag for human.
- **Model-6 ↑ˡ/↑ʳ disjointness lemma exists in 3 places; Prune's copy has a spurious parameter** — `duplicate`, needs-care/medium, ~16 LOC, risk medium
    - files: src/Categories/APROP/Hypergraph/Util/Prune.agda, src/Categories/APROP/Hypergraph/Soundness/Discharge/FinOrderNoInv.agda, src/Categories/APROP/Hypergraph/Soundness/Discharge/DepIrrefl.agda
    - verify: Core claim confirmed but UNDERCOUNTED: the lemma exists in FIVE places, not three. ↑ˡ-↑ʳ-disjoint in Prune.agda:296 (spurious (k:ℕ) param), FinOrderNoInv.agda:107 (clean ∀{m k}), LinearHComposeP.agda:461 (specialized local); plus ↑ˡ≢↑ʳ alias in DepIrrefl.agda:69, DecodeProperties.agda:79, Linearity.agda:123. DepIrrefl:67 comment corroborates 'Prune.↑ˡ-↑ʳ-disjoint is parameterised on an unused n'. CAVEAT: Read Prune.agda:192 — ↑ˡ-↑ʳ-disjoint lives inside `module _ {n m : ℕ}`, so `m` is a module param; the proposed `∀ {m k}` normalization requires extracting it from the module AND breaks Prune's own 3-explicit-arg call sites at 320/321. Real duplicate cluster but the fix is non-trivial + cross-subtree.
    - rec: Consolidate to one clean lemma but plan for Prune's module-param entanglement and its own call sites; note there are 5 copies not 3; flag for human.
- **Model-7 Interface labeling vlab-c and its lemmas are copy-pasted across FromAPROP boundary functions** — `hoist`, confirmed/high, ~45 LOC, risk medium
    - files: src/Categories/APROP/Hypergraph/Model/FromAPROP.agda
    - verify: Read FromAPROP.agda:280-393. `vlab-c i = [ lookup (flatten A) , lookup (flatten B) ]′ (splitAt nA i)` re-declared at 286,317,331,352,362,382 (6×). vlab-inL at 288,318,363,383 (4×); vlab-inR at 292,332,365,385 (4×). lem-L/lem-R byte-identical between domL-hSwap (367-372) and codL-hSwap (387-392) (2× each). Counts match the finding. A shared `module hGenSwap-impl` is feasible (parallel to existing hTensor-impl pattern). Risk medium: results feed many Soundness consumers so the boundary-lemma types must be preserved.
    - rec: Introduce one module holding vlab-c/vlab-inL/vlab-inR/lem-L/lem-R; open it from hGen/hSwap and their 4 boundary lemmas, preserving result types.
- **Model-8 Several unused imports across Model files** — `reexport`, confirmed/high, ~4 LOC, risk low
    - files: src/Categories/APROP/Hypergraph/Model/FromAPROP.agda, src/Categories/APROP/Hypergraph/Model/Iso.agda, src/Categories/APROP/Hypergraph/Model/PrunedCompose.agda
    - verify: FromAPROP: `rg -nw '++-identityʳ|++-assoc'` → only line 38 import; `rg -nw 'yes|no'` → yes 0 body uses, no only in English comments (90/246/337 'no vertices/edges'), so line 43 dead. Iso: `grep -nP 'subst(?!₂)'` → only line 20 import (every body use is subst₂). PrunedCompose: `rg -nw map-cong` → only line 29; `grep -nP 'subst(?!₂)'` → only line 34 (body uses are all subst₂). All four trims verified.
    - rec: Drop ++-identityʳ/++-assoc and the yes/no line from FromAPROP; drop bare subst from Iso line 20; drop map-cong and bare subst from PrunedCompose lines 29/34.
- **Model-9 Comments still use deprecated stdlib names inject+ / raise instead of _↑ˡ_ / _↑ʳ_** — `stale-comment`, confirmed/high, ~8 LOC, risk low
    - files: src/Categories/APROP/Hypergraph/Model/Invariant.agda, src/Categories/APROP/Hypergraph/Model/FromAPROP.agda, src/Categories/APROP/Hypergraph/Model/PrunedCompose.agda
    - verify: Read the cited lines: Invariant.agda:52-53/76/181/295 all say 'inject+'/'raise'; :295 states `range (n+m) ≡ map (inject+ m)… ++ map (raise n)…` but the body at :298 uses `map (_↑ˡ m)`/`map (n ↑ʳ_)`. FromAPROP:72 'map through inject+/raise'. PrunedCompose:153 'elab-c at inject+ / raise inputs'. Live code uses _↑ˡ_/_↑ʳ_ throughout, so comments are stale. CAVEATS: (a) Invariant:181 sits inside the Model-2 dead region (moot if that lands); (b) a blind 'raise'→'_↑ʳ_' replace could over-match the English word 'raise', so do targeted edits.
    - rec: Targeted comment edits (not blind search-replace) to use _↑ˡ_/_↑ʳ_ in the cited lines.
- **Model-10 hTensor-impl and hComposeP-impl share a near-identical edge-routing + reduction-lemma skeleton** — `duplicate`, needs-care/medium, ~80 LOC, risk high
    - files: src/Categories/APROP/Hypergraph/Model/FromAPROP.agda, src/Categories/APROP/Hypergraph/Model/PrunedCompose.agda
    - verify: Read FromAPROP.agda:110-203 and PrunedCompose.agda:69-203. The 6 reduction lemmas (ein-c-inj₁-red/eout-c-inj₁-red/ein-c-inj₂-red/eout-c-inj₂-red/elab-c-inj₁/elab-c-inj₂) and ein-c/eout-c/elab-c are structurally parallel with identical `with splitAt … | splitAt-↑ˡ/↑ʳ … | refl = refl` proofs. DIFFERENCES are larger than 'just the router': K-side route (injR vs remapP), composite vertex count (G.nV+K.nV vs G.nV+count-non K.dom), composite vlab (vlab-c [G.vlab,K.vlab] vs vlab-P [G.vlab,λ-pruned]), the map-via-* lemma (map-via-raise vs map-via-remapP), and hComposeP's extra bdy-eq + boundary apparatus. `rg -l` confirms ~12 external consumer files (Linearity/DecodeAttempt/TensorKBlock*/TensorBraid/LinearHComposeP/DecodeAttemptLinearP/DepIrrefl/FinOrderNoInv + spike), so names/types are load-bearing. Refactor is cross-subtree, perf/OOM-sensitive, and the abstraction is incomplete as stated. Finding self-rates high-risk/low-conf and flags for human — appropriate.
    - rec: Do NOT execute blindly; the abstraction must also parameterize vlab + vertex-count + map-via lemma, not only the router. Leave as documented future work; verify typecheck-memory before/after.

### Solver

- **Solver-1 shape-ok? in Match/Match.agda has zero callers** — `dead-code`, confirmed/high, ~11 LOC, risk low
    - files: src/Categories/APROP/Hypergraph/Solver/Match/Match.agda
    - verify: `grep -rn shape-ok? src/ spikes/ docs/` returns ONLY Match.agda:54 (def name) and :59 (def equation) — zero references anywhere else. Read confirms tryEdge (Match.agda:90-100) inlines the arity/atom-list shape check via its own `with`-block, keeping the equality proofs p/q to feed flat-match-subst — so it structurally cannot call the Bool-returning shape-ok? (which discards proofs). The local _≟L_ (Match.agda:51-52) is used by tryEdge:92,94, so it stays.
    - rec: Delete shape-ok? (Match.agda:54-64); keep _≟L_.
- **Solver-2 flat-match (non-subst) and its private help-subst-eq are unused in Verify.agda** — `dead-code`, confirmed/high, ~26 LOC, risk low
    - files: src/Categories/APROP/Hypergraph/Solver/Match/Verify.agda
    - verify: `grep -rnE 'flat-match([^-]|$)' src/ spikes/`: every hit outside Verify.agda:160-161 (the def) is a narrative comment (Split.agda:69, Match.agda:18, Verify.agda:16, spikes/GlobalPhiDirect.agda:144). All live calls use flat-match-subst (Match.agda:99, SubMatch.agda:161, Verify.agda:241). The spike GlobalPhiDirect.agda:33 opens Verify `using (module Verify)` — the inner submodule, NOT top-level flat-match. `grep -rnE 'help-subst-eq([^2]|$)'` shows help-subst-eq only at def (105,110) + its single use at line 174 inside flat-match's `compare (yes p)`, so it dies with flat-match. help-subst-eq2 (143/147/154) is independent (inner to flat-match-subst) and stays; UIP-ListX is shared by both and stays. flat-match=18 LOC, help-subst-eq=8 LOC.
    - rec: Delete flat-match (160-177) and standalone help-subst-eq (105-112); reword the 3 narrative comments to cite flat-match-subst.
- **Solver-3 Unused D⁺ = Soundness.Decode.Decode module alias (and its import) in Rewrite/Deep.agda** — `dead-code`, confirmed/high, ~2 LOC, risk low
    - files: src/Categories/APROP/Hypergraph/Solver/Rewrite/Deep.agda
    - verify: `grep -onE 'D⁺' Deep.agda` returns ONLY line 78 (the alias definition) — zero uses in the body. Read confirms tryEmb decodes via DL⁺ (DecodeLean, line 79) and the body uses U⁺ at 196-197. The bare `import ...Soundness.Decode.Decode` (line 61) exists only to back the D⁺ alias; DecodeLean is imported separately (line 62) and reuses what it needs from Decode internally. Removing alias+import is safe.
    - rec: Delete D⁺ alias (Deep.agda:78) and the supporting import (Deep.agda:61).
- **Solver-4 deriveAtomEq byte-identical (mod aliases) in Verify.agda and Rewrite/SubMatch.agda** — `duplicate`, confirmed/high, ~10 LOC, risk low
    - files: src/Categories/APROP/Hypergraph/Solver/Match/Verify.agda, src/Categories/APROP/Hypergraph/Solver/Rewrite/SubMatch.agda
    - verify: Read both: Verify.deriveAtomEq (195-204) and Verify-Sub.deriveAtomEq (134-143) have identical signature shape ((φ)→(∀i→vlab₂(φi)≡vlab₁ i)→∀xs ys→ys≡map φ xs→map vlab₂ ys≡map vlab₁ xs) and identical body `trans (cong (map vlab₂) p) (trans (sym (map-∘ xs)) (map-cong φ-lab xs))`; only the module aliases (J/H vs S/L) differ, which are arbitrary Hypergraph args. Both files already `import ...Match.Totals` (Verify:32, SubMatch:46). Totals.agda is a plain unparameterized module — a generic deriveAtomEq over two Hypergraphs + vertex map hoists cleanly. No other deriveAtomEq exists in tree. Each used 2× per file (verify body + atom-ein/atom-eout record fields).
    - rec: Hoist one generic deriveAtomEq into Match/Totals.agda; import from both Verify and Verify-Sub.
- **Solver-5 Kahn topological-sort block duplicated between Rewrite/Deep.agda and Rewrite/DeepProv.agda** — `duplicate`, confirmed/high, ~28 LOC, risk medium
    - files: src/Categories/APROP/Hypergraph/Solver/Rewrite/Deep.agda, src/Categories/APROP/Hypergraph/Solver/Rewrite/DeepProv.agda
    - verify: Read both blocks: Deep.agda:129-157 (remove1/consume/findReady/kahn, private in Build) vs DeepProv.agda:100-126 (same four, private in BuildO). remove1 and consume are literally identical (both on List (Fin S.nV)). findReady/kahn differ ONLY by carried record type (Edge with .ins/.outs/.lab vs EdgeO with .ins/.outs/.origin), both accessed solely via .ins/.outs. DeepProv.agda:99 documents 'kahn mirror (verbatim from Deep.agda, minus labels)'. A generic findReady/kahn over an edge type E with `ins outs : E → List (Fin nV)` unifies them. CAVEAT: byte-for-byte agreement is load-bearing — the gate relies on identical edge order — so any hoist must preserve that; a shared generic kahn enforces it structurally (a plus). Note: the finding called DeepProv 'untracked'; it has since been committed (`git ls-files` matches, clean) — does not affect the duplicate verdict, only that co-location is now a normal edit not a new-file move.
    - rec: Hoist remove1/consume + generic findReady/kahn into a shared Rewrite/Kahn.agda; instantiate from Build (Edge) and BuildO (EdgeO).
- **Solver-6 ⟦v⟧ record + FreeFunctorHelper/⟦_⟧₀ derivation duplicated between Frontend.ObjInterp and Frontend.Solver telescopes** — `simplify`, needs-care/medium, ~8 LOC, risk medium
    - files: src/Categories/APROP/Hypergraph/Solver/Frontend.agda
    - verify: Read Frontend.agda:91-122: ObjInterp (91-102) and Solver (110-120) both build the same `⟦v⟧ = record { C=C.U; Monoidal-C=C.monoidal; Symmetric-C=λ⦃_⦄→C.symmetric }` (lines 97 and 116) and re-run `FreeFunctorHelper asFreeMonoidalData ⟦v⟧` + `Go ⟦_⟧ᵖ₀` to get ⟦_⟧₀. The duplication is REAL. But the proposed `open ObjInterp C ⟦_⟧ᵖ₀ using (⟦_⟧₀)` must happen INSIDE Solver's parameter telescope (⟦_⟧₀ is needed at line 120, before the ⟦_⟧ᵖ₁ parameter at 121), whereas ObjInterp exposes ⟦_⟧₀ only via `open Go ... public` in its body (line 102). Whether a `let open ObjInterp ...` in a telescope can pull that re-exported name cleanly is exactly the typecheck question the finding flags. Cannot be confirmed without running agda (disallowed). Risk medium; the ~8-line saving is small.
    - rec: Human/agda check whether `open ObjInterp C ⟦_⟧ᵖ₀ using (⟦_⟧₀)` typechecks inside Solver's telescope before de-duplicating.
- **Solver-7 List-equality deciders `≡-dec _≟X_` repeated as local one-liners across Match-pipeline files** — `hoist`, confirmed/high, ~3 LOC, risk low
    - files: src/Categories/APROP/Hypergraph/Solver/Match/Verify.agda, src/Categories/APROP/Hypergraph/Solver/Match/Match.agda, src/Categories/APROP/Hypergraph/Solver/Rewrite/Deep.agda
    - verify: `grep -rn '≡-dec _≟X_'` shows exactly three identical definitions: Verify.agda:75 (_≟LX_), Match.agda:52 (_≟L_), Deep.agda:67 (_≟LX_) — all `≡-dec _≟X_` on List X with the same signature atom decider, so genuinely shareable. The _≟F_ list variants (DecodeLean.agda:76 H.nV, SubMatch.agda:125 S.nV ≡-decL, Verify.agda:191 J.nV) are at distinct local Fin nV types and are correctly excluded as non-shareable. Observation is factually accurate. LOW VALUE: three trivial one-liners; the finding itself conditions the hoist on Solver-4's shared module being created and marks it optional — agree.
    - rec: Optionally fold `_≟LX_ = ≡-dec _≟X_` into Solver-4's shared helper and reuse from Verify/Match/Deep; skip if not co-bundled.

### SoundnessCore

- **SoundnessCore-1 Facade Soundness.agda carries dead bridge⁻¹ / bridge-cancel duplicating SoundnessParam.agda** — `dead-code`, confirmed/high, ~32 LOC, risk low
    - files: src/Categories/APROP/Hypergraph/Soundness.agda, src/Categories/APROP/Hypergraph/Soundness/Strict/SoundnessParam.agda
    - verify: Read Soundness.agda: only export is `soundness` (line 84) = `SA.soundness-assembled TKF.decodePˢ-⊗-concrete`, using neither bridge⁻¹ nor bridge-cancel. grep `bridge⁻¹|bridge-cancel` over src+spikes: occurs in Soundness.agda (defs 46/50/53/54), in SoundnessParam.agda (its own copy 57/61/64/65 AND consumed at 115-118), plus one prose mention in Strict/Boundary:18. Diffed the two bodies: byte-for-byte identical. All 4 facade importers (spikes/Leg3Recomp:47, GConstructionIdentityCoherence:138, GConstructionCoherence/Wiring:39, Solver/Split:44) use `using (soundness)` — none names bridge⁻¹/bridge-cancel. grep of unflatten/bridge/_≅_/FM/flatten inside Soundness.agda body: every one is used ONLY inside the dead lemmas (incl. flatten on line 25, used only in bridge⁻¹'s type), so the proposed import trims are all valid.
    - rec: Delete the 'Inverse bridge + cancellation' section (lines 43-74) plus now-dead imports (lines 25 flatten, 27-28 unflatten/unflatten-flatten-≈, 29-30 bridge, 36 _≅_, 38-41 FM/HomReasoning).
- **SoundnessCore-2 UnflattenMonoidal §3 (to-uf-map-++/from-uf-map-++) and to-uf-cong/from-uf-cong helpers are unused** — `dead-code`, confirmed/high, ~55 LOC, risk low
    - files: src/Categories/APROP/Hypergraph/Soundness/Base/UnflattenMonoidal.agda
    - verify: grep over src+spikes: to-uf-map-++/from-uf-map-++ appear ONLY at their defs (261/267, 269/275) + docstring line 19 — zero external refs. to-uf-cong/from-uf-cong appear ONLY at their defs (227/233, 235/241), docstring 17, and inside the two dead map-++ defs (267/275) + the §3 banner line 259 — no non-dead caller. All four UnflattenMonoidal importers (Strict/Embed:28, Strict/Boundary:35, Discharge/Sub/SeparableStack:76, Discharge/Sub/BoxKernel:56) use explicit using-lists (cancel-mid-iso, c-iso-assoc-to/from, subst-id-dom/cod, conj-lemma, bridge-dom/cod, subst-2) — none names the four helpers.
    - rec: Delete to-uf-cong/from-uf-cong (227-241) and §3 to-uf-map-++/from-uf-map-++ + banner (251-275), and trim docstring bullets (17-21).
- **SoundnessCore-3 BridgeCoherence: dead decode-id-is-id-unit / decode-id-is-id-Var and α⇒-coh-list / α⇐-coh-list** — `dead-code`, confirmed/high, ~54 LOC, risk low
    - files: src/Categories/APROP/Hypergraph/Soundness/Bridge/BridgeCoherence.agda
    - verify: grep over src+spikes: decode-id-is-id-unit/decode-id-is-id-Var appear only at docstring line 30 + their defs (69/70, 75/76) — no caller. α⇒-coh-list/α⇐-coh-list appear only at defs (397/402/403, 417/422/423) + their own self-recursive step (414, 434) — no non-recursive caller. Read 393-435: both α-coh-list are purely self-recursive, only depend on the live α⇒/⇐-form-list, no external entry. Both importers (Strict/Boundary:41-43 using bridge-id-is-id/bridge-λ⇒/⇐-is-id/ρ⇒/⇐-coherence/α⇒-form-list, Discharge/BridgeAlphaFormCompound:29-35 using bridge-∘/⊗/-id-is-id/α⇒/⇐-form-list/iso…) use explicit using-lists naming none of the four; only public re-export (line 21) is bridge-∘/bridge-⊗.
    - rec: Delete decode-id-is-id-unit/Var (+ comment 65-67) and α⇒-coh-list/α⇐-coh-list; folds with SoundnessCore-4.
- **SoundnessCore-4 BridgeCoherence import of Discharge.DecodeAttemptLinearP (decode) becomes redundant once decode-id-is-id-* go** — `reexport`, confirmed/high, ~5 LOC, risk low
    - files: src/Categories/APROP/Hypergraph/Soundness/Bridge/BridgeCoherence.agda
    - verify: `open … DecodeAttemptLinearP sig using () renaming (decodeP to decode)` at lines 31-32. grep -P '\bdecode\b' in BridgeCoherence.agda: the renamed token `decode` is used ONLY at the two dead-lemma defs (lines 69, 75); every other hit is a comment (28/30/66/67) or the import itself (32). So once SoundnessCore-3 lands, the import block (28-32) — a Bridge-layer file reaching up into the Discharge layer — is dead.
    - rec: After SoundnessCore-3, delete lines 28-32 (comment + DecodeAttemptLinearP import).
- **SoundnessCore-5 Private ↑ˡ≢↑ʳ disjoint-injection helper duplicated in DecodeProperties and Linearity (and DepIrrefl)** — `hoist`, confirmed/high, ~18 LOC, risk low
    - files: src/Categories/APROP/Hypergraph/Soundness/Decode/DecodeProperties.agda, src/Categories/APROP/Hypergraph/Soundness/Linearity/Linearity.agda, src/Categories/APROP/Hypergraph/Model/Invariant.agda
    - verify: Read both: DecodeProperties:79-86 (`↑ˡ≢↑ʳ : … → ¬(i ↑ˡ nB ≡ nA ↑ʳ j)` + flip `↑ʳ≢↑ˡ`) and Linearity:123-127 (`↑ˡ≢↑ʳ : … → i ↑ˡ nB ≡ nA ↑ʳ j → ⊥`) — same splitAt-↑ˡ/splitAt-↑ʳ `with … | ()` chase; the type difference (¬A vs A→⊥) is definitional. grep confirms a third top-level copy at DepIrrefl:69. Model.Invariant already exports inject+-inj(56)/raise-inj(66)/disj-L-R(78); DecodeProperties already imports Model.Invariant (line 18); Linearity does NOT (would need the new import — proposal notes this). Verified no cycle: Model.Invariant imports only Model.Core/FromAPROP, not the Soundness layer.
    - rec: Hoist ↑ˡ≢↑ʳ (+ ↑ʳ≢↑ˡ flip) into Model.Invariant; import in DecodeProperties+Linearity and delete the two private copies (DepIrrefl optional).
- **SoundnessCore-6 Private tabulate-+ helper duplicated verbatim in Linearity and LinearHComposeP** — `hoist`, confirmed/high, ~6 LOC, risk low
    - files: src/Categories/APROP/Hypergraph/Soundness/Linearity/Linearity.agda, src/Categories/APROP/Hypergraph/Soundness/Discharge/LinearHComposeP.agda
    - verify: Read both: Linearity:154-159 and LinearHComposeP:69-77 — identical type (`tabulate f ≡ tabulate (f∘↑ˡ) ++ tabulate (f∘↑ʳ)`) and body (zero/suc split via `cong (f zero ∷_)` + `Fun.∘`), both `private`. grep tabulate-+ shows it used inside each file (Linearity 225/242; LinearHComposeP 322/338) and nowhere else. LinearHComposeP already imports a batch from Linearity (lines 29-31) and already has `Fun` in scope (uses it in its copy line 77).
    - rec: Make tabulate-+ non-private in Linearity, add to LinearHComposeP's using-list, delete the LinearHComposeP copy.
- **SoundnessCore-7 ExtractPrefix.agda (and FreeSMC/Steps.agda) cite nonexistent module Discharge.APROPMacLaneFromSMC** — `stale-comment`, confirmed/high, ~4 LOC, risk low
    - files: src/Categories/Hypergraph/ExtractPrefix.agda, src/Categories/FreeSMC/Steps.agda
    - verify: `find src spikes -iname '*APROPMacLaneFromSMC*'` returns nothing. grep of the name: only ExtractPrefix.agda:10 and FreeSMC/Steps.agda:62 (both in comments). grep `process-steps-maybe`: only those same two files' comments — the cited correspondence lemma does not exist. The 'shared so they observe one definition' rationale is still TRUE: Decode.Decode:49 and FreeSMC.Steps both `open import Categories.Hypergraph.ExtractPrefix public`, so the proposed rewrite (keep the sharing reason, drop the APROPMacLaneFromSMC clause) is accurate.
    - rec: Update both docstrings to keep the definitional-sharing reason and drop the dead APROPMacLaneFromSMC / process-steps-maybe reference.
- **SoundnessCore-8 UnflattenMonoidal docstring claims §3/box-of bridges consume to-uf-map-++ via Decode.mid', but mid' uses inline subst₂** — `stale-comment`, confirmed/high, ~3 LOC, risk low
    - files: src/Categories/APROP/Hypergraph/Soundness/Base/UnflattenMonoidal.agda, src/Categories/APROP/Hypergraph/Soundness/Decode/Decode.agda
    - verify: §3 banner (UnflattenMonoidal 252-259) and docstring (19-21) state the map-++ laxator naturality is 'the precise transport the per-edge box-of bridges consume (cf. mid' in Decode.agda)'. Read Decode.mid' (lines 118-123): it is `subst₂ HomTerm (cong unflatten (sym (map-++ H.vlab …))) … mid` — inline, NOT a call to to-uf-map-++/from-uf-map-++/to-uf-cong (the tree-wide grep in SoundnessCore-2 shows those names occur only inside UnflattenMonoidal). Claim is false and the helpers are dead.
    - rec: Remove the §3 narration with the dead defs (folds into SoundnessCore-2); drop the cf.-mid' provenance.
- **SoundnessCore-9 UnflattenMonoidal re-exports c-iso-assoc-from-cons that no consumer uses** — `reexport`, confirmed/high, ~1 LOC, risk low
    - files: src/Categories/APROP/Hypergraph/Soundness/Base/UnflattenMonoidal.agda
    - verify: grep c-iso-assoc-from-cons over src+spikes: CIsoAssocFromCons docstring(4) + def(217/227) + the UnflattenMonoidal re-export line 38 — and nowhere else. The two consumers of c-iso-assoc-from get it without -cons: BoxKernel imports CIsoAssocFromCons directly (line 54-55, `using (c-iso-assoc-from)`); Embed gets it via UnflattenMonoidal (using-list line 29 names only c-iso-assoc-from). c-iso-assoc-from-cons stays defined/exported by CIsoAssocFromCons itself, so dropping it from the UnflattenMonoidal re-export is safe.
    - rec: Drop c-iso-assoc-from-cons from the re-export using-list at line 38 (keep c-iso-assoc-from).
- **SoundnessCore-10 Unflatten.agda imports unitorˡ and associator but uses neither** — `reexport`, confirmed/high, ~1 LOC, risk low
    - files: src/Categories/APROP/Hypergraph/Soundness/Base/Unflatten.agda
    - verify: Line 29 `open Monoidal Monoidal-FreeMonoidal using (unitorˡ; unitorʳ; associator)` — a plain (NON-public) open, so no re-export. grep -P whole-word: unitorˡ only at line 29; associator only at line 29; unitorʳ at line 29 and the single real use line 51 (`unflatten-flatten-≈ (Var x) = ≅.sym unitorʳ`). Reducing the open to `using (unitorʳ)` is safe.
    - rec: Reduce line 29 to `using (unitorʳ)`.

### Discharge

- **Discharge-1 Three copies of the `↑ˡ ≢ ↑ʳ` disjointness lemma inside Discharge/** — `hoist`, confirmed/high, ~18 LOC, risk low
    - files: src/Categories/APROP/Hypergraph/Soundness/Discharge/DepIrrefl.agda, src/Categories/APROP/Hypergraph/Soundness/Discharge/FinOrderNoInv.agda, src/Categories/APROP/Hypergraph/Soundness/Discharge/LinearHComposeP.agda
    - verify: Read DepIrrefl:69-75 (↑ˡ≢↑ʳ, generic {S}{T} case-absurd), FinOrderNoInv:107-113 (↑ˡ-↑ʳ-disjoint, identical splitAt-↑ˡ/↑ʳ/case-absurd body), LinearHComposeP:461-470 (same body specialised to G.nV/cn). grep across src/ found 3 more sibling copies (Prune:296 parameterised on unused k:ℕ, DecodeProperties:79, Linearity:123), confirming the same disjointness proof recurs. All use the splitAt-↑ˡ m i k / splitAt-↑ʳ m k j / inj₁≢inj₂ pattern.
    - rec: Hoist one generic ↑ˡ-↑ʳ-disjoint into a shared Fin-util module; import from the three Discharge sites (and ideally the 3 outside).
- **Discharge-2 SigmaBlockHexagon is a generic free-SMC coherence module imported by Categories.FreeSMC / Categories.PermuteCoherence** — `misplaced`, confirmed/high, ~0 LOC, risk medium
    - files: src/Categories/APROP/Hypergraph/Soundness/Discharge/Sub/SigmaBlockHexagon.agda
    - verify: Header (lines 1-30) shows module is parameterised by (d : FreeMonoidalData) ⦃ s≤v : Symm ≤ … ⦄, NOT an APROPSignature; comment says 'Everything below is derived from the FreeMonoidal (symmetric) axioms alone'. Import list contains only Categories.FreeMonoidal, Categories.Category, Categories.PermuteCoherence.Faithfulness, Categories.Coherence.Monoidal + stdlib — zero APROP-specific imports (only 'APROP' occurrence is its own module path). grep import shows upward importers OUTSIDE the APROP subtree: FreeSMC.SigmaBlockTensor:21, FreeSMC.BraidBlock:41, PermuteCoherence.FaithfulnessInductive:67 (plus APROP-internal Embed/Braid/BlockNFBraid). Faithfulness does not import SigmaBlockHexagon, so relocating to FreeSMC/PermuteCoherence introduces no cycle.
    - rec: Relocate to Categories.FreeSMC (or Categories.PermuteCoherence) and update the ~6 importers; removes the library→application upward dependency.
- **Discharge-3 count-mono-cons re-defined locally in StackUnique despite importing CountCombinatorics** — `duplicate`, confirmed/high, ~5 LOC, risk low
    - files: src/Categories/APROP/Hypergraph/Soundness/Discharge/Sub/StackUnique.agda, src/Categories/APROP/Hypergraph/Soundness/Discharge/Sub/CountCombinatorics.agda
    - verify: CountCombinatorics:214-218 defines count-mono-cons (∀{n}(v x)(xs)→count v xs ≤ⁿ count v (x∷xs); body: with v≟x / yes→Nat.n≤1+n / no→Nat.≤-refl). StackUnique:125-129 re-defines it as a local indented binding with byte-identical body (used internally at StackUnique:140). StackUnique:74 already imports CountCombinatorics sig using (count-cons-yes; count-cons-no; ↭⇒count; ∈→count-pos) but does NOT include count-mono-cons. (LinearHComposeP imports it from a count module too.)
    - rec: Delete StackUnique's local copy (125-129) and add count-mono-cons to the existing CountCombinatorics using-list.
- **Discharge-4 Four unused subst₂/⊗ transport helpers in HomTermTransport** — `dead-code`, confirmed/high, ~24 LOC, risk low
    - files: src/Categories/APROP/Hypergraph/Soundness/Discharge/Sub/HomTermTransport.agda
    - verify: grep across src/+spikes/: ⊗id-∘∘ → only HomTermTransport:128/132 (sig+def); pvl-refl → only :158/161; subst₂-cod-trans → only :163/170; subst₂-dom-trans → only :172/179. Zero call sites for all four. Cross-checked ⊗id-∘ (the genuinely-live one): SeparableStack:74 imports it and uses it at :596, plus internal use by ⊗id-∘∘:133 — but ⊗id-∘∘ itself has no users. (SolverSigma/Leg3Recomp have their own local ⊗id-∘, unrelated.)
    - rec: Delete ⊗id-∘∘, pvl-refl, subst₂-cod-trans, subst₂-dom-trans from HomTermTransport.
- **Discharge-5 Dead public wrapper bridge-α⇒-form-⊗-⊗ in BridgeAlphaFormCompound** — `dead-code`, confirmed/high, ~10 LOC, risk low
    - files: src/Categories/APROP/Hypergraph/Soundness/Discharge/BridgeAlphaFormCompound.agda
    - verify: grep bridge-α⇒-form-⊗-⊗ across src/+spikes/: only BridgeAlphaFormCompound:687/692 (its own sig+def) plus two stale comment mentions in BridgeCoherence:539,601. Importers of BridgeAlphaFormCompound = BridgeCoherence (comment-only), CIsoAssocFromCons (comment-only at :27), Boundary. Boundary imports module as BAFC and uses only BAFC.Worker.work (Boundary:328); grep BAFC. shows only Worker. So the 'Public entry point' wrapper is never called.
    - rec: Delete the dead wrapper bridge-α⇒-form-⊗-⊗ (687-693) and its banner; callers already use Worker.work directly.
- **Discharge-6 Dead aliases: objUIP-UIP, lemmaA/≺-resp-≅ᴴ, box-of-cong** — `dead-code`, confirmed/high, ~18 LOC, risk low
    - files: src/Categories/APROP/Hypergraph/Soundness/Discharge/ObjUIP.agda, src/Categories/APROP/Hypergraph/Soundness/Discharge/EdgeDependency.agda, src/Categories/APROP/Hypergraph/Soundness/Discharge/EdgeStepRelation.agda
    - verify: objUIP-UIP: grep → only ObjUIP:51/52 (=objUIP); consumers use objUIP′. lemmaA: grep → only EdgeDependency:87/88 + its alias ref at :91; ≺-resp-≅ᴴ: grep → only EdgeDependency:90/91 (=lemmaA). The raw directions ≺⇒ψ≺/ψ≺⇒≺ are the live ones (NoInvTau:21/60, IsoInvarianceWiring:31/121). box-of-cong: grep → only EdgeStepRelation:54/64 (sig+def), zero external; SeparableStack imports box-of/fire-mid/EdgeStepR but not box-of-cong.
    - rec: Delete objUIP-UIP, lemmaA + its alias ≺-resp-≅ᴴ, and box-of-cong.
- **Discharge-7 just≢nothing re-defined privately in StackEquiv and twice in DecodeCompose despite a shared copy in HomTermTransport** — `duplicate`, confirmed/high, ~6 LOC, risk low
    - files: src/Categories/APROP/Hypergraph/Soundness/Discharge/Sub/HomTermTransport.agda
    - verify: HomTermTransport:62-63 exports just≢nothing : ∀{a}{A:Set a}{x:A}→just x≡nothing→⊥ (=()). Identical local where-bound copies: StackEquiv:88-89 (used at 468/470), DecodeCompose:611-612 and 617-618 (used at 609/614). SeparableStack:74 already imports it from HomTermTransport (used at 409/417/533/536). All four bodies are byte-identical 2-liners. Finding correctly notes touching Strict/ requires coordination; proof is trivial.
    - rec: Import just≢nothing from HomTermTransport in StackEquiv and DecodeCompose; drop the three local re-declarations.
- **Discharge-8 map⁺-↭-reflexive in PermutationTransport duplicates Categories.PermuteCoherence.FinBijSubst** — `dead-code`, needs-care/high, ~4 LOC, risk low
    - files: src/Categories/APROP/Hypergraph/Soundness/Discharge/Sub/PermutationTransport.agda
    - verify: PermutationTransport:133-136 map⁺-↭-reflexive f refl=refl vs FinBijSubst:122-124 map⁺-↭-reflexive h refl=refl — identical bodies/statement (var f vs h, FinBijSubst uses module-level implicit A/C levels). BUT it is NOT dead: grep shows it is used at PermutationTransport:230. The 'kind:dead-code' label is inaccurate; it is a genuine duplicate that is in use. Critically, PermutationTransport has ZERO existing imports of Categories.PermuteCoherence (grep PermuteCoherence in the file = empty), so importing from FinBijSubst would ADD a new APROP→PermuteCoherence dependency edge for 4 LOC. FinBijSubst imports no APROP, so no cycle, but the tradeoff is real — finding itself flags it optional/for-human-judgement.
    - rec: Leave as-is unless the new APROP→PermuteCoherence edge is acceptable; it is a used duplicate, not dead code.
- **Discharge-9 subst₂-resp-≈Term general form (HomTermTransport) subsumes the List-X-specialised copy in BridgeCoherence** — `duplicate`, needs-care/medium, ~7 LOC, risk medium
    - files: src/Categories/APROP/Hypergraph/Soundness/Discharge/Sub/HomTermTransport.agda, src/Categories/APROP/Hypergraph/Soundness/Bridge/BridgeCoherence.agda
    - verify: HomTermTransport:102-105 subst₂-resp-≈Term : ∀{A A' B B'}(p:A≡A')(q:B≡B'){u v:HomTerm A B}→u≈Term v→… (general ObjTerm endpoints; body refl refl u≈v=u≈v). BridgeCoherence:146-152 same name specialised to List X with cong unflatten pre-applied (refl refl f≈g=f≈g). The general form is a strict generalisation — proven by BoxKernel:954-955 using it with cong unflatten _ applied. BUT BridgeCoherence does NOT import HomTermTransport (only comment at :18), so adopting it adds an import edge and every BridgeCoherence call site would need cong unflatten threaded through. Two same-named lemmas in two scopes is confusing but the substitution is non-trivial.
    - rec: Optionally drop the BridgeCoherence specialisation and call the general HomTermTransport one with cong unflatten; verify index shapes at each call site first.
- **Discharge-10 Mirror permute-slide lemmas (++⁺ˡ vs ++⁺ʳ) split across FireMidEquivariant / BlockNFBraid with shared body already noted** — `simplify`, needs-care/medium, ~0 LOC, risk medium
    - files: src/Categories/APROP/Hypergraph/Soundness/Discharge/Sub/FireMidEquivariant.agda, src/Categories/APROP/Hypergraph/Soundness/Discharge/Sub/BlockNFBraid.agda, src/Categories/APROP/Hypergraph/Soundness/Discharge/Sub/PermutationTransport.agda
    - verify: FireMidEquivariant:122 permute-++⁺ˡ-slide (left slide; empty case uses solveMor!/FinSetup) and BlockNFBraid:636 frame-ext (++⁺ʳ mirror; uses pvv-++⁺ʳ + frame-transport begin-block) are the two directional halves. PermutationTransport:326 explicitly comments frame-transport 'is the shared body of frame-ext/… (and the pvv-++⁺ˡ-slide left slide)', confirming the common subst₂ core is ALREADY factored. The two slide statements genuinely differ in direction and proof style; estLOC 0 = no concrete saving, finding is a flag-for-human-judgement.
    - rec: Optional: co-locate the left/right slide statements atop the existing frame-transport core; low value, the directions are genuinely distinct.

### Strict

- **Strict-1 bridge⁻¹ / bridge-cancel in capstone Soundness.agda are dead (duplicated, unused copy)** — `dead-code`, confirmed/high, ~46 LOC, risk low
    - files: /Users/andre/IOHK/categorical-crypto/.claude/worktrees/string-diagram-solver/src/Categories/APROP/Hypergraph/Soundness.agda
    - verify: Read the full 85-line capstone Soundness.agda: the only theorem `soundness` (line 80-84) is `SA.soundness-assembled TKF.decodePˢ-⊗-concrete`; it never references bridge⁻¹/bridge-cancel. `grep -rn 'bridge-cancel|bridge⁻¹' src spikes` shows uses only at the capstone definition sites (lines 46-74) and in Strict/SoundnessParam.agda (def lines 57-65 + REAL uses at 115-118) plus a comment in Boundary.agda — confirming the live copy is SoundnessParam's, invoked by soundness-strict. So the capstone copy has zero users. The dead block's imports (flatten 25, unflatten/unflatten-flatten-≈ 27-28, bridge 29-30, _≅_ 36, FM/HomReasoning 38-41) become unused once removed. CAVEAT: the proposed action's import-keep list omits `Model.Translation`(⟪_⟫), which IS still needed by the surviving `soundness` type signature (line 82); keep that import too.
    - rec: Delete bridge⁻¹+bridge-cancel (lines 44-74) and the now-unused imports, but KEEP Model.Translation (⟪_⟫) alongside Model.Iso, SA, TKF, and the APROP open.
- **Strict-2 pvv-relabelˢ (+3 private helpers) verbatim-duplicated: TensorPVVRelabel vs DecodeComposeAssembly — incomplete hoist** — `duplicate`, confirmed/high, ~95 LOC, risk medium
    - files: /Users/andre/IOHK/categorical-crypto/.claude/worktrees/string-diagram-solver/src/Categories/APROP/Hypergraph/Soundness/Strict/Tensor/TensorPVVRelabel.agda, /Users/andre/IOHK/categorical-crypto/.claude/worktrees/string-diagram-solver/src/Categories/APROP/Hypergraph/Soundness/Strict/Decode/DecodeComposeAssembly.agda
    - verify: Read both: TensorPVVRelabel defines pvv-relabelˢ (76-149)+permˢ-K-X(57)/eval-subst₂-↭(61)/permuteˣ-subst₂(69); DecodeComposeAssembly redefines identical pvv-relabelˢ(331-404)+same 3 helpers(312-329). Bodies byte-identical except DC.mp vs opened mp. `grep TensorPVVRelabel DecodeComposeAssembly.agda` => exit 1 (NOT imported). `grep -rln TensorPVVRelabel` => only TensorBraid + the file itself. Call sites pvv-relabelˢ at 560,626 use the inline copy (plain 7-arg applications, verified line 560: `pvv-relabelˢ injL vlC G.vlab vlab-injL perm-f Pdom Pcod`). Hoist feasibility verified: DecodeComposeAssembly's pvv-relabelˢ lives inside `module ComposeShape{A B C₀}(g)(f)` (line 87) but does NOT use those params; mp/permuteˢ-X/XPerm arrive via StackEquiv `... public`(line55) which re-exports DecodeCompose `public`(StackEquiv line46) — the SAME defs TensorPVVRelabel imports directly as DC. So PVV.pvv-relabelˢ is drop-in. Medium risk only from confirming arg shapes at the 2 sites (they match).
    - rec: Import TensorPVVRelabel as PVV into DecodeComposeAssembly, delete inline pvv-relabelˢ + 3 helpers (309-404), repoint sites 560/626 to PVV.pvv-relabelˢ.
- **Strict-3 Unused co-located import `IsoInvarianceConcrete as IC` in DecodePRespIso** — `reexport`, confirmed/high, ~1 LOC, risk low
    - files: /Users/andre/IOHK/categorical-crypto/.claude/worktrees/string-diagram-solver/src/Categories/APROP/Hypergraph/Soundness/Strict/Decode/DecodePRespIso.agda
    - verify: `grep -n 'IsoInvarianceConcrete|\bIC\b|IC\.' DecodePRespIso.agda` returns exactly two lines: line 19 (a prose comment naming the bare module) and line 60 (`import ... as IC`). No `IC.`-qualified use anywhere. It is `import ... as` (not open, not public), so removing it changes no scope.
    - rec: Delete line 60.
- **Strict-4 Unused stdlib import `Permutation.Propositional.Properties as PermProp` in Separability** — `reexport`, confirmed/high, ~1 LOC, risk low
    - files: /Users/andre/IOHK/categorical-crypto/.claude/worktrees/string-diagram-solver/src/Categories/APROP/Hypergraph/Soundness/Strict/Separability.agda
    - verify: `grep -n PermProp Separability.agda` => single match at line 69 (the import). Alias never used, not opened, not public.
    - rec: Delete line 69.
- **Strict-5 nothing≢just re-derived privately in sibling Interchange files** — `hoist`, confirmed/high, ~2 LOC, risk low
    - files: /Users/andre/IOHK/categorical-crypto/.claude/worktrees/string-diagram-solver/src/Categories/APROP/Hypergraph/Soundness/Strict/Interchange/SwapCore.agda, /Users/andre/IOHK/categorical-crypto/.claude/worktrees/string-diagram-solver/src/Categories/APROP/Hypergraph/Soundness/Strict/Interchange/SwapCoreRun.agda
    - verify: Read SwapCore 82-84: `private nothing≢just : ... → ⊥ ; nothing≢just ()`. SwapCoreRun 66-67 identical, also under `private`, with ~8 real uses (lines 173-216). SwapCoreRun imports SwapCore (line 44) but SwapCore's copy is private so invisible — hence the redundant re-derivation. Hoist (un-private SwapCore's, drop SwapCoreRun's) is sound. Trivial 2-LOC helper.
    - rec: Make SwapCore.nothing≢just non-private and delete the SwapCoreRun copy.
- **Strict-6 PartI header says 'two in-progress shapes' but only decodePˢ-⊗ remains a parameter** — `stale-comment`, confirmed/high, ~4 LOC, risk low
    - files: /Users/andre/IOHK/categorical-crypto/.claude/worktrees/string-diagram-solver/src/Categories/APROP/Hypergraph/Soundness/Strict/PartI.agda
    - verify: Read PartI 1-75: header lines 11-14 'Two shapes — Agen ... and ⊗ ... are taken as module parameters'; line 62 'parameterised over the two in-progress shapes'. But the actual `module _`(line 64) has exactly ONE parameter decodePˢ-⊗ (65-67), and decodePˢ-Agen is concrete via `DGen.decodePˢ-Agen`(line 72). Comment is stale.
    - rec: Reword header+line-62 to one parameter (decodePˢ-⊗); note Agen now concrete via DecodeGen.
- **Strict-7 Capstone Strict/Soundness.agda header narrates a 'SINGLE remaining residual pending' that is now discharged** — `stale-comment`, confirmed/high, ~6 LOC, risk low
    - files: /Users/andre/IOHK/categorical-crypto/.claude/worktrees/string-diagram-solver/src/Categories/APROP/Hypergraph/Soundness/Strict/Soundness.agda
    - verify: Read Strict/Soundness.agda full: header 4-13 calls decodePˢ-⊗ 'the SINGLE remaining residual ... pending the K-block box-braid KBlockσ' and frames 're-pointing' as future ('at which point Soundness.soundness is re-pointed at it'). Per Strict-1 verification, the capstone Hypergraph/Soundness.agda:84 ALREADY calls `SA.soundness-assembled TKF.decodePˢ-⊗-concrete`, and TKF.decodePˢ-⊗-concrete is unconditional (ZERO postulates, verified in Strict-10). Module stays correctly parametric; only the prose is stale.
    - rec: Note decodePˢ-⊗ is now supplied unconditionally by TensorKBlockFinal.decodePˢ-⊗-concrete and the capstone is already re-pointed.
- **Strict-8 PermSupport claims permˢ-K is discharged via Strict.Embed; actual route is PermDischarge+Braid** — `stale-comment`, confirmed/high, ~3 LOC, risk low
    - files: /Users/andre/IOHK/categorical-crypto/.claude/worktrees/string-diagram-solver/src/Categories/APROP/Hypergraph/Soundness/Strict/Perm/PermSupport.agda
    - verify: Read PermSupport 1-25: lines 11-13 say permˢ-K is 'discharged ... by transporting the non-strict K kernel through the strictification boundary Strict.Embed'. `grep Embed PermSupport.agda` => only line 13 (the comment); no import of Embed exists there. Read PermK.agda 1-46: permˢ-K is discharged via `PD.Discharge ... D.Main (BR.Generic.strict-braid FlatGen)` (PermDischarge + Braid), lines 40-45; `grep Embed PermK.agda PermDischarge.agda` => none. Strict.Embed is imported only by FreeStrictSMC, Embed itself, and Boundary (for embF/embF-resp-≈ˢ, line 50). So the documented K-discharge route is wrong/obsolete.
    - rec: State permˢ-K is discharged axiom-free in Strict.Perm.PermK via PermDischarge + Braid.Generic.strict-braid (not Strict.Embed).
- **Strict-9 SwapCore header describes a pre-split combined architecture (build/run-interchange₀ˢ live elsewhere now)** — `stale-comment`, confirmed/high, ~8 LOC, risk low
    - files: /Users/andre/IOHK/categorical-crypto/.claude/worktrees/string-diagram-solver/src/Categories/APROP/Hypergraph/Soundness/Strict/Interchange/SwapCore.agda
    - verify: Read SwapCore 1-45: title line 4 'The STRICT EMPTY-TAIL two-edge interchange core run-interchange₀ˢ'; ARCHITECTURE line 30 lists 'build + run-interchange₀ˢ — the four-way firing split'. But `grep -rn run-interchange₀ˢ` shows it is DEFINED in SwapCoreRun.agda:256 (re-exported by FireMid.agda:1293 `open RunInterchangeˢ using (run-interchange₀ˢ; build) public`); `build` clauses also live in SwapCoreRun (170-266). SwapCore's actual top-level def is `data EdgeStepRˢ`(line 121) + algebra bricks. Header reflects the pre-split module.
    - rec: Retitle SwapCore to its real role (strict EdgeStepRˢ algebra bricks) and move build/run-interchange₀ˢ bullets to SwapCoreRun/FireMid.
- **Strict-10 TensorReconcile labels braidˢ a 'REMAINING RESIDUAL NOT discharged'; it is discharged by TensorBraid** — `stale-comment`, confirmed/high, ~6 LOC, risk low
    - files: /Users/andre/IOHK/categorical-crypto/.claude/worktrees/string-diagram-solver/src/Categories/APROP/Hypergraph/Soundness/Strict/Tensor/TensorReconcile.agda
    - verify: Read TensorReconcile 30-42: 'REMAINING RESIDUAL (precisely typed, NOT discharged here): braidˢ'. braidˢ is genuinely a parameter of reconcile-from-braid (line 131) and decodePˢ-⊗-from-braid (line 149). But TensorBraid.agda:406 supplies it: `decodePˢ-⊗-cond kb = let cand,braidˢ = braidˢ-from-kblock kb in TR.Reconcile.decodePˢ-⊗-from-braid permˢ-K f g cand braidˢ`. TensorKBlockFinal.agda (268-285) feeds KBlockσ via Rec.KBlockσ-from-factorization to produce decodePˢ-⊗-concrete with 'ZERO postulates' (header line 24); `grep '^postulate|^  postulate'` across TensorKBlockFinal/TensorBraid/TensorReconcile => none. So braidˢ is discharged downstream and the ⊗-shape is unconditional; the 'NOT discharged' framing is stale.
    - rec: Reword the residual section: braidˢ is the parameter discharged downstream by Strict.Tensor.TensorBraid (via KBlockσ), making the ⊗-shape unconditional.

### PermuteCoherence

- **PermuteCoherence-1 FaithfulnessK: only σ-block-self-inverse-direct is consumed; ~210 LOC of permute-inverse / residual-equivalence machinery is dead** — `dead-code`, confirmed/high, ~210 LOC, risk low
    - files: src/Categories/PermuteCoherence/FaithfulnessK.agda
    - verify: `grep -rn FaithfulnessK src/ spikes/` → exactly one importer: FaithfulnessInductive.agda:64. Read of FaithfulnessInductive.agda:64-65 shows the import line is `using (σ-block-self-inverse-direct)` ONLY (line 68's σ-block-natural₃ comes from SigmaBlockHexagon, a different module — confirmed by reading lines 62-68). Word-boundary grep of every other FaithfulnessK export (permute-inverse-left/right, ↭-sym-involutive, SwapBlockInverseResidual, constructive-swap-block-inverse, permute-inverse-left!/right!, PermuteRespSymResidual, constructive-trans-self-loop, constructive-permute-resp-sym, inv-from-self-loop) returns zero hits outside the file. The lone ↭-sym-involutive hit at StackEquiv.agda:482 is `PermProp.↭-sym-involutive` (read of StackEquiv:70 confirms PermProp = stdlib Data.List...Permutation.Propositional.Properties; StackEquiv has NO FaithfulnessK import). The survivor (lines 175-197) plus its private helpers σ-block-involutive/σ-block-natural₃ use only α⇐-comm/α-comm/σ∘σ≈id/assoc-family — none reference permute/unflatten/TransSelfLoopResidual, so the deletion is self-contained.
    - rec: Delete the dead §1-4/§6-10 blocks and FinBij/Eval/EvalSoundness/TransSelfLoopResidual imports; keep σ-block-self-inverse-direct + its two private helpers; rewrite header.
- **PermuteCoherence-2 FaithfulnessInductive.faithfulness (FaithfulnessResidual value) and its sole helper permute-resp-≅↭ⁱ are unused** — `dead-code`, confirmed/high, ~24 LOC, risk low
    - files: src/Categories/PermuteCoherence/FaithfulnessInductive.agda
    - verify: `grep -rn FaithfulnessInductive` → only importer is PermDischarge.agda:66, with `using (_≅↭ⁱ_; complete)` (read confirms) — does NOT bring in `faithfulness`. The PermSupport.agda:8 hit is a comment. `grep -rnw faithfulness src/ spikes/` shows the FaithfulnessInductive `faithfulness` only at its own def (658-659). `grep -rn permute-resp-≅↭ⁱ` shows it only in its own definition (237-252) and inside `faithfulness` at line 660; PermDischarge:190 uses its own re-implemented `permuteˢ-resp-≅↭ⁱ ∘ complete` instead. So faithfulness has zero external users and permute-resp-≅↭ⁱ's only user is faithfulness.
    - rec: Delete faithfulness (658-660), then permute-resp-≅↭ⁱ (237-252); trim header narration.
- **PermuteCoherence-3 Faithfulness.faithfulness alias (rename of permute-resp-≅↭) is unused** — `dead-code`, confirmed/high, ~5 LOC, risk low
    - files: src/Categories/PermuteCoherence/Faithfulness.agda
    - verify: Read Faithfulness.agda:151-158: `faithfulness = permute-resp-≅↭` is a trivial alias inside `module _ (R : FaithfulnessResidual)`. `grep -rnw faithfulness src/ spikes/` finds the identifier (excluding the FaithfulnessInductive one and comments) only at Faithfulness.agda:154,158. Several importers open Faithfulness without a using-list (FireMidEquivariant:54, HomTermTransport:38, BlockNFBraid:34, SigmaBlockCommRaw:22) or re-export public (Unflatten:36), so the alias COULD be in scope unqualified — yet no file references it. Steps.agda:30-31 opens with `using (unflatten; unflatten-++-≅; permute) public`, which omits faithfulness. wide⇒narrow / permute-self-loop-id(-wide) / the residual records remain live.
    - rec: Delete the faithfulness alias (154-158) and its docstring bullet (line 18).
- **PermuteCoherence-4 FaithfulnessK imports `unflatten` (and, post-cleanup, `permute`) it never uses** — `reexport`, confirmed/high, ~2 LOC, risk low
    - files: src/Categories/PermuteCoherence/FaithfulnessK.agda
    - verify: `grep -nw unflatten FaithfulnessK.agda` → single hit, the using-list at line 29 (already dead today). `grep -nw permute FaithfulnessK.agda` → all code uses are inside the dead §2-10 (lines 52-318); the surviving σ-block-self-inverse-direct (175-197) uses no `permute`. `grep -nw α⇐-comm FaithfulnessK.agda` → live use at line 150 inside private σ-block-natural₃ (feeds the survivor). So trimming line 29 to `using (α⇐-comm)` is correct; `unflatten` removable now, `permute` falls out with PermuteCoherence-1.
    - rec: Trim line 29 to `using (α⇐-comm)`; drop unflatten now, permute with PermuteCoherence-1.
- **PermuteCoherence-5 Canonical.bubble-to-front defines the same `suc-injective` local helper twice** — `duplicate`, confirmed/high, ~6 LOC, risk low
    - files: src/Categories/PermuteCoherence/Canonical.agda
    - verify: Read Canonical.agda:59-77: within the single function `bubble-to-front`, identical helper `suc-injective : ∀ {a b} → suc a ≡ suc b → a ≡ b; suc-injective refl = refl` appears in two distinct clause-local where blocks (lines 66-67 for the `zero` clause, 72-73 for the `suc k` clause). Imports (lines 23-26) bring in Data.Nat.Base (zero/suc) but NOT Data.Nat.Properties, so stdlib suc-injective is not currently in scope. Both copies are byte-identical and over ℕ. Proposed fix (import stdlib suc-injective or hoist one copy) is valid and low-risk.
    - rec: Replace both ℕ-level copies with Data.Nat.Properties.suc-injective import (or hoist one).
- **PermuteCoherence-6 Provenance narration about a removed `insert` postulate in InsertProof / Word** — `stale-comment`, confirmed/high, ~4 LOC, risk low
    - files: src/Categories/PermuteCoherence/InsertProof.agda, src/Categories/PermuteCoherence/Word.agda
    - verify: `grep -rn postulate src/Categories/PermuteCoherence/` returns exactly ONE hit — the word inside the comment InsertProof.agda:6 ('drop the `insert` postulate'); no actual postulate declaration exists in the subtree. Read InsertProof:1-8 and Word:382-386 confirm the comments narrate a no-longer-present `insert` postulate. Word:457-458 (separately) only says straightenW needs the Insertion Lemma — that part is accurate, not stale. The described relationship (straightenW depends on insert-thm, hence downstream of Word) is real; only the wording is historical. Purely cosmetic.
    - rec: Reword InsertProof:5-6 and Word:386 to describe the current insert-thm dependency without the removed postulate.
- **PermuteCoherence-7 BringToFrontAdjL / BringToFrontAdjR are mirror-image proofs of the two adjacency cases** — `simplify`, needs-care/high, ~60 LOC, risk high
    - files: src/Categories/PermuteCoherence/BringToFrontAdjL.agda, src/Categories/PermuteCoherence/BringToFrontAdjR.agda
    - verify: `wc -l` → 137 vs 142 LOC. `diff` of import blocks (lines 8-35) → exit 0 (byte-identical). Full `diff` of bodies shows systematic but NON-mechanical mirror: AdjL `(adj : Adj i j)` with toℕj≡=Adj→suc adj and inequality reasoning via swapℕ-fix-val + ii≢j/ii≢sj; AdjR `(adj : Adj j i)` with toℕi≡ and value-tracking via swapℕ-sk/swapℕ-k. `grep` → each imported by exactly one file (BringToFrontCases.agda:30-31). The arithmetic differs in a load-bearing way (not pure textual mirror), so a parameterised merge is non-trivial and could risk these Fin-arithmetic proofs / typecheck cost. Finding's own recommendation already says FLAG-for-human / do NOT attempt blindly, which matches needs-care.
    - rec: Leave as-is unless a human confirms a safe orientation-parameterised merge; do not attempt blindly.

### Coherence

- **Coherence-1 Symmetric.agda interface comment omits the rewriteDeepProv* tool family that the showcase actually uses** — `stale-comment`, confirmed/high, ~6 LOC, risk low
    - files: /Users/andre/IOHK/categorical-crypto/.claude/worktrees/string-diagram-solver/src/Categories/Coherence/Symmetric.agda
    - verify: `rg -n rewriteDeepProv src/Categories/Coherence/Symmetric.agda` -> no matches (exit 1). The module-doc palette (lines 28-39) lists `rewriteDeep(ₙ)!`, `rewriteDeepTo!`, `normalize(To)!` but never `rewriteDeepProv*`. Confirmed `rewriteDeepProvₙ!`/`rewriteDeepProv!`/`rewriteDeepProvTo!` are defined at indentation level 2 INSIDE `module Solver` (Frontend.agda:110, defs at 318/331/351); Setup `open Solver C ... public` (Symmetric.agda:126) re-exports them, so they ARE in Setup scope for clients. Frobenius.agda drives its derivation with `rewriteDeepProvTo!` (lines 120,123,126,129,132).
    - rec: Add a `rewriteDeepProv(ₙ/To)!` bullet to the Symmetric.agda palette comment alongside `rewriteDeepTo!`, noting they are the carve-provenance-guided gate-#1 variants the Frobenius showcase uses.
- **Coherence-2 Test.agda palette and Frobenius.agda header narrate rewriteDeep! but the code uses rewriteDeepProvTo!** — `stale-comment`, confirmed/high, ~8 LOC, risk low
    - files: /Users/andre/IOHK/categorical-crypto/.claude/worktrees/string-diagram-solver/src/Categories/Coherence/Symmetric/Test.agda, /Users/andre/IOHK/categorical-crypto/.claude/worktrees/string-diagram-solver/src/Categories/Coherence/Symmetric/Test/Frobenius.agda
    - verify: Test.agda:37-41 lists `rewriteDeepTo!` pointing at `→ Test.Deep, Test.Frobenius`; showcase note (49-51) says Frobenius derives by `chains of deep rewrites`; no `rewriteDeepProv*` anywhere in Test.agda. Frobenius.agda:16 header: `transcribed as a chain of \`rewriteDeep!\` steps`. `rg rewriteDeepTo! src/.../Test/` -> only Deep.agda:111(comment),118; NOT Frobenius. `rg rewriteDeepProv src/.../Test/` -> only Frobenius.agda:118(comment),120,123,126,129,132. So the showcase uses `rewriteDeepProvTo!` exclusively and the `Test.Frobenius` cross-reference on the `rewriteDeepTo!` bullet is itself drifted.
    - rec: Update Frobenius.agda:16 and Test.agda:37-51 to name `rewriteDeepProvTo!` for the Frobenius steps, retarget the `rewriteDeepTo!` pointer to `Test.Deep` only, and add a `rewriteDeepProv*` palette entry.
- **Coherence-3 Wiring re-exports focFrame with zero users anywhere** — `reexport`, confirmed/high, ~1 LOC, risk low
    - files: /Users/andre/IOHK/categorical-crypto/.claude/worktrees/string-diagram-solver/src/Categories/Coherence/Symmetric.agda
    - verify: `rg -n \bfocFrame\b src spikes` shows: Frontend.agda:71/73 (def) + 224(comment)/237/238/241/242/251/252 (internal uses by rewriteAuto(ₙ)! within the SAME defining module); Symmetric.agda:92 (the re-export); spikes/Leg3Recomp.agda:68,598 (doc comments only). `rg -n \bfocFrame\b src --glob '!.../Frontend.agda'` -> ONLY Symmetric.agda:92. No Test module or any client consumes the re-export. Sibling `deepFrame` on the same `using`-line IS consumed (Test/Deep.agda:113, spikes/FrobProbe.agda:130/133, plus Frontend). Wiring is a deliberately-public interface, so this is surface trimming, not strict dead code.
    - rec: Drop `focFrame` from the Wiring re-export `using`-list at Symmetric.agda:92 (keep `deepFrame`), unless an out-of-repo client relies on it.
- **Coherence-4 Single-atom test scaffolding duplicated across four Test configurations** — `hoist`, confirmed/low, ~12 LOC, risk low
    - files: /Users/andre/IOHK/categorical-crypto/.claude/worktrees/string-diagram-solver/src/Categories/Coherence/Symmetric/Test/Frobenius.agda, /Users/andre/IOHK/categorical-crypto/.claude/worktrees/string-diagram-solver/src/Categories/Coherence/Symmetric/Test/DeepArity.agda, /Users/andre/IOHK/categorical-crypto/.claude/worktrees/string-diagram-solver/src/Categories/Coherence/Symmetric/Test/Drivers.agda, /Users/andre/IOHK/categorical-crypto/.claude/worktrees/string-diagram-solver/src/Categories/Coherence/Symmetric/Test/Rewrite.agda
    - verify: `rg -n 'FreeMonoidalHelper Symm \(Fin 1\)' src/.../Test/` -> exactly 4 hits: Frobenius:57, DeepArity:33, Rewrite:52, Drivers:40 (matches finding). All four share the identical `open FreeMonoidalHelper Symm (Fin 1) using (ObjTerm; Var; _⊗₀_) renaming (unit to unitᵗ)`, an atom `a = Var zero`, and `⟦ _ ⟧ᵖ₀ = A`. Atoms3 precedent is real: Coherence.agda:45 `module Atoms3 (A₀ A₁ A₂ : C.Obj)` exporting ObjTerm/atoms/⟦_⟧ᵖ₀, opened by Cycle3/Braiding/Crossings (66,105,174). CAVEATS: Rewrite.agda names the atom `a₀` not `a` (rename needed on import); Atoms3 does NOT export `_⊗₀_` (opened separately at Coherence.agda:175), so an Atoms1 mirror is not purely mechanical; each block is only ~3-4 lines. Finding's own 'low value' caveat is apt. No OOM risk (test scaffolding, no type-level blowup).
    - rec: Optional: add a parameterized `module Atoms1 (A : C.Obj)` (in a small shared Test helper) mirroring Atoms3 and open it in the four single-atom configs; marginal value, watch the `a`/`a₀` and `_⊗₀_` naming differences.


---

## Execution status (2026-06-17)

**Phase 1 — per-subtree intra-file sweep (committed `631ad9a`, full `--safe` gate green).**
All confirmed low-risk items applied across the 7 subtrees (33 of 34; only rank 32 skipped —
its co-bundling precondition was unmet, exactly as the finding flagged). Net −318 LOC over 43 files.

**Phase 2 — cross-subtree consolidations.** Applied:
- **rank 5** — deleted the dead `bridge⁻¹`/`bridge-cancel` block + orphaned imports from the capstone
  `Soundness.agda` (kept `Model.Translation` ⟪_⟫ and `Model.Iso` ≅ᴴ, which the surviving theorem needs).
- **rank 19** — hoisted `tabulate-+` (un-privated in `Linearity`, added to `LinearHComposeP`'s existing
  `using`-list, deleted the local copy). No new import edge, no name clash.
- **rank 37** — relocated `SigmaBlockHexagon` (generic free-SMC coherence) out of the APROP application
  layer to `Categories.FreeSMC.SigmaBlockHexagon`; 7 importers repointed; no import cycle.

**Phase 2 — Fin-disjointness consolidation cluster (ranks 33/34/35) — DONE in a later focused pass:**
- **rank 33** — added a single `↑ˡ≢↑ʳ` to `Model.Invariant`; repointed the 5 Soundness/Discharge copies
  (DecodeProperties/Linearity/DepIrrefl delete-and-import; FinOrderNoInv/LinearHComposeP via thin aliases).
- **rank 34** — `Invariant.inject+-inj`/`raise-inj` are now thin wrappers over stdlib `↑ˡ-injective`/`↑ʳ-injective`
  (signatures kept, so the ~6 call sites are untouched).
- **rank 35** — `Prune`'s `↑ˡ-inj`/`↑ʳ-inj` wrapped over the same stdlib lemmas. Its `↑ˡ-↑ʳ-disjoint` stays
  local (Util-layer cannot import the Model-layer `Invariant` without inverting layering; no stdlib equivalent).
- rank 20 stays skipped (counterproductive heavy import). Full `--safe` gate all rc=0.

**Earlier deferral notes (kept for the record):**
- **rank 20** (Maybe-discrimination dedup) — *counterproductive.* `Strict/Decode/DecodeCompose:297`
  documents that its local `just≢nothing` is **deliberately** re-proved as a 1-liner *to avoid a heavy
  `HomTermTransport` import*. None of StackEquiv/DecodeCompose/SwapCore/SwapCoreRun import HomTermTransport;
  the "dedup" would add a heavy cross-module import to save a 2-line absurd-pattern lemma. Skipped.
- **rank 33** (`↑ˡ≢↑ʳ` copied 5–6×) — *fragile multi-site.* 4 of the 5 consumers import `Model.Invariant`
  unqualified (or not at all), so adding `↑ˡ≢↑ʳ` to `Invariant` clashes tree-wide with their local copies;
  consolidation requires a coordinated deletion across all sites with per-site aliases (`¬ P` vs `P → ⊥`;
  `↑ˡ-↑ʳ-disjoint` vs `↑ˡ≢↑ʳ`) to dedup ~25 LOC of trivial proof. Plan: add the general lemma to
  `Invariant`, repoint via `using`/`as` aliases at all 5 sites in one commit. Deferred for a focused pass.
- **rank 34** (`inject+-inj`/`raise-inj` → stdlib `↑ˡ-injective`/`↑ʳ-injective` wrappers) and **rank 35**
  (`Prune.↑ˡ-↑ʳ-disjoint` spurious-param removal) — needs-care implicit/explicit arg adaptation across
  call sites; `35` is entangled with `Invariant`'s module params and overlaps `33`. Deferred with `33`.

The 2 high-risk mirror-proof merges (ranks 53/54) remain out of scope per the original plan.
