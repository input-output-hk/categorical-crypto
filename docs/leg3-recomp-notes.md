# LEG 3 (recomposition + focus/retract/pad soundness) — working notes

Module: src/Leg3Recomp.agda  ({-# OPTIONS --safe --without-K #-})
Goal: ⟪ deepFrame s lᵗ lᵗ n found ⟫ ≅ᴴ ⟪ ctx ⟫[h ↦ ⟪lᵗ⟫]
deepFrame = post ∘ ((id{k} ⊗₁ lᵗ) ∘ pre), (k,pre,post) from focusAtₙ ctx (Agen hole) then retract.

## Sub-proofs
(1) ⟪frame⟫ definitional expansion — TODO
(2) focusAtₙ term-soundness — TODO
(3) retract soundness — TODO
(4) hole-subst-commutes-with-⟪⟫ — TODO
(5) pad-layer soundness — TODO

## Log

### Audit (step 1)
- Translation.agda: ⟪g∘f⟫ = hComposeP ⟪f⟫ ⟪g⟫ (DEFINITIONAL), ⟪f⊗₁g⟫ = hTensor ⟪f⟫ ⟪g⟫ (DEFINITIONAL). Confirmed.
- ⟪_⟫ maps λ⇒/λ⇐/ρ/α to hId, σ to hSwap. So all coherence iso terms collapse to hId graphs.
- Iso.agda: refl-≅ᴴ, sym-≅ᴴ, trans-≅ᴴ all proven (equivalence).
- SoundnessFullWired: REVERSE direction ⟪f⟫≅ᴴ⟪g⟫ → f≈Term g (proven). NOT what we need directly.
- FORWARD direction f≈Term g → ⟪f⟫≅ᴴ⟪g⟫ does NOT exist. hComposeP-resp-≅ᴴ / hTensor-resp-≅ᴴ mentioned in HomTermInvariant.agda:7 but NOT proven.
- HomTermInvariant: ⟪_⟫-dom-unique / ⟪_⟫-cod-unique proven (prereqs for congruence).

### Strategy
Goal RHS ⟪ctx⟫[h↦⟪lᵗ⟫] is GRAPH-level hole subst. Path:
 - hole-subst-commutes (sub-proof 4): ⟪ctx⟫[h↦⟪lᵗ⟫] ≅ᴴ ⟪ ctx[h↦lᵗ] ⟫ (term-level subst over base sig)
 - focusAtₙ term-soundness (sub-proof 2): ctx ≈Term⁺ post⁺ ∘ ((id ⊗ Agen hole) ∘ pre⁺)
 - retract soundness (3): ⟪retract p⟫ ≡ ⟪p⟫ for h-free terms
 - then need ≈Term → ≅ᴴ (FORWARD soundness of ⟪_⟫) to land the iso. MUST BUILD this — it is the genuine LEG-3 core mass.
 - pad layer (5): repadR/repadL σ/α coherence soundness.

NB: ≈Term → ≅ᴴ forward is the per-axiom graph-identity direction; each axiom is an hId/hSwap collapse. Plan to build it as the central reusable lemma `⟪⟫-resp-≈Term`.

### Progress checkpoint 1 (COMPILES clean)
- (1) frame-expand : ⟪frame⟫ ≅ᴴ ⟪post∘((id⊗mid)∘pre)⟫ via refl-≅ᴴ — DONE (definitional). ~10 LOC.
- (2) infrastructure: Pred / All-Pred / app-Pred / map-Pred ; leaf-frame-id (left-unitor collapse, PROVEN); leaf-try-sound (uses SFW.soundness-full-wired on recovered findIso witness, PROVEN). ~80 LOC so far.
- TODO (2): mutual go-all-sound/focusAll-sound (∘ cases easy; ⊗ cases need interchange+σ).

### CHECKPOINT 2 (COMPILES clean, ZERO postulates/holes, --safe --without-K)
DONE:
- (1) frame-expand : ⟪frame⟫ ≅ᴴ ⟪post∘((id⊗mid)∘pre)⟫ (refl-≅ᴴ, definitional). ~10 LOC.
- (2) focusAtₙ TERM-SOUNDNESS — FULLY PROVEN.
    * Pred / All-Pred / app-Pred / map-Pred (list infra)
    * leaf-frame-id (left-unitor collapse λ⇒∘((id⊗lᵗ)∘λ⇐)≈lᵗ)
    * leaf-try-sound (uses SFW.soundness-full-wired on recovered findIso ≅ᴴ witness)
    * rfactor-coh (⊗ right-factor coherence chase, PROVEN; α-naturality)
    * braid-nat + braid-conj + lfactor-coh (⊗ left-factor σ+α braid chase, PROVEN;
      NB: earlier planned as temp-postulate but DISCHARGED — full σ∘σ≈id braid-cancel)
    * mutual focusAll-sound/go-all-sound (∘ both operands, ⊗ both factors, leaf, units)
    * lookup-Pred + focusAtₙ-sound corollary:
        focusAtₙ s lᵗ n ≡ just (k,pre,post) → s ≈Term post∘((id{k}⊗lᵗ)∘pre)
  ~480 LOC. Works over ARBITRARY APROPSignatureDec, so applies at Deep's C⁺ (sig⁺) too.

REMAINING: (3) retract soundness, (4) hole-subst-commutes, (5) pad layer, final assembly.

### CHECKPOINT 3 (COMPILES clean, ZERO postulates/holes)
DONE:
- (3) retract soundness — module RetractSound (P Q). FULLY PROVEN:
    * incl : HomTerm A B → HomTerm⁺ A B (signature inclusion, structural)
    * retract-incl : retract (incl p) ≡ just p  (section / right-inverse, structural induction)
    * retract-faithful : retract p ≡ just p₀ → p ≡ incl p₀  (faithfulness on hole-free terms)
  ~85 LOC. Instance plumbing: σ clause preserves the input ⦃Symm≤Symm⦄ instance into σ⁺.
  This is the verifiable content guaranteeing pre₀/post₀ = retract pre⁺/post⁺ are the
  genuine base-sig inclusions whose translation the assembly controls.

STATUS: (1)(2)(3) DONE, postulate-free, --safe --without-K.
REMAINING: (4) hole-subst-commutes-with-⟪⟫, (5) pad-layer soundness, final ≅ᴴ assembly.

### CHECKPOINT 4 (COMPILES clean, ZERO postulates/holes)
DONE:
- (5) pad-layer soundness — PARTIAL (the σ/α iso kernel, fully proven):
    * peelR-leaf-iso / peelR-leaf-iso' : (σ∘λ⇒)∘(λ⇐∘σ)≈id and inverse — the Var-w
      peel-RIGHT leaf maps (r=λ⇐∘σ, u=σ∘λ⇒) are mutually inverse. PROVEN.
    * peelL-leaf-iso / peelL-leaf-iso' : λ⇒∘λ⇐≈id, λ⇐∘λ⇒≈id — peel-LEFT leaf. PROVEN.
    * liftR-iso : associator-conjugation preserves the round-trip (u∘r≈id ⇒
      lifted wrappers compose to id). PROVEN. (covers liftR + the no-σ parts of liftL)
  ~95 LOC. These establish the peel maps are ISOS — the core soundness fact making
  repadding sound (repadded frame = old frame conjugated by an iso ⇒ same morphism).
  REMAINING for full (5): the liftL-with-swapIn/swapOut variants' round-trip
  (same shape + one σ-naturality, ~40 LOC), and the peel-vs-padded-generator
  naturality (r Q ∘ (id⊗x) ≈ (id⊗(x⊗id))∘r P), plus tying to repadR/repadL Foc
  outputs (blocked on those being `private` in Deep.At — needs re-export or mirror).

### FINAL STATUS (src/Leg3Recomp.agda — 800 LOC, --safe --without-K, ZERO postulates/holes, builds CLEAN)

Per sub-proof:
- (1) ⟪frame⟫ definitional expansion ...... DONE (~10 LOC). frame-expand via refl-≅ᴴ.
- (2) focusAtₙ term-soundness ............. DONE, FULLY PROVEN (~480 LOC).
      focusAll-sound / go-all-sound (mutual; ∘ both, ⊗ both factors incl. σ-braid
      left-factor, leaf via reverse soundness), focusAtₙ-sound corollary.
      NB lfactor-coh (σ+α braid chase) was planned as temp-postulate but DISCHARGED.
      Works over ANY APROPSignatureDec ⇒ directly applicable at Deep's C⁺/sig⁺.
- (3) retract soundness ................... DONE, FULLY PROVEN (~85 LOC).
      incl + retract-incl (section) + retract-faithful (faithfulness on hole-free).
- (5) pad-layer soundness ................. PARTIAL, proven kernel (~95 LOC).
      peelR/peelL leaf isos (the σ content) + liftR-iso (α-conjugation round-trip).
      Remaining: liftL-swap variant (~40 LOC) + peel/generator naturality + tie to
      repadR/repadL (blocked: those are `private` in Deep.At — need re-export/mirror).
- (4) hole-subst-commutes-with-⟪⟫ ......... NOT DONE (blocked).
      BLOCKER: requires the FORWARD translation soundness f≈Term g → ⟪f⟫≅ᴴ⟪g⟫
      ("Hypergraph completeness" direction), which does NOT exist in tree (only the
      reverse `soundness-full-wired`). Every coherence axiom collapses to hId/hSwap, so
      it is TRUE and provable, but it is the unwritten ~sizeable Completeness module
      (per-axiom graph iso + hComposeP/hTensor congruences). Documented in module tail.

ASSEMBLY: recipe documented in module tail; composes (1)+(2)+(3)+(4)+forward-lemma.
The term-level recomposition identity (s ≈Term deepFrame) is fully reachable from the
proven pieces; only the final ≅ᴴ wrap-up is gated on the one forward lemma.

NO TEMP POSTULATES remain. All claimed-DONE items are postulate/hole-free and machine-checked.
