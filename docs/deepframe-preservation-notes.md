# CRUX SPIKE NOTES — proof-carrying Route A milestone-0 de-risking

Started: 2026-06-14. Work dir: /tmp/crux-spike. NO commits, NO touching /Users/andre.

## Goal
GO/NO-GO for proof-carrying Route A. Two targets:
- TARGET 1: per-edge LABEL preservation (expected easy)
- TARGET 2: per-edge ENDPOINT preservation for ONE edge at process-edges level (bellwether)

## Log

### 2026-06-14 — code reading complete
- Confirmed decoder structure (Decode.agda): process-edges folds edge-step left-nested ∘ (t' ∘ t), one Agen-edge per edge in Fin order. decode-attempt = final-permute ∘ process-term. Agen-edge e = Agen-edge-aux (H.elab e) = (iso) ∘ Agen g ∘ (iso) where H.elab e ≡ flat g (up to subst₂ FlatGen).
- Translation.agda: ⟪_⟫ is DEFINITIONAL on ∘/⊗/Agen: ⟪Agen f⟫ = hGen f; ⟪g∘f⟫ = hComposeP ⟪f⟫ ⟪g⟫; ⟪f⊗₁g⟫ = hTensor ⟪f⟫ ⟪g⟫. Coherences (λ ρ α σ) → hId/hSwap (0 user edges).
- hGen f (FromAPROP.agda:274): nE=1, elab = λ _ → subst₂ FlatGen lem-in lem-out (flat f). THE LABEL ATOM: a single Agen's hypergraph has exactly one edge whose label is `flat f` modulo a subst₂ on the boundary vertex-lists.
- hComposeP edges = G-edges then K-edges (pruned); hTensor edges = G then K (splitAt). So ⟪t⟫'s edge enumeration = the in-order concatenation of the Agen leaves' single edges, in term left-to-right (data-flow) order — EXACTLY the ROUTEA-NOTES order claim.
- LABEL-PRESERVATION REFRAMED: the real content is NOT "decode emits the label" (definitional) but "⟪_⟫ ∘ decode round-trip preserves it". Two sub-facts: (A) every Agen leaf of the decoded term carries H.elab e [structural on the term, easy]; (B) ⟪_⟫ maps an Agen-leaf's label to a hypergraph edge with that label [the hGen fact above, modulo subst].

### 2026-06-14 — TARGET 1 (LABEL) progress: GREEN so far
- src/CruxSpike.agda compiles clean (--safe --without-K, NO postulates, NO holes).
- PROVEN:
  - genOf : FlatGen ins outs → Gen* (= Σ A B, mor A B), forgets boundaries.
  - genOf-subst₂ p q fg ≡ genOf fg : the boundary subst₂ FlatGen NEVER touches the underlying generator. THIS is what defuses the heavy boundary bookkeeping that the plan feared. refl after matching p,q.
  - genOf-elab-c-inj₁/₂ (hComposeP): label of composite edge eG↑ˡ / G.nE↑ʳ = label of originating G/K edge. Proof = match splitAt + genOf-subst₂. (Note: did NOT need the heavy elab-c-inj₁/₂ lemmas in PrunedCompose — genOf bypasses their substs entirely.)
  - genList-hComposeP : genList (hComposeP G K eq) ≡ genList G ++ genList K. Via range-++ (Invariant.agda) + map-++ + map-∘ + map-cong. ~12 LOC.
  - genOf-Telab-c-inj₁/₂ + genList-hTensor : same for hTensor. ~20 LOC.
- KEY METHODOLOGICAL WIN: working with genList (the boundary-free generator shadow) instead of the indexed elab makes label preservation a clean list-concatenation induction. The vertex/boundary substs that the plan flagged as where "LOC can balloon" are absorbed once-and-for-all by genOf-subst₂. This is strong GO evidence for the LABEL half.

### 2026-06-14 — TARGET 1 (LABEL) COMPLETE — fully general, GREEN
- MASTER THEOREM proven (no postulate, no hole, --safe --without-K):
    genList-⟪⟫ : ∀ {A B} (t : HomTerm A B) → genList ⟪ t ⟫ ≡ termGens t
  where termGens is the in-order list of leaf generators of the term (Agen→[g], coherences→[], ∘/⊗→++ in data-flow order matching ⟪g∘f⟫=hComposeP ⟪f⟫ ⟪g⟫).
- Total LABEL cost: ~120 LOC for the FULLY GENERAL theorem over arbitrary HomTerms. Not bench-specific. This is much cheaper than the plan's implicit estimate and dodges focus/retract entirely for the label half: once you have decode-attempt's term, genList-⟪⟫ gives you the labels of ⟪decode⟫'s edges = termGens(decoded term), and termGens of process-edges' output = the per-edge H.elab list by a trivial process-edges induction (each edge-step contributes exactly Agen-edge-aux(H.elab e) = one leaf with genOf = genOf(H.elab e); coherence wrappers contribute []).
- VERDICT for label half: clean GO. The boundary substs (the feared balloon) are absorbed once by genOf-subst₂ (one refl-after-match). Structural induction carries the rest.

### 2026-06-14 — TARGET 2 (ENDPOINTS) analysis begins
- Iso.agda _≅ᴴ_ : the endpoint half = field ψ-ein e : K.ein (ψ e) ≡ map φ (G.ein e) with φ : Fin G.nV → Fin K.nV the vertex correspondence (+ ψ-eout). The label half I proved corresponds to ψ-elab (modulo atom-ein/atom-eout substs that genOf showed harmless).
- CRITICAL STRUCTURAL OBSERVATION from Decode.agda: the decoded TERM is typed in `unflatten (map H.vlab …)` — the term and hence ⟪decode⟫ carry ATOM labels (X values via H.vlab), NOT the original Fin H.nV vertex identities. The Fin H.nV indices appear ONLY in the algorithm's stack `s : List (Fin H.nV)`; they are pushed through H.vlab into the term immediately. So ⟪decode H⟫'s vertices are FRESH (term-structure-built via injL/injR/remapP), labelled by X, with NO residual trace of which original H-vertex they came from beyond the X label.
- CONSEQUENCE: recovering φ : H.nV → ⟪decode⟫.nV is NOT a structural read-off. Two distinct H-vertices with the SAME X-label are indistinguishable in ⟪decode⟫. φ must be reconstructed from the WIRING (which edge endpoint went where), i.e. from the stack-threading history — exactly the global data. This is the wall the plan feared.

### 2026-06-14 — TARGET 2 refined: where φ comes from, and the wall
- Refinement of the X-label worry: flatten-unflatten l ≡ l holds POSITIONALLY (Unflatten.agda:42-44). So the boundary X-list is recovered position-for-position; ⟪⟫'s vertices ARE in bijection with boundary/wiring POSITIONS, and positions DO carry identity. So φ is not destroyed by X-collapse after all — it is a POSITION map. Earlier "two same-label vertices indistinguishable" worry is too pessimistic at the term level: the term keeps them in distinct positions. GOOD news, softens the wall.
- The actual φ source: edge-step (Decode.agda:102-127) on success carries `perm : s ↭ (H.ein e ++ rest)` from extract-prefix. The Agen-edge e in ⟪⟫ gets endpoints = the LOCAL positions 0..|ein|-1 (front) within the stack-as-list; permute-via-vlab perm re-associates those to the stack's positions. So for ONE edge in isolation, the edge's ⟪⟫-endpoints are determined by `perm` applied to the front |ein e| slots — φ_local is readable from perm.
- THE WALL (now precise): the stack `s` at edge e is `process-edges (earlier edges) H.dom .proj₁`. To turn φ_local (positions in s) into φ_global (Fin H.nV), you must know the CONTENT of s at step e — i.e. which H-vertices occupy which stack slots. That stack content is the fold of ALL prior edge-steps (each pops H.ein, pushes H.eout). Tracking it = a process-edges invariant `stack-content : the multiset/list of s at step k is determined`, which is exactly the linearity/topological-soundness reasoning (each vertex produced once, consumed once). This is global, and it is precisely what Linearity.agda / DecodeAttemptLinearP already do for the `just` totality proof — substantial existing machinery.

### 2026-06-14 — TARGET 2: endpoint induction IS structurally available (positive)
- PROVEN in CruxSpike.agda (no postulate, no hole):
  - endpoint-Agen-ein/eout : leaf endpoints of ⟪ Agen g ⟫ are DEFINITIONAL (refl) — the front |flatten A| / back |flatten B| range. Leaf is free.
  - EndpointStep.comp-ein-G : ein (hComposeP G K eq) (eG↑ˡK.nE) ≡ map injL (G.ein eG)  [= ein-c-inj₁-red, reused]
  - EndpointStep.comp-ein-K : ein (hComposeP G K eq) (G.nE↑ʳeK) ≡ map remapP (K.ein eK) [= ein-c-inj₂-red, reused]
- CONCLUSION: the endpoint induction has the SAME left-nested ∘/⊗ shape as the label induction, EXCEPT the per-level vertex map is injL (G-side, trivial) / remapP (K-side, boundary-keyed) instead of identity. The composite-edge endpoint is structurally expressible as (vertex-map) ∘ (sub-edge endpoint). The reduction lemmas ALREADY EXIST in PrunedCompose (ein-c-inj₁-red/inj₂-red, eout analogues). hTensor has injL/injR analogues too. So milestone-1's endpoint half is NOT blocked at the per-composite-edge step.
- REMAINING RISK (the real wall, now isolated): assembling the per-level injL/remapP cascade into ONE global φ : H.nV → ⟪decode⟫.nV and proving ψ-ein against H.ein (ORIGINAL graph). The endpoint-step relates composite↔subterm; the FINAL leg relates the decode-term's leaf wiring (permute-via-vlab perm + unflatten-++ bridges) to H.ein/H.eout. That leg needs: (i) ⟪permute-via-vlab perm⟫'s vertex action = perm (a Steps-level fact, likely existing/structural), and (ii) the stack-content invariant (which Fin H.nV sits in which slot at step e) to know the front |H.ein e| slots ARE H.ein e. (ii) is the global/linearity part — but it is the SAME invariant the existing `just`-totality proof (DecodeAttemptLinearP / Linearity.agda) already establishes. So it is reusable, bounded existing machinery, NOT a new months-scale theorem.

### 2026-06-14 — positional stack machinery DOES exist (key for endpoints)
- Linearity.agda (411 LOC) tracks only COUNT (produced/consumed once), NOT positions. By itself insufficient for endpoints.
- BUT DecodeAttemptLinearP.agda (461 LOC) DOES track the stack POSITIONALLY through process-edges: lemmas like process-edges-↑ˡ-pure-L, edge-step-↑ˡ-pure-L-just relate the threaded stack to `map injL xs` / explicit ↭ permutations. DecodeAttempt.agda (655 LOC) has process-edges-++-stack (stack content composes across edge-list concatenation, by induction). This is exactly the positional stack-content threading the endpoint proof needs, already written (for the pruned `just`-totality proof) and --safe.
- So the endpoint "final leg" (decode-term leaf wiring ↔ H.ein/H.eout) can REUSE ~1500 LOC of existing positional stack machinery rather than re-deriving it. It still needs a NEW invariant connecting stack POSITION to the ⟪⟫-vertex index emitted by edge-step, but the hard substrate (stack threads correctly) is done.

================================================================================
## VERDICT: GO (qualified) for proof-carrying Route A
================================================================================

(1) LABEL preservation: CLEAN GO. Fully general theorem genList-⟪⟫ proven over
    ALL HomTerms (~120 LOC, no postulate, no hole, --safe --without-K). The
    feared boundary-subst balloon is absorbed once by genOf-subst₂ (refl after
    matching). Applied to decode-attempt's term, label preservation is immediate.
    Confidence: HIGH. Milestone-1 LABEL half is far cheaper than the plan's
    400-700 LOC bracket suggested — call it ~150-250 LOC including the
    process-edges termGens-equals-H.elab lemma.

(2) ONE-edge ENDPOINT at process-edges level: PARTIAL GO, no hard wall hit.
    - Leaf endpoints: definitional (refl).
    - Per-composite-edge endpoint relay: PROVEN via reuse of PrunedCompose's
      ein-c-inj₁-red (injL, G-side) / ein-c-inj₂-red (remapP, K-side). The
      endpoint induction has the SAME ∘/⊗ shape as the label induction; the only
      difference is a non-trivial per-level vertex map (injL/remapP) vs identity.
    - The remaining piece (leaf wiring ↔ H.ein) needs a positional stack-content
      invariant. This did NOT turn out to require global acyclicity as a NEW
      theorem: (a) the count-based linearity (Linearity.agda) gives the multiset
      side; (b) DecodeAttemptLinearP/DecodeAttempt ALREADY thread the stack
      POSITIONALLY across process-edges. So the endpoint proof reuses existing
      --safe machinery; the genuinely new work is a vertex-index invariant
      linking stack slot k to the emitted ⟪⟫-vertex.
    - I did NOT fully close one edge's endpoint end-to-end (that needs the
      vertex-index invariant + permute-via-vlab's ⟪⟫-action, ~1-2 days more than
      the spike budget). But every sub-step I touched went through structurally
      with NO postulate standing in for the hard part. No wall.

(3) Temporary postulates used: NONE. Everything in CruxSpike.agda is proven.
    (This is itself strong evidence: I did not have to fake the hard part to make
    the rest go through.)

(4) Revised milestone-1 (complement-edge preservation, general) estimate:
    - LABEL half: ~150-250 LOC (genList-⟪⟫ done; + process-edges termGens lemma).
    - ENDPOINT half: ~500-800 LOC NEW (the vertex-index/φ-reconstruction invariant
      + permute-via-vlab/unflatten-++ ⟪⟫-action lemmas), REUSING ~1500 LOC of
      existing positional stack machinery (DecodeAttempt/DecodeAttemptLinearP/
      Linearity) — do NOT re-derive those.
    - Net milestone-1: ~650-1050 LOC, consistent with the plan's 400-700 if the
      reuse holds, slightly above if the vertex-index invariant is fiddly. The
      plan's 5-8 week total still looks right; risk is at the high end, not blown.

(5) SINGLE BIGGEST REMAINING RISK: the vertex-index invariant linking the
    process-edges STACK POSITION to the ⟪⟫-vertex emitted for an edge's
    endpoint. The positional stack threading exists; what's unproven is that
    permute-via-vlab + the unflatten-++-≅ bridges in edge-step compose to place
    each H-vertex at the ⟪⟫-position that φ predicts, uniformly across the
    left-nested ∘-tower's remapP cascade. This is fiddly (Fin arithmetic through
    remapP/injL/cast) but it is BOUNDED Fin-combinatorics, not a global
    well-formedness/acyclicity theorem in disguise. The spike found no evidence
    it needs the Route-B graph-completeness leg. Recommend a 1-2 day follow-up
    spike closing ONE edge's endpoint end-to-end before committing milestone 1.

================================================================================
## SESSION 2 (2026-06-14, new agent) — pushing ONE edge endpoint end-to-end
================================================================================

### Recovered state
- CruxSpike.agda compiles clean (verified). Label half DONE (genList-⟪⟫). Endpoint
  per-composite-edge relay PROVEN (EndpointStep.comp-ein-G/K). Leaf endpoints refl.
- The decided target now: take ONE successful edge-step (just branch), and show
  ⟪ bridged ⟫'s user-edge has ein/eout on the stack positions matching H.ein/H.eout.
- bridged = mid' ∘ permute-via-vlab vlab perm ; mid = to(iso) ∘ (Agen-edge e ⊗₁ id) ∘ from(iso).
- So ⟪bridged⟫ = hComposeP ⟪perm⟫ ⟪mid'⟫ ; the lone user edge lives in ⟪mid⟫'s
  (Agen-edge e ⊗₁ id) factor, on the LEFT (↑ˡ) of the ⊗ with id.

### 2026-06-14 (S2) — edge-COUNT lemma proven, reframes the difficulty
- nE-⟪⟫ : nE ⟪t⟫ ≡ length (termGens t)  [PROVEN, via genList-⟪⟫ + length-range +
  length-map]. Corollary: nE of any coherence-iso term is 0; nE of Agen-edge-aux
  (flat g) is 1. NOTE: even getting nE=1 for the leaf is NOT definitional refl
  (hComposeP nE = G.nE+K.nE and the iso-nE=0 facts are propositional). nE-⟪⟫
  supplies it cleanly. ~10 LOC.
- KEY STRUCTURAL FINDING (the wall, made fully precise this session):
  The hypergraph is a COSPAN. A 0-edge graph (⟪coherence⟫, ⟪permute p⟫) carries
  its entire dom↔cod wiring as VERTEX-INDEX IDENTITIES (which Fin nV each dom/cod
  position points at), NOT as any edge data. genList/nE (label side) is BLIND to
  this. So the endpoint invariant is irreducibly a fact about vertex-index
  identities traced through the remapP/injL/injR cascade of hComposeP/hTensor
  PLUS the dom/cod index choices of hSwap/hId. permute p (built from id/⊗/σ/α)
  must be shown to realize p AS A VERTEX-POSITION MAP. There is no shortcut via
  the label machinery — this is genuinely the hard, separate half.

### 2026-06-14 (S2) — composition-layer probes PROVEN; permute layer is the wall
- PROVEN (no postulate/hole, --safe --without-K, all in CruxSpike.agda):
  - leaf-ein≡dom / leaf-eout≡cod : for hGen g = ⟪Agen g⟫, the lone edge's
    ein/eout coincide DEFINITIONALLY (refl) with dom/cod. Leaf endpoint = free.
  - tensor-id-ein : ein of the user-edge through `⊗₁ id` (= hTensor (hGen g)(hId C))
    = map injL (G.ein zero)  [reuse hTensor-impl.ein-c-inj₁-red].
  - tensor-id-ein-is-dom-prefix : that injL-block = map injL (G.dom) = the FRONT
    (A-prefix) block of the composite domain interface. So the `⊗₁ id` layer of
    edge-step's `mid` is provably benign: the edge stays on the domain prefix.
- THE PERMUTE LAYER IS THE WALL (rigorously isolated this session):
  - bridged = mid' ∘ permute-via-vlab vlab perm. The remaining transport is
    through hComposeP ⟪permute perm⟫ ⟪mid'⟫. permute perm is a 0-EDGE hypergraph
    whose ENTIRE content is a dom↔cod VERTEX-INDEX wiring realizing perm.
  - hComposeP routes the K-side (⟪mid'⟫) edge via remapP = remap K.dom lookup-cod:
    a K-vertex IN K.dom is rerouted to the matching G.cod vertex (injL). To prove
    the edge lands on H.ein e's stack positions you must show ⟪permute perm⟫'s
    cod-vertices sit at the perm-image positions AND remapP threads them there.
  - SEARCHED the whole tree: NO existing lemma states "⟪permute p⟫'s dom→cod
    vertex map = p". The existing soundness machinery (SwapStep, DecodeComposePruned,
    IsoInvarianceWiring, ProcessEdges↭Goal) reasons about permute at the ≈Term
    (term-equation) level, NOT the hypergraph-vertex level. This vertex-action
    lemma is GENUINELY NEW and is the irreducible hard part.
  - GOOD NEWS on tractability: the positional substrate EXISTS. Prune.agda has
    remap-inj₁ (member at position i ↦ f i ↑ˡ count-non) / remap-inj₂ /
    remap-injective / remap-vlab. So the permute vertex-action proof would chain
    remap-inj₁ through permute's id/⊗/σ/α recursion + the hComposeP remapP cascade.
    Substantial Fin-combinatorics, but the primitives are present and --safe. No
    sign it needs global acyclicity / Route-B graph completeness.

================================================================================
## SESSION-2 VERDICT
================================================================================
- DID ONE EDGE'S ENDPOINT CLOSE END-TO-END (zero postulates)? NO — not fully.
  What DID close cleanly (zero postulates): (a) leaf endpoint = boundary (refl);
  (b) the `⊗₁ id` composition layer (edge stays on domain prefix); (c) edge-COUNT
  nE-⟪⟫. What did NOT close: the `permute`/remapP vertex-action transport, i.e.
  the actual link from the edge's emitted ⟪⟫-vertex back to H.ein e/H.eout e
  through the stack permutation. That requires the NEW permute-vertex-action lemma.
- POSTULATE CLASSIFICATION: I introduced ZERO postulates. I did NOT fake the hard
  part with a placeholder; I stopped at it honestly. The unproven piece (permute
  vertex-action + remapP threading) IS the hard part — so by the decision rule the
  single-edge case is NOT closed end-to-end.
- NO WALL OF THE FEARED KIND: the hard part is bounded Fin/remap combinatorics with
  existing primitives (remap-inj₁ etc.), NOT a disguised global acyclicity theorem.
  The cospan-wiring observation makes clear WHY the label machinery can't reach it,
  but also that it is self-contained.
- REVISED CONFIDENCE: GO (downgraded from "STRONG GO" — the bellwether did not fully
  close in-budget, but no blocking wall appeared and every primitive needed exists).
- REVISED MILESTONE-1 ESTIMATE:
  * LABEL half: ~150-250 LOC (genList-⟪⟫ DONE; + process-edges termGens lemma). HIGH conf.
  * ENDPOINT half: the NEW permute-vertex-action lemma is the cost center. Estimate
    ~400-700 LOC for it (chaining remap-inj₁ through permute's recursion + hComposeP
    remapP cascade + the unflatten-++-≅ bridges), PLUS ~200-400 LOC to assemble the
    per-edge statement and push it through process-edges (reusing DecodeAttempt/
    DecodeAttemptLinearP ~1500 LOC positional stack threading — do NOT re-derive).
  * Net milestone-1: ~750-1350 LOC. Toward the HIGH end of the plan's 400-700 bracket
    for the endpoint half specifically; consistent with the plan's 5-8 week total at
    the upper-middle of the range. Risk concentrated entirely in the permute
    vertex-action lemma — recommend prototyping THAT lemma (base + prep + swap cases)
    as the very first milestone-1 task to confirm the LOC estimate before committing.

================================================================================
## SESSION 3 (2026-06-14, new agent) — PROTOTYPE the permute-vertex-action lemma
================================================================================

### Recovered + located the exact definitions
- `permute` source = Categories/PermuteCoherence/Faithfulness.agda:90-95. Over `List X`
  (NOT Fin), 4 ↭-constructors:
    permute refl       = id
    permute (prep x p) = id ⊗₁ permute p
    permute (swap x y p) = (id ⊗₁ (id ⊗₁ permute p)) ∘ α⇒ ∘ (σ ⊗₁ id) ∘ α⇐
    permute (trans p q) = permute q ∘ permute p
- `permute-via-vlab vlab p = permute (map⁺ vlab p)` (Steps.agda:56).
- APROP HomTerm ≡ FreeMonoidal.HomTerm asFreeMonoidalData (APROP.agda:30), so CruxSpike's
  ⟪_⟫ applies to `permute p` directly. GOOD — no type-bridging needed.
- 0-edge hypergraph content = nV, vlab, dom:List(Fin nV), cod:List(Fin nV). The
  "vertex action" = the dom↔cod relationship. ⟪id⟫=hId, ⟪σ⟫=hSwap, ⟪α⟫=hId, ⟪g∘f⟫=hComposeP,
  ⟪f⊗₁g⟫=hTensor.
- hId A: dom=cod (recursive tensor of hVar/hEmpty). hSwap A B: dom = injL-block ++ injR-block,
  cod = injR-block ++ injL-block (the swap, at vertex-index level).
- DECISION on lemma shape: prove `cod ⟪permute p⟫ ≡ permuteVec p (dom ⟪permute p⟫)` where
  the RHS reorders the dom POSITION-list by p. This is the position-level vertex action.

### 2026-06-14 (S3) — refl case CLOSED, zero postulates, but NOT trivial
- permute-refl-dom≡cod PROVEN. Required helper hId-dom≡cod : dom(hId A)≡cod(hId A),
  which is NOT refl — hTensor recursion makes dom=map injL G.dom ++ map injR K.dom,
  so it's a 2-line structural cong₂ induction on A. ~8 LOC total for refl case.
- LESSON: even the "trivial" refl case is a (small) induction, because hId is recursive
  via hTensor at the Fin-nV (vertex-index) level. Foreshadows that the whole lemma is
  Fin-index bookkeeping through injL/injR/remapP, NOT one-liners.
- prep case: ⟪permute(prep x p)⟫ = hTensor (hId(Var x)) ⟪permute p⟫. dom/cod each split
  injL(hId-block, identity) ++ injR(recursive permute-block). The recursion is in injR.
- STATEMENT-CHOICE PROBLEM (the real design question): need a dom↔cod relation stable
  under hTensor(prep), hComposeP(trans), hSwap(swap). Candidate: cod ≡ applyσ p dom where
  applyσ replays p's head-shuffle on the Fin-nV list. BUT under hComposeP (trans), nV
  CHANGES (pruning) so dom/cod live in different Fin nV than the sub-permutes — the
  reindexing via remapP must be threaded. This is exactly the predicted hard part.

### 2026-06-14 (S3) — prep + swap structural probes; wall character pinned down
- prep case: ⟪permute(prep x p)⟫ = hTensor(hId(Var x)) ⟪permute p⟫. dom/cod block
  split (map injL G-block ++ map injR K-block) is DEFINITIONAL (prep-dom/prep-cod = refl).
  So prep reduces cleanly to: identity on head block + recursive action on tail (injR).
  prep is EASY once the carried invariant is fixed. ~10-20 LOC.
- swap case (the genuinely new constructor): permute(swap x y p) =
  (id⊗₁(id⊗₁permute p)) ∘ α⇒ ∘ (σ⊗₁id) ∘ α⇐  →  a 4-layer hComposeP nest of hId/hSwap.
  * GOOD: pruning COLLAPSES vertex count. swap2 (smallest: x∷y∷[] ↭ y∷x∷[]) has
    nV ≡ 2 (PROVEN refl) — the 4-layer nest does NOT blow up vertices. No acyclicity.
  * HARD: dom/cod do NOT auto-reduce. hComposeP gives dom = map injL G.dom,
    cod = map remapP K.cod. So the concrete swap2 dom is a NESTED map injL / map remapP
    cascade (printed; tangled). Evaluating it = applying remap-inj₁/₂ + classify-inj₁-lookup
    layer by layer.
- THE CROSSABILITY ARGUMENT (why this is GO not NO-GO): the substrate to cross the cascade
  EXISTS and is decidable Fin-combinatorics — Prune.agda has remap-inj₁, remap-inj₂,
  classify, classify-inj₁-lookup, count-non. Because every ⟪permute⟫ sub-graph is a 0-edge
  cospan whose cod is a bijective reordering of dom (cod ⊆ dom as a permutation), the remapP
  at each hComposeP layer ALWAYS takes the inj₁ (member) branch → remap-inj₁ → lookup-cod,
  chaining cleanly to the previous layer's cod. No inj₂/non-member dead-ends. This is the
  key structural enabler, and it's an invariant you CARRY (cod-is-perm-of-dom), provable
  inductively alongside the main statement.
- CARRYABLE INVARIANT (the design answer): prove jointly
    (I)  cod ⟪permute p⟫ = (positional reorder of) dom ⟪permute p⟫  realizing p, AND
    (II) every cod vertex ∈ dom (so remapP always hits inj₁ at the next ∘ layer).
  (II) makes the trans/swap hComposeP remapP reductions go through.

================================================================================
## SESSION-3 VERDICT — the permute-vertex-action lemma
================================================================================
- WHAT CLOSED, ZERO POSTULATES (CruxSpike.agda compiles --safe --without-K, 0 postulates):
  * refl case: permute-refl-dom≡cod (via hId-dom≡cod, a small cong₂ induction). ~8 LOC.
  * prep case STRUCTURE: prep-dom / prep-cod block-split definitional (refl). Reduces prep
    to head-identity + recursive tail.
  * swap case BOUNDARY (label level): swap-domL/swap-codL via existing ⟪⟫-domL/codL (free).
  * swap VERTEX-COUNT collapse: swap2-nV ≡ 2 (PROVEN). No vertex blow-up; no acyclicity.
- WHAT DID NOT CLOSE: the swap (and trans) VERTEX-INDEX dom→cod map through the hComposeP
  remapP cascade. NOT faked with a postulate — stopped honestly at it. By the decision rule
  this means the lemma is NOT fully closed end-to-end this session.
- CLASSIFICATION of the gap: STRUCTURAL/BOUNDED, not the-hard-part-in-disguise. It is a
  finite remap-inj₁/classify cascade over a vertex set that PROVABLY does not blow up
  (nV stays = boundary size), with ALL needed primitives already present and --safe. No
  missing sub-theory; no global acyclicity; no Route-B graph completeness. The cospan-
  bijection invariant (cod ⊆ dom) is the single new inductive fact that unlocks it.
- LOC ESTIMATE for the FULL permute-vertex-action lemma (refl+prep+swap+trans, with the
  carried cod-perm-of-dom invariant + remapP cascade lemmas):
  * refl: ~8 (DONE). prep: ~20. swap: ~120-180 (the 4-layer remapP cascade + hSwap block +
    the α/hId glue reductions). trans: ~60-100 (two-layer remapP compose, reuses swap's
    cascade lemmas). Shared remapP/classify reduction helpers + invariant: ~80-120.
  * TOTAL: ~290-430 LOC for the standalone permute-vertex-action lemma. Tightens the S2
    estimate (was 400-700) toward the LOW end — the nV-collapse finding is the reason
    (no blow-up to manage).
- MILESTONE-1 ENDPOINT HALF (full): permute-vertex-action (~290-430) + assembling the
  per-edge ψ-ein/ψ-eout statement and pushing through process-edges (reusing
  DecodeAttempt/DecodeAttemptLinearP ~1500 LOC positional stack threading — DO NOT
  re-derive): ~200-400 NEW. Endpoint half ~490-830 LOC.
- LABEL HALF: ~150-250 LOC (genList-⟪⟫ DONE). 
- NET MILESTONE-1: ~640-1080 LOC. Consistent with the plan; risk now firmly LOW-to-MID,
  not high — the bellwether sub-lemma's hard part turned out bounded + collapse-friendly.

VERDICT: GO for committing milestone 1.
  Rationale: (1) zero postulates needed anywhere; (2) refl closed, prep+swap structure
  closed, swap proven to NOT blow up vertices (nV collapses to boundary size); (3) the
  one unclosed piece (remapP vertex cascade) is bounded decidable Fin-combinatorics with
  ALL primitives present, gated by a single carryable cospan-bijection invariant — no
  disguised global theorem, no missing sub-theory, no acyclicity. Not STRONG-GO only
  because the swap remapP cascade was not pushed fully through in-budget; recommend the
  FIRST milestone-1 task be closing swap2 (smallest concrete swap) end-to-end at the
  vertex-index level to confirm the ~120-180 LOC swap estimate before scaling.

================================================================================
## SESSION 4 (2026-06-14, CHUNK-1 implementation) — permute-vertex-action lemma
================================================================================

### Design decision (the statement)
- Defined `permVec : xs ↭ ys → List Z → List Z` (positional reorder mirroring
  `permute`'s recursion: refl=id, prep=cons, swap=swap-first-2, trans=compose).
- LEMMA `vAction p : cod ⟪permute p⟫ ≡ permVec p (dom ⟪permute p⟫)` — VERTEX-INDEX
  level (Fin nV), the actual downstream content (pins which interface vertex each
  cod position is). Label-level would be too weak (reduces to a fact about lists
  + p alone with no hypergraph identity).
- Proved `permVec-map f p zs : permVec p (map f zs) ≡ map f (permVec p zs)`
  (naturality — permVec only reorders, never inspects). ~10 LOC, all constructor cases.

### CLOSED zero-postulate (compiles --safe --without-K):
- vAction-refl : via sym (hId-dom≡cod (unflatten xs)). ~1 LOC.
- vAction-prep p ih : ⟪permute(prep x p)⟫ = hTensor (hId(Var x)) ⟪permute p⟫.
  dom/cod = injL zero ∷ map injR (dom/cod K). cong (injL zero ∷_) + permVec-map +
  IH. ~8 LOC. NO remapP needed (prep is pure hTensor/hId, definitional block split).
- permVec + permVec-map: ~20 LOC infrastructure.

### CASE trans CLOSED zero-postulate (the predicted "hard" remapP cascade) — KEY WIN
- vAction-trans p q ihp ihq. ⟪permute(trans p q)⟫ = hComposeP ⟪permute p⟫ ⟪permute q⟫ eq.
  dom = map injL (dom P); cod = map remapP (cod Q).
- The whole remapP cascade collapses to ONE reuse of the EXISTING
  `map-remapP-K-dom : map remapP K.dom ≡ map (_↑ˡ cn) G.cod`
  (LinearHComposeP.agda), with Linear P / Linear Q from `⟪⟫-LinearP`. The proof is a
  5-step ≡-chain gluing IH(p), IH(q), permVec-map (naturality x3), and that crux fact.
  ~15 LOC + imports. NO per-layer remap-inj₁/classify chasing was needed at all — the
  linearity layer already packaged "each K.dom member routes to matching G.cod via injL".
- This is MUCH cheaper than S3's 60-100 LOC estimate. The cospan-bijection invariant the
  S3 notes wanted is exactly what map-remapP-K-dom encodes (via Linear's Unique cod).

### CASE swap CLOSED zero-postulate (the predicted WALL) — via a GENERIC compose lemma
- KEY ABSTRACTION: `Reorder` = record { app : ∀{Z:Set}→List Z→List Z ; natural :
  map-commutation }. `HasAction H φ = cod H ≡ app φ (dom H)`. `_then_` composes
  Reorders. (Reorder lives at Set-level carriers only — Set₁ record; universe-poly
  app made it Setω and failed, fixed by specialising carriers to Set.)
- GENERIC LEMMA `hComposeP-HasAction G K eq linG linK haG haK : HasAction
  (hComposeP G K eq) (φG then φK)`. This is the trans proof made generic — the SINGLE
  workhorse. Reuses `map-remapP-K-dom` (+ ⟪⟫-LinearP) exactly as trans did.
- swap term = t4 ∘ α⇒ ∘ (σ⊗id) ∘ α⇐ (∘ right-assoc) ⇒ ⟪⟫ = left-nested 3× hComposeP.
  Layer HasActions:
    * hId-HasAction A : ⟪α⇐⟫,⟪α⇒⟫ realise idR (cod≡dom via hId-dom≡cod). 
    * swap-tensor-id-HasAction C : ⟪σ⊗id⟫ = hTensor (hSwap(Var x)(Var y)) (hId C)
      realises swap2R (swap first 2 positions). hSwap nA=nB=1 ⇒ dom=[a,b],cod=[b,a];
      tensoring with hId C (cod≡dom) just appends a shared block ⇒ cod = swap2 dom.
      Proof = cong (λ w → injL b ∷ injL a ∷ map injR w) (sym hId-dom≡cod C). ~6 LOC.
    * tensor-id-left-HasAction K φ : hTensor (hId(Var x)) K realises consR φ (mirror
      of vAction-prep). t4 = consR(consR(permR p)) by two applications.
  Then 3× hComposeP-HasAction (φs given explicitly to kill metas) ⇒ HasAction of the
  whole composite with reorder (((idR then swap2R) then idR) then consR(consR permR p)).
- The composite reorder's app EQUALS permVec (swap x y p) — proved POINTWISE by `refl`
  on the 3 list shapes ([], z∷[], z∷w∷rest): all reduce definitionally. ~3 LOC.
  Transport HasAction along it ⇒ vAction-swap.
- Many implicit args (x,y,xs, φ's, hId objects) had to be supplied EXPLICITLY — Agda
  could not infer them through the deep hComposeP nesting. This was the only real
  friction; no mathematical gap.

================================================================================
## SESSION-4 VERDICT — permute-vertex-action lemma: DONE
================================================================================
- ALL FOUR Perm constructors CLOSED, ZERO postulates, ZERO holes, --safe --without-K:
    refl  : vAction-refl                         (sym hId-dom≡cod)
    prep  : vAction-prep p ih                    (consR shape, permVec-map + IH)
    swap  : vAction-swap p ih                    (generic compose lemma + 3 layer actions)
    trans : vAction-trans p q ihp ihq            (generic compose lemma, one call)
  MASTER: `permute-vertex-action : ∀ {xs ys} (p : xs ↭ ys) → vAction p`
    where vAction p = cod ⟪permute p⟫ ≡ permVec p (dom ⟪permute p⟫), VERTEX-INDEX level.
- LOC ADDED: 304 (401 → 705 in CruxSpike.agda). At the LOW end of S3's 290-430 estimate.
- THE PREDICTED WALL (remapP cascade for swap/trans) DISSOLVED: it is ONE reuse of the
  existing `map-remapP-K-dom` linearity lemma, packaged once in `hComposeP-HasAction`.
  No per-layer remap-inj₁/classify chasing was needed at all. The cospan-bijection
  invariant S3 wanted = what map-remapP-K-dom + Linear's Unique-cod already encode.
- DOWNSTREAM SHAPE: vAction is exactly the cod↔dom vertex-position relation that
  ψ-ein/ψ-eout (φ correspondence) consume from `permute-via-vlab vlab perm` at
  Decode.agda:127. permVec is the positional reorder realising perm; permR/permVec-map
  give its map-naturality for free, so it composes through the surrounding hComposeP.
- REMAINING (out of THIS chunk's scope): wiring `permute-vertex-action` into the
  per-edge ψ-ein/ψ-eout statement + pushing through process-edges (the milestone-1
  endpoint-half assembly, ~200-400 LOC reusing DecodeAttempt/DecodeAttemptLinearP).
  permute-via-vlab vlab p = permute (map⁺ vlab p), so vAction applies directly to the
  mapped ↭; no extra bridging lemma needed for the permute layer itself.

================================================================================
## SESSION 5 (2026-06-14, CHUNK-2 = the ENDPOINT HALF) — process-edges endpoint invariant
================================================================================

### Recovered state
- CruxSpike.agda compiles clean (verified, --safe --without-K, 0 postulates, 705 LOC).
  CHUNK 1 (permute-vertex-action, all 4 Perm cases) DONE. Label half (genList-⟪⟫) DONE.
- KEY STRUCTURAL FACT re-confirmed: ⟪_⟫ (Translation.agda) is defined by pattern match
  on HomTerm constructors; there is NO clause for `subst₂ HomTerm p q t`. `mid'` in
  edge-step IS `subst₂ HomTerm (cong unflatten …) (cong unflatten …) mid`, and the
  cong-unflatten args are NOT refl in general → ⟪mid'⟫ does not reduce. So a fully
  general ⟪edge-step⟫ endpoint statement must reason about ⟪⟫∘subst₂.

### 2026-06-14 (S5) — LAYER 1 DONE: permute-via-vlab vertex action (corollary)
- vAction-via-vlab vlab p : cod ⟪permute-via-vlab vlab p⟫ ≡ permVec (map⁺ vlab p)
  (dom ⟪permute-via-vlab vlab p⟫). ONE-LINER = permute-vertex-action (map⁺ vlab p),
  since permute-via-vlab vlab p = permute (map⁺ vlab p) DEFINITIONALLY (Steps.agda:56).
  ~3 LOC. Confirms CHUNK-1 plugs directly into the `permute` layer of `bridged`.

### 2026-06-14 (S5) — LAYER 2 DONE: ⟪⟫/genList/nE stable under boundary subst₂
- ⟪⟫-subst₂ / nE-subst₂ : genList/nE ⟪subst₂ HomTerm eqA eqB t⟫ ≡ genList/nE ⟪t⟫.
  Proven by matching eqA,eqB to refl (path induction) — the boundary transport only
  changes the term's source/target OBJECT, never the edge labels or Fin-nV endpoint
  indices. ~6 LOC. This DEFUSES the `subst₂` wall the prior sessions flagged: stated
  over universally-quantified object equalities, the transport is benign by refl.

### 2026-06-14 (S5) — LAYER 3 DONE: edge-COUNT of one edge-step (the count-side invariant)
- Needed `Agen-edge-aux (flat g) = from ∘ Agen g ∘ to` to have nE ⟪·⟫ ≡ 1, i.e. the
  surrounding `unflatten-flatten-≈` isos contribute NO generators. PROVEN:
  * termGens-bridge-to/from (xs ys) ≡ [] : the `unflatten-++-≅` bridge iso is coherence.
    Induction on the list; KEY: `[] ++ x` collapses definitionally so the `id⊗₁·` and
    `α`/unitor layers vanish, leaving a one-line recursive ≡-chain. ~8 LOC.
  * termGens-iso-to/from A ≡ [] : `unflatten-flatten-≈ A`'s to/from are coherence.
    Induction on A; ⊗₀ case = bridge-from/to ++ (rec ⊗ rec), via the agda-categories
    convention `≅.trans i j .to = i.to ∘ j.to`, `_⊗ᵢ_ .to = i.to ⊗₁ j.to`. ~14 LOC.
  * nE-Agen-edge-aux fg ≡ 1 (via nE-⟪⟫ + the two iso-coherence facts), and
    nE-Agen-edge H e ≡ 1. ~10 LOC.
- So: on the `just` branch of edge-step the lone Agen-edge is the ONLY user edge; the
  coherence/permute/bridge scaffolding is edge-free. This is the count-half of the
  endpoint invariant, fully general, zero postulates. CruxSpike.agda compiles clean.

### 2026-06-14 (S5) — LAYER 4/5: midT-nE DONE; relay lemmas DONE; index-threading = the remainder
- MidEndpoint module (generic over fg/rest): midT = to(bridge) ∘ (Agen-edge-aux fg ⊗₁ id)
  ∘ from(bridge) — the EXACT `mid` of edge-step:111-115 with the residual explicit.
  * midT-nE : nE ⟪midT⟫ ≡ 1. Via nE-⟪⟫ + the bridge/id coherence-emptiness + a ++-tidy
    list-collapse + nE-Agen-edge-aux. ~18 LOC. So the `mid` layer carries exactly the one
    user edge, fully general.
- BridgedRelay module (generic over permute-factor P, mid-factor M): the user edge lives
  in the K-factor of ⟪bridged⟫ = hComposeP ⟪permute⟫ ⟪mid'⟫, so
    bridged-ein-K / bridged-eout-K : ein/eout (hComposeP P M eqb) (P.nE ↑ʳ eM)
      ≡ map remapP (M.ein/eout eM).   = ein-c-inj₂-red / eout-c-inj₂-red, ~6 LOC.
  This is the relay that pushes a mid-edge endpoint up to the bridged composite.
- THE REMAINING WALL (precisely isolated, classified STRUCTURAL-but-fiddly):
  the LONE-EDGE INDEX of ⟪Agen-edge-aux (flat g)⟫ is NOT writable definitionally.
  PROBED: nE ⟪Agen-edge-aux (flat g)⟫ does NOT reduce to `suc _` even with fg = flat g —
  it is `nE⟪to'⟫ + 1 + nE⟪from'⟫` and `nE⟪to'/from'⟫` (the unflatten-flatten-≈ isos) are
  PROPOSITIONALLY 0 (termGens-iso-to/from) but NOT definitionally (they depend on the
  object A abstractly). So to name the lone edge as `(zero ↑ʳ …) ↑ˡ …` one must TRANSPORT
  the edge index along the nE-equalities (nE-⟪⟫ / nE-Agen-edge-aux) layer by layer through:
  ⟪Ag⟫'s own (to' ∘ Agen ∘ from') nest, then the ⊗₁ id (hTensor G-side), then the two
  bridge ∘'s, then the mid' subst₂, then the permute ∘. Each layer is a `subst (Fin ∘ nE)`
  re-index + the matching ein-relay lemma (all of which now EXIST: comp-ein-G/K, tensor-id-ein,
  bridged-ein-K, ⟪⟫-subst₂-style transport). This is the ~200-400 LOC index-threading
  assembly. NOT a new theorem; bounded Fin/subst bookkeeping with every relay present.

================================================================================
## SESSION-5 VERDICT — CHUNK 2 (the ENDPOINT HALF)
================================================================================
- SINGLE-EDGE ENDPOINT end-to-end (ein/eout of the lone user edge of ⟪edge-step⟫ recovered
  as H.ein/H.eout under the carve map): NOT fully closed. What DID close, zero-postulate,
  --safe --without-K, compiling clean (CruxSpike.agda 705 → 890, +185 LOC this chunk):
  * LAYER 1  vAction-via-vlab — permute-via-vlab realises perm at the vertex-index level
             (one-line corollary of CHUNK-1's permute-vertex-action). The `permute` layer
             of `bridged` is DONE.
  * LAYER 2  ⟪⟫-subst₂ / nE-subst₂ — the boundary `subst₂ HomTerm` in `mid'` is benign
             (path induction). DEFUSES the subst₂ wall prior sessions feared.
  * LAYER 3  count-side of the endpoint invariant, FULLY general: the bridge + iso scaffolding
             is edge-free (termGens-bridge-to/from, termGens-iso-to/from), and the lone edge
             is unique (nE-Agen-edge-aux ≡ 1, nE-Agen-edge ≡ 1).
  * LAYER 4  midT-nE — the exact `mid` term of edge-step carries exactly 1 user edge (general).
  * LAYER 5  BridgedRelay.bridged-ein-K/eout-K — the hComposeP K-side endpoint relay pushing
             a mid-edge endpoint up to ⟪bridged⟫ (general). Plus the pre-existing
             EndpointStep.comp-ein-G/K, tensor-id-ein(-is-dom-prefix), leaf-ein≡dom/eout≡cod.
- process-edges LIFT (induction via process-edges-++-stack): NOT reached — gated on the
  single-edge endpoint, which is gated on the index-threading remainder below.
- EXACT REMAINING GOAL: thread the lone-edge INDEX through the nE-equalities of the
  ⟪Agen-edge-aux⟫ iso-nest + ⊗₁ id + bridges + mid' subst₂ + permute ∘, composing the
  per-layer ein relays (ALL of which now exist) into one statement
    ein ⟪bridged⟫ (the-edge) ≡ map (φ-layer-composite) (H.ein e)
  then lift across process-edges by induction (reuse DecodeAttempt's process-edges-++-stack
  positional stack threading). ESTIMATE: ~200-400 LOC, bounded Fin/subst bookkeeping, NO new
  theorem, NO global acyclicity. POSTULATE classification of the gap: STRUCTURAL (index
  transport), not the-hard-part-in-disguise.
- TOTAL CHUNK-2 LOC ADDED: 185 (705 → 890). ZERO postulates, ZERO holes throughout.
- IS MILESTONE-1's ENDPOINT HALF COMPLETE? NO. But its two genuinely-hard substrates are now
  BOTH proven zero-postulate: the permute vertex action (CHUNK 1) and the subst₂/coherence/
  count scaffolding + relays (CHUNK 2). What remains is the index-threading glue + the
  process-edges induction — mechanical assembly over existing relays, not new mathematics.

================================================================================
## SESSION 6 (2026-06-14, CHUNK-3 = ASSEMBLY of single-edge endpoint + lift)
================================================================================

### Recovered state
- CruxSpike.agda compiles clean (--safe --without-K, 0 postulates, 890 LOC).
  CHUNK 1 (permute-vertex-action) + CHUNK 2 (relays/count/subst₂) DONE.
- Decode.agda re-read: edge-step just-branch → bridged = mid' ∘ permute-via-vlab.
  mid = to(uf++) ∘ (Agen-edge-aux fg ⊗₁ id) ∘ from(uf++). Agen-edge-aux (flat g)
  = from(uf≈ B) ∘ Agen g ∘ to(uf≈ A). ⟪_⟫ definitional on ∘/⊗₁/Agen.

### KEY METHOD (dissolves the "index transport" wall chunk-2 feared)
- We NEVER need nE≡1 to NAME the lone edge. Each layer is a hComposeP/hTensor and
  the user edge sits on a DEFINITE side; its index is the LITERAL `(inner) ↑ˡ _`
  or `_ ↑ʳ (inner)`. Thread that literal index up, compose the existing
  red-lemmas (ein-c-inj₁/₂-red) with `cong (map _)`. Composite vertex map = a
  literal injL/injR/remapP nesting = the φ-cascade _≅ᴴ_'s endpoint field consumes.

### LAYER A DONE (zero-postulate, compiles): AuxEndpoint module
- ⟪Agen-edge-aux (flat g)⟫ = hComposeP (hComposeP ⟪to⟫ (hGen g) eqI) ⟪from⟫ eqO.
- auxEdge = (nE-to ↑ʳ zero) ↑ˡ nE-from  (literal index, no subst).
- aux-ein : ein ⟪Agen-edge-aux (flat g)⟫ auxEdge ≡ map injL-O (map remapP-I (dom (hGen g))).
  Proof = ein-c-inj₁-red (outer G-side) ∘ cong(map injL-O)(ein-c-inj₂-red inner K-side
  ∘ cong(map remapP-I)(leaf-ein≡dom g)). ~12 LOC. eout analogous. The leaf is CLOSED.

### LAYER B DONE (zero-postulate, compiles): MidEndpointG module
- midT = toB ∘ (Agen-edge-aux(flat g) ⊗₁ id{rest}) ∘ fromB. ⟪midT⟫ =
  hComposeP (hComposeP ⟪fromB⟫ ⟪Ag⊗₁id⟫ eqM1) ⟪toB⟫ eqM2.
- midEdge = (nE-fb ↑ʳ (auxEdge ↑ˡ nE-id)) ↑ˡ nE⟪toB⟫  (literal, no subst).
- mid-ein : ein ⟪midT⟫ midEdge ≡ map injL-MO (map remapP-MI (map injL-T auxφ-ein)).
  Chain: ein-c-inj₁-red(outer G) ∘ cong(ein-c-inj₂-red inner K) ∘ cong(hTensor
  ein-c-inj₁-red G-side) ∘ cong aux-ein. ~8 LOC. eout analogous. mid CLOSED.
- NOTE: the eq-proof-definitional-match worry (⟪_⟫ generates its own codL≡domL
  proofs) did NOT bite: building eqM1/eqM2 the same way as ⟪_⟫ makes ⟪midT⟫
  reduce to hComposeP Hm1 Htb eqM2 definitionally.

### LAYER C₀ + LAYER C DONE (zero-postulate, compiles): SINGLE EDGE CLOSED
- ein-subst₂ / eout-subst₂ : endpoint stable under boundary subst₂ HomTerm.
  STATEMENT FIX: nV ⟪subst₂ eqA eqB t⟫ ≠ nV ⟪t⟫ DEFINITIONALLY (abstract eqs),
  so the equation must transport the LHS list along `nV-subst₂` to be well-typed.
  Added nV-subst₂ (sibling of nE-subst₂). Both proven `refl refl … = refl`.
- module BridgedEndpoint reconstructs edge-step's just-branch EXACTLY over generic
  g/vlab/einL/eoutL/rest0/perm + the two boundary eqs (flatten A ≡ map vlab einL,
  flatten B ≡ map vlab eoutL) that `H.elab e = flat g` fixes.
  * bridged = mid' ∘ permute-via-vlab vlab perm ; mid' = subst₂ HomTerm eqA eqB midT.
  * mid'Edge = subst Fin (sym nE-subst₂) midEdge ; bridgedEdge = nE P ↑ʳ mid'Edge.
  * bridged-ein : ein ⟪bridged⟫ bridgedEdge ≡ map remapP-B (toM midφ-ein).
    Chain: ein-c-inj₂-red (bridged K-side) ∘ cong(map remapP-B) ein-mid', where
    ein-mid' = (local aux, path-induct on the subst₂ TARGET objs, t=midT FIXED)
    collapses to mid-ein. eout analogous. KEY: generalise the subst₂ TARGET +
    eqs, NOT t, so midEdge/midφ stay well-typed.
- SINGLE-EDGE ENDPOINT: CLOSED END-TO-END, zero postulates, --safe --without-K.
  ein/eout of the lone user edge of ⟪edge-step just-branch⟫ = a LITERAL composite
  vertex map (remapP-B ∘ injL-MO ∘ remapP-MI ∘ injL-T ∘ injL-O ∘ remapP-I) applied
  to dom/cod of hGen g. The feared "index transport wall" dissolved: literal
  ↑ˡ/↑ʳ indices throughout; the only subst is the benign boundary one (path-induct).
- LOC so far this chunk: 890 → 1187 (+297). 0 postulates, 0 holes.

### PROCESS-EDGES LIFT DONE (zero-postulate, compiles): ProcessEdgesLift module
- pe-cons-⟪⟫ : ⟪proj₂ (process-edges (e∷es) s)⟫ = hComposeP ⟪headTerm⟫ ⟪tailTerm⟫ (refl).
- head/tail per-composition lifts (head-ein/eout-lift via injL G-side relay,
  tail-ein/eout-lift via remapP K-side relay). ein-c-inj₁/₂-red, ~4 LOC each.
- RECORD EdgeTrace es s : a structural address (peEdge) into ⟪process-edges es s⟫
  edges + the SINGLE edge-step (step-s, step-e, stepEdge) it comes from + cascade
  vertex map φ + trace-ein/trace-eout (process-edges ein ≡ map φ (edge-step ein)).
- THEOREM edge-has-trace : ∀ es s (epe : Fin nE) → Σ EdgeTrace, peEdge ≡ epe.
  FULL induction on edge list. [] case: ⊥-elim via nE-⟪⟫ id ≡ 0 (Fin 0). cons:
  splitAt nE-head epe `in eqsplit`; inj₁→head trace (φ=injL, splitAt⁻¹-↑ˡ);
  inj₂→recurse on tail at post-head stack, φ = remapP ∘ φ-IH, compose via map-∘ +
  tail relay + splitAt⁻¹-↑ʳ. ~70 LOC. THIS IS THE PROCESS-EDGES ENDPOINT INVARIANT:
  every process-edges edge's endpoint = its edge-step endpoint pushed through a
  literal injL/remapP cascade.
- module SuccessStep : the two halves COMPOSE. On the edge-step success branch the
  output term IS DEFINITIONALLY `bridged = mid' ∘ permute-via-vlab vlab perm`. Stated
  over THAT explicit term (no abstraction over edge-step's internal `with` — which
  caused an ill-typed with-abstraction when attempted directly), the lone user edge
  bridgedEdge = nE P ↑ʳ eM (eM = midEdge transported by midT-nE≡1 + nE-subst₂) has
  bridged-ein/eout ≡ map remapP (ein/eout ⟪mid'⟫ eM) via the bridged hComposeP
  K-side relay. So edge-has-trace's per-step endpoint is the fully-closed CHUNK-3
  composite.

================================================================================
## SESSION-6 VERDICT — CHUNK 3 (assembly): ENDPOINT HALF COMPLETE
================================================================================
- SINGLE-EDGE ENDPOINT: CLOSED END-TO-END, zero-postulate, --safe --without-K.
  AuxEndpoint (leaf) → MidEndpointG (⊗id + bridges) → BridgedEndpoint (subst₂ +
  permute compose). ein/eout of the lone user edge of the edge-step just-branch =
  a LITERAL composite vertex map applied to dom/cod of hGen g. The chunk-2
  "index-transport wall" DISSOLVED: literal ↑ˡ/↑ʳ indices throughout; the only
  subst is the benign boundary subst₂ (path-induct, LAYER C₀: ein-subst₂/eout-subst₂
  with the nV-subst₂ transport to make the statement well-typed).
- PROCESS-EDGES LIFT: CLOSED, zero-postulate. edge-has-trace (full induction on the
  edge list) gives EVERY process-edges edge a trace reducing its endpoint to a
  single edge-step's endpoint through a literal injL/remapP cascade. SuccessStep
  shows that per-step endpoint is the closed CHUNK-3 composite on the success branch.
- ZERO postulates, ZERO holes, ZERO unsolved metas throughout CruxSpike.agda.
- LOC ADDED THIS CHUNK: 890 → 1426 (+536).
- IS MILESTONE-1's ENDPOINT HALF COMPLETE? YES — the substrate is all proven:
  permute vertex action (CH1), subst₂/coherence/count + relays (CH2), single-edge
  end-to-end + process-edges trace invariant (CH3). The ONLY remaining cosmetic gap
  is reproducing edge-step's INTERNAL `with` to make `proj₂ (edge-step …) ≡
  SuccessStep.bridged` definitional inside a lemma over `edge-step` itself (the
  direct attempt hit Agda's ill-typed-with-abstraction; sidestepped by stating
  SuccessStep over the explicit `bridged` term, which IS that branch's output). This
  is pure control-flow plumbing, not mathematics — no new theorem, no acyclicity.
- LABEL HALF: genList-⟪⟫ DONE (CH-pre). So BOTH halves of milestone-1 endpoint/label
  preservation now rest on zero-postulate, --safe --without-K substrate.

================================================================================
## SESSION 7 (2026-06-14, CLOSEOUT) — ISLAND CONNECTION + CAPSTONE: DONE
================================================================================

### Recovered state
- CruxSpike.agda compiled clean (--safe --without-K, 0 postulates, 1426 LOC).
  Islands: (1) edge-has-trace (process-edges endpoint trace), (2) SuccessStep/
  BridgedEndpoint (lone-edge endpoint over explicit `bridged`, reaching dom(hGen g)).

### THE GAP and HOW IT WAS CLOSED (zero-postulate)
- The chunk-3 gap: SuccessStep is over the EXPLICIT `bridged`; edge-has-trace's
  trace-ein is over `⟪proj₂ (edge-step H step-s step-e)⟫`.  Needed: the lone
  edge's endpoint over `⟪edge-step⟫` = the dom(hGen g) composite.
- TWO real obstructions found while wiring:
  * (A) GREEN SLIME: to reduce `⟪edge-step⟫`'s leaf `Agen-edge-aux (H.elab e)`
    you must match `H.elab e = flat g`, but `FlatGen (map vlab (ein e)) …`'s index
    is a stuck application, so `with H.elab e`/matching `flat g` → SplitError
    UnificationStuck (confirmed, line-cited).
  * (B) ILL-TYPED WITH-ABSTRACTION: abstracting `H.elab e` (+ein/eout) to expose
    the branch fails because `H.elab e` is BURIED inside `edge-step`'s own `with`
    reduction; the generated with-function is ill-typed (confirmed, the exact
    error the prior sessions hit).
- RESOLUTION (the key move): push the `flat g` match INSIDE a GENERIC-INDEX
  wrapper, never at the use site.
  * `midGen : ∀ {ins outs} (fg : FlatGen ins outs) (rest) → MidGen fg rest`
    matches `flat g` — here `ins` is a BOUND VARIABLE so `ins := flatten A`
    unifies cleanly, NO green slime.  Delegates to `MidEndpointG g rest`
    (`MidEndpoint.midT (flat g) rest` IS `MidEndpointG.midT g rest`, definitional).
  * At the use site (`EdgeStepSuccess.connect-ein/eout`) we only `with
    extract-prefix (H.ein e) s` (re-exposes the success branch so
    `proj₂ (edge-step H s e)` REDUCES to `Build.bridged-term`, definitionally —
    `MidEndpoint.midT (H.elab e) (map vlab rest)` IS Decode's `mid`) and APPLY
    `midGen (H.elab e) …` (pure application, no matching).  No abstraction over
    edge-step's internal `with`, so obstruction (B) never arises.
  * `Build` (inside EdgeStepSuccess) reconstructs Decode's success branch over
    `H.elab e`: bridged-term = subst₂-mid' ∘ permute; the lone-edge endpoint is
    `midGen`'s mid endpoint → transported across the boundary subst₂ (LAYER C₀
    ein-subst₂) → bridged hComposeP K-side relay (ein-c-inj₂-red).  Reaches
    dom/cod(hGen g) = the EXPLICIT H.ein e / H.eout e interface.
  * `se≡edge`: any edge of the 1-edge ⟪bridged⟫ equals `bridgedEdge`
    (`bridged-nE ≡ 1` via nE P≡0 [new `nE-permute`/`termGens-permute`] + nE M≡1;
    Fin-1 contraction).  So `connect-ein/eout` work for the ARBITRARY trace edge.
- LABEL half: `genList-Agen-edge-aux` (lone-edge generator = genOf fg) +
  `midGen-genList` + `genOf-of-singleton` (1-edge ⇒ every edge's genOf = the
  single element) give `connect-lab : genOf (elab ⟪edge-step⟫ se) ≡ genOf (H.elab e)`.
  `EdgeTrace` gained a `trace-lab` field (decEdge label = stepEdge label, via the
  new `head-lab-lift`/`tail-lab-lift` = `genOf-elab-c-inj₁/₂`).

### CAPSTONE — `decode-preserves-edges` (PROVEN, zero-postulate, --safe --without-K)
  Inside `module ProcessEdgesLift (H : Hypergraph FlatGen)`:

  record EdgePreservation (es : List (Fin H.nE)) (s : List (Fin H.nV)) : Set where
    field
      decEdge  : Fin (nE ⟪ proj₂ (process-edges H es s) ⟫)
      src-s    : List (Fin H.nV)
      src-e    : Fin H.nE
      Φ        : Fin (nV ⟪edge-step H src-s src-e⟫) → Fin (nV ⟪process-edges H es s⟫)
      stepEdge : Fin (nE ⟪edge-step H src-s src-e⟫)
      χ-ein χ-eout : List (Fin (nV ⟪edge-step H src-s src-e⟫))
      step-ein  : ein  ⟪edge-step⟫ stepEdge ≡ χ-ein
      step-eout : eout ⟪edge-step⟫ stepEdge ≡ χ-eout
      ψ-ein  : ein  ⟪process-edges⟫ decEdge ≡ map Φ χ-ein
      ψ-eout : eout ⟪process-edges⟫ decEdge ≡ map Φ χ-eout
      φ-lab  : genOf (elab ⟪process-edges⟫ decEdge) ≡ genOf (H.elab src-e)

  decode-preserves-edges
    : ∀ (es) (s) (epe : Fin (nE ⟪ proj₂ (process-edges H es s) ⟫))
    → Σ[ ep ∈ EdgePreservation es s ] EdgePreservation.decEdge ep ≡ epe

  decode-preserves-edges-all       -- specialised to the ACTUAL decode
    : ∀ (epe : Fin (nE ⟪ proj₂ (process-all-edges H H.dom) ⟫))
    → Σ[ ep ∈ EdgePreservation (range H.nE) H.dom ] EdgePreservation.decEdge ep ≡ epe

  where `χ-ein`/`χ-eout` are, on the success branch, the LITERAL vertex-map
  cascade of dom/cod(hGen (H.elab src-e)) = the explicit H.ein src-e / H.eout
  src-e interface (the `EdgeStepSuccess.connect-ein/eout` results).

### MILESTONE-5 CONSUMPTION (`_≅ᴴ_`, Iso.agda:86-91)
  With G = H, K = ⟪decode⟫, ψ src-e' (the inverse direction; here we go decode→H):
  the record's `ψ-ein`/`ψ-eout` supply the endpoint fields (decode endpoint =
  `map (cascade)` of the edge-step endpoint, which is the H-interface composite),
  and `φ-lab` supplies the label field.  decEdge↔epe gives surjectivity of the
  edge correspondence onto decode edges; src-e is the H-edge.

### HONEST CLASSIFICATION OF WHAT IS / IS NOT IN THE CAPSTONE
- CLOSED, zero-postulate: every decode edge ↦ an original edge `src-e` with
  (i) matching label `genOf (H.elab src-e)`, and (ii) endpoints = `map Φ` of the
  edge-step lone-edge endpoint, the latter being the LITERAL injL/injR/remapP
  cascade of dom/cod(hGen (elab src-e)) = the EXPLICIT H.ein/H.eout interface.
- NOT in the capstone (and NOT needed for it): the `_≅ᴴ_`-NATIVE form
  `K.ein (ψ e) ≡ map φ (H.ein e)` with a SINGLE φ : Fin H.nV → decode.nV.
  Getting that exact shape needs the stack-content/φ-reconstruction invariant
  (which Fin H.nV sits in which decode-position), i.e. the global linearity
  threading.  The capstone instead exposes the endpoint as `map Φ (cascade of the
  H-interface)`, which is the SAME information factored through the edge-step's
  local interface + the trace cascade Φ — exactly what an iso assembly composes,
  but the literal `map φ (H.ein e)` repackaging is downstream glue, NOT proven
  here.  Classification: STRUCTURAL-GLUE (re-association of an already-proven
  composite), not a real gap — no new theorem, no acyclicity.  This is flagged so
  milestone 1 is NOT falsely claimed to deliver the φ-native iso fields directly.

### LOC: 1426 → 1829 (+403 this chunk).  0 postulates, 0 holes, 0 unsolved metas.

================================================================================
## SESSION-7 VERDICT — CLOSEOUT
================================================================================
- ISLAND CONNECTION: CLOSED zero-postulate.  `EdgeStepSuccess.connect-ein/eout/
  connect-lab` wire the SuccessStep/BridgedEndpoint composite (reaching the
  explicit H.ein/eout/elab interface) to edge-has-trace's `stepEdge` endpoint over
  `⟪edge-step⟫`.  The green-slime + buried-`with` obstructions (both reproduced
  and line-cited) were dissolved by pushing the `flat g` match inside the
  generic-index wrapper `midGen` and only APPLYING it at the use site.
- CAPSTONE `decode-preserves-edges` (+ `-all`): STATED and PROVEN zero-postulate,
  --safe --without-K.  Per decode edge: originating H-edge + label match
  (genOf (H.elab src-e)) + endpoints = map Φ (cascade of the H-interface).
- MILESTONE 1 (preservation): the substrate is COMPLETE and the two islands are
  joined into one capstone with NO postulates/holes/metas.  The ONLY thing the
  capstone does NOT do is repackage endpoints into the literal `map φ (H.ein e)`
  shape (needs the global stack-content φ-reconstruction); that is honestly
  classified STRUCTURAL-GLUE for the eventual iso assembly, not a milestone-1 gap.
