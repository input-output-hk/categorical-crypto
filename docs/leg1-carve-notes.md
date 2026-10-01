# LEG 1 (carve combinatorics) — proof notes

> **Status note (2026-09-02).** A dated spike log. `Leg1Carve.agda` lives in `spikes/`, never in `src/`; read every path and name below as of its own entry's date.

GOAL: `H'[h↦⟪lᵗ⟫] ≅ᴴ ⟪s⟫`. New module src/Leg1Carve.agda, --safe --without-K.
Sub-proofs: (a) kahn output ↭ (holeEdge ∷ complement); (b) carve+substitute = id up to perm + emb.

## 2026-06-14

- Read findiso-witness-plan.md LEG1 section, Deep.agda Build (complement/holeEdge/kahn/assemble/holeGraph),
  SubMatch `_↪ᴴ_` record, Iso.agda `_≅ᴴ_` + refl/sym/trans, Core Hypergraph, DeepProv BuildO/pairsO mirror.
- KEY structures:
  - `_≅ᴴ_` (Iso.agda 64-100): φ/φ⁻¹ vtx bij + laws, ψ/ψ⁻¹ edge bij + laws, φ-lab, ψ-ein/eout, φ-dom/cod,
    atom-ein/eout, ψ-elab (subst₂ along atoms).
  - `_↪ᴴ_` (SubMatch 71-107): φ inj (φ⁻¹ partial, φ-inv), ψ inj (ψ-inv), φ-lab, ψ-ein/eout, atom-ein/eout, ψ-elab.
  - Build.Edge: ins/outs : List(Fin S.nV); lab : F⁺.FlatGen ... . complement = keep(range S.nE) skipping ψ-image.
    holeEdge = edge boundary-dom boundary-cod (subst hole!). kahn = fuel-bounded findReady-removal. assemble keeps
    nV=S.nV, vlab=S.vlab, dom/cod=S.dom/cod.
- stdlib `Data.List.Relation.Binary.Permutation.Propositional` is --safe (cubical-compatible). Has
  refl/prep/swap/trans, ↭-sym, ↭-trans, and `shift : xs ++ [v] ++ ys ↭ v ∷ xs ++ ys` — exactly findReady's shape.

### Architecture decision
- Sub-proof (a) kahn-permutation is the cleanest self-contained deliverable: prove
  `kahn fuel avail pending ≡ just out → out ↭ pending`. findReady extracts the matched edge from the middle
  (order-preserving on the rest) ⇒ `e ∷ rest ↭ pending`; then induct. Will REDEFINE kahn/findReady/consume/remove1
  in Leg1Carve (Deep's are `private`) — verbatim copies, label-agnostic over an arbitrary Edge type.

### (a) DONE — kahn-permutation
- `src/Leg1Carve.agda` module `KahnPerm {V} _≟V_ {E} eins eouts`: verbatim label-agnostic copies of
  remove1/consume/findReady/kahn. COMPILES --safe --without-K, ZERO postulates/holes.
- `findReady-↭ : findReady avail pending ≡ just (e,av,rest) → e ∷ rest ↭ pending` (~12 LOC body).
  Proof: ready-now case → ↭-refl; skip case → `↭-trans (swap r x ↭-refl) (prep x IH)`.
- `kahn-↭ : kahn fuel avail pending ≡ just out → out ↭ pending` (~10 LOC). Induct on fuel;
  `↭-trans (prep e IH) (findReady-↭ ...)`.
- Tactics that worked: `with f x in eq` idiom to pin the scrutinee (avoids blocked-meta on Maybe.map);
  `with () ← eq` to discharge nothing≡just; helper `just-inj`, `map-just-inv` (latter ended unused, kept).
- ~95 LOC so far for part (a) incl. function copies.

### (b) core DONE — partition perm + ↭→index-bijection bridge
- `module Partition {I J} (cls : I → Maybe J)`: `imagePart`/`compPart` (= ψ-image / Build.complement walk),
  `partition-↭ : imagePart es ++ compPart es ↭ es` (~6 LOC). just-head→prep, nothing-head→shift+prep.
- `module PermIdx {A}`: propositional, ≡-based reconstruction of stdlib's setoid `onIndices`/`onIndices-lookup`
  (stdlib only proves these for the Setoid permutation; ≅ᴴ wants plain Fin→Fin funcs with ≡ laws):
  - `toIdx : xs ↭ ys → Fin(length xs) → Fin(length ys)` (refl/prep/swap/trans, mirrors Homogeneous.onIndices)
  - `toIdx-lookup : lookup ys (toIdx p i) ≡ lookup xs i`   ← the law ≅ᴴ ψ-ein/eout/elab rest on
  - `fromIdx p = toIdx (↭-sym p)`; `toIdx-fromIdx`/`fromIdx-toIdx` two-sided inverse laws (↭-sym structural ⇒
    straight induction). Gives ≅ᴴ ψ/ψ⁻¹/ψ-left/ψ-right.
  ALL COMPILE --safe --without-K, ZERO postulates/holes.
- This is the genuinely-reusable crux: any "same vertices, edges permuted" pair is now one lemma from ≅ᴴ.

### Remaining for full LEG 1 assembly (next)
- `permEdges-≅ᴴ` capstone: G,K same nV/vlab/dom/cod; K.nE=length idx; idx ↭ range G.nE;
  K.ein i = G.ein (lookup idx i) etc ⇒ G ≅ᴴ K. Edge bij = toIdx/fromIdx of (idx ↭ range), φ=id.
  Then instantiate: G=⟪s⟫=S, K = substituted graph (complement++ψ-image via emb), idx from partition-↭+kahn-↭.
- The cross-signature hole-substitution (sig⁺ relabel/retract, hole atom subst₂) to define the substituted
  graph object over `sig` is the remaining PLUMBING (orthogonal to the new combinatorics).

### (b) capstone DONE — permuted-edge ≅ᴴ
- `module PermEdges`, inner `module _ {X}{Gen}`:
  - `reEdge G nE' ein' eout' elab'`: hypergraph with G's vertices/vlab/dom/cod but a fresh edge family
    (= shape of Deep.Build.assemble, which keeps nV/vlab/dom/cod from S).
  - `reEdge-≅ᴴ`: given an edge bijection ψ/ψ⁻¹ (+laws) and ON-THE-NOSE endpoint/label agreement
    (ein'(ψ e)≡ein G e, eout', and elab up to subst₂ along the derived atom eqs), produces `G ≅ᴴ reEdge…`.
    φ=id ⇒ all vertex/boundary laws refl/map-id. ~12-field record, ZERO holes.
  - `permIdx-≅ᴴ` (inner `module _ (G) (idx) (p : idx ↭ allFin (nE G))`): the PRODUCER. K=reEdge with
    K.ein i = G.ein (lookup idx i) etc. Edge bij = PermIdx.toIdx/fromIdx of (↭-sym p) composed with the
    `allFin` length cast (cast handled via stdlib length-tabulate/lookup-tabulate/cast-involutive).
    ein/eout/elab-ok all from `toIdx-lookup` + `lookup-tabulate id` (range-id) + subst₂-collapse-on-refl.
    ALL COMPILES --safe --without-K, ZERO postulates/holes.
- NET: any "same vertices, edges = original permuted via idx, idx ↭ allFin" pair → `≅ᴴ`, in ONE call.
  This is the complete GENERAL LEG-1 machinery (the genuinely-new combinatorics of (a)+(b)).

### Final wiring (remaining) — instantiate at Deep.At.Build + SubMatch.emb
- Need: idx : List(Fin S.nE) for the carved+substituted edge order, and `idx ↭ allFin S.nE`.
  From partition-↭ (cls=ψ⁻¹ over allFin S.nE) get `imagePart++compPart ↭ allFin S.nE`; compPart = the
  S-indices of Build.complement; imagePart = ψ-image S-indices = (substituting hole back) ⟪lᵗ⟫'s edges.
  kahn-↭ then reorders the assembled list (still ↭). Compose ⇒ `idx ↭ allFin S.nE`. Feed permIdx-≅ᴴ.
- The ONLY remaining gap to the literal `H'[h↦⟪lᵗ⟫] ≅ᴴ ⟪s⟫` statement is the cross-signature
  hole-substitution OBJECT: H' lives over sig⁺ (relabel'd complement + hole!); the substituted graph must
  be re-expressed over `sig` with the hole edge replaced by ⟪lᵗ⟫'s edges (= emb ψ-image, S.elab labels).
  This is signature PLUMBING (retract/relabel inverse on h-free edges + hole-atom subst₂), orthogonal to
  the new combinatorics, NOT YET written. Classification: STRUCTURAL (no hard math), ~150-300 LOC.

### Wiring + Closure DONE — end-to-end index permutation
- `module Wiring {A}`: `concat-↭` (concat preserves ↭; swap case = stdlib `shifts`), `concatMap-↭`. Clean.
- `module Closure {I J} (cls)`: models a carve item as `Maybe I` (nothing=hole, just c=kept complement edge).
  - `expand image`: hole↦image (=⟪lᵗ⟫'s ψ-image S-indices), just c↦[c].
  - `concatMap-just`/`expand-hole`: substituting the hole in `nothing ∷ map just comp` = `image ++ comp`.
  - `closure`: assembled ↭ (nothing ∷ map just comp)  →  image++comp ↭ es  →  concatMap (expand image) assembled ↭ es.
    Composes Wiring.concatMap-↭ + expand-hole + the partition. THE index-level LEG-1 permutation.
  - `closure-partition`: specialise image=imagePart, comp=compPart, premise = partition-↭.
  ALL COMPILES --safe --without-K, ZERO postulates/holes.

## FINAL STATUS (2026-06-14)
- src/Leg1Carve.agda: 523 LOC, COMPILES clean --safe --without-K, ZERO postulates / ZERO holes
  (verified by grep for postulate/{!/?/TODO/trustMe → none).
- (a) kahn-permutation: DONE (KahnPerm.kahn-↭ + findReady-↭).
- (b) carve=id-up-to-perm: combinatorial CORE + capstone DONE:
    * Partition.partition-↭ (stable partition = permutation)
    * PermIdx: ↭ → Fin-index bijection (toIdx/fromIdx) + lookup law + 2-sided inverse (≡-based onIndices)
    * PermEdges.reEdge-≅ᴴ + permIdx-≅ᴴ: from `idx ↭ allFin (nE G)` produce `G ≅ᴴ (G re-edged by idx)`.
      THIS IS THE ≅ᴴ FOR LEG 1, modulo the substituted-graph object.
    * Wiring.concatMap-↭ + Closure.closure: the end-to-end index permutation `substituted-order ↭ allFin (nE S)`.
- _≅ᴴ_ assembled? YES at the general level (permIdx-≅ᴴ produces the full 15-field record, φ=id).
- REMAINING for the LITERAL `H'[h↦⟪lᵗ⟫] ≅ᴴ ⟪s⟫`: only the cross-signature hole-substitution OBJECT — re-
  expressing H' (over sig⁺, relabel'd complement + hole!) as a `reEdge ⟪s⟫ …` over `sig` with the hole edge
  replaced by emb's ψ-image (S.elab labels). Requires: retract/relabel-inverse on h-free edges (ExtendSig)
  + the hole-atom subst₂ alignment. Classification: STRUCTURAL signature PLUMBING, no new math; est ~150-300 LOC;
  NOT written (out of this session's budget). Everything the combinatorics needs to FEED it is proven.
- Instantiation note: instantiate KahnPerm at V=Fin S.nV (≟F), Closure/Partition at I=Fin S.nE, J=Fin L.nE,
  cls=emb.ψ⁻¹; the carve's `complement` index-projection = compPart (emb.ψ⁻¹) (allFin S.nE); kahn output feeds
  Closure.closure-partition; result `idx ↭ allFin S.nE` feeds PermEdges.permIdx-≅ᴴ at G=⟪s⟫.
