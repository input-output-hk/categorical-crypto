{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- Provenance-guided gate #1 finder for the deep-rewrite engine.  It derives
-- the `findIso ⟪ s ⟫ ⟪ deepFrame s lᵗ lᵗ n _ ⟫` witness from the carve's
-- PROVENANCE rather than re-discovering it by backtracking DFS: it tracks
-- which originating ⟪s⟫-edge each carved frame edge came from, and uses that
-- to predict the (H-edge , J-edge) pairing directly.  Every candidate is
-- still gated end-to-end by `Verify.verify`, so the result is sound and
-- fail-closed: a wrong prediction fails the gate, it never yields a bad iso.
--
-- Edge-ordering facts the prediction relies on:
--   * `⟪ g ∘ f ⟫ = hComposeP ⟪f⟫ ⟪g⟫` enumerates f's edges then g's
--     (PrunedCompose.ein-c via `splitAt G.nE`), `hTensor` left then right,
--     coherence terms are edge-free.
--   * `decode-attempt H'` emits exactly one `Agen` per H'-edge, in H' edge
--     (= kahn) order; `focusAt` and `retract` are structure-preserving.
--   * Hence ⟪ post ∘ (id{k} ⊗₁ mid) ∘ pre ⟫'s edges are, in order:
--       [kahn edges before the hole] ++ [⟪mid⟫'s edges] ++ [kahn after].
--   * Deep.Build's `complement` walks `range S.nE` skipping ψ-image edges,
--     so every carved edge has a known originating ⟪s⟫-edge, and the hole's
--     slot expands to the embedding ψ's image (⟪lᵗ⟫-edge order).
--
-- `kahn` only inspects edge endpoints, never labels, so the provenance
-- mirror below runs on a label-free edge record and needs no sig⁺ machinery.
--
-- The guided pipeline is: seed (interfaces) → fold `tryEdge` over the
-- provenance-predicted edge pairs (deterministic, branching factor 1; this
-- also propagates the vertex bijection through `pairUp`) → Verify.verify.
--------------------------------------------------------------------------------

open import Categories.APROP.Hypergraph.Solver.Signature using (APROPSignatureDec)

module Categories.APROP.Hypergraph.Solver.DeepProv (sig-dec : APROPSignatureDec) where

open APROPSignatureDec sig-dec using (sig)

open import Categories.APROP.Hypergraph.Core using (Hypergraph)
open import Categories.APROP.Hypergraph.FromAPROP sig using (FlatGen; range)
open import Categories.APROP.Hypergraph.Iso using (_≅ᴴ_; sym-≅ᴴ; trans-≅ᴴ)
open import Categories.APROP.Hypergraph.Tabulate using (tabH; tab-≅ᴴ)
open import Categories.APROP.Hypergraph.Solver.PBij using (emptyBij)
open import Categories.APROP.Hypergraph.Solver.SubMatch sig-dec
  using (subMatchAll; _↪ᴴ_)
open import Categories.APROP.Hypergraph.Solver.Seed sig-dec
  using (seedFromInterfaces)
open import Categories.APROP.Hypergraph.Solver.Match sig-dec
  using (tryEdge; VertexBij; EdgeBij)
open import Categories.APROP.Hypergraph.Solver.Verify sig-dec
  using (module Verify)

open import Data.Fin using (Fin; toℕ)
import Data.Fin as Fin
open import Data.Fin.Properties using () renaming (_≟_ to _≟F_)
open import Data.List.Base using (List; []; _∷_; _++_; map; length)
open import Data.Maybe.Base using (Maybe; just; nothing; _>>=_)
import Data.Maybe.Base as Maybe
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Product using (_×_; _,_)
open import Relation.Nullary using (yes; no)

--------------------------------------------------------------------------------
-- Bounds-checked ℕ → Fin conversion (lets provenance pairs live at ℕ, so
-- they need not mention the frame graph's edge count in their type).

toFin? : (n : ℕ) → ℕ → Maybe (Fin n)
toFin? zero    _       = nothing
toFin? (suc n) zero    = just Fin.zero
toFin? (suc n) (suc m) = Maybe.map Fin.suc (toFin? n m)

--------------------------------------------------------------------------------
-- Provenance mirror of Deep.At.Build: same complement walk, same kahn, but
-- carrying each carved edge's originating S-edge instead of its label.

module BuildO (L S : Hypergraph FlatGen) (emb : L ↪ᴴ S) where
  private
    module L = Hypergraph L
    module S = Hypergraph S
    open _↪ᴴ_ emb using (ψ; ψ⁻¹; boundary-dom; boundary-cod)

  record EdgeO : Set where
    constructor edgeO
    field
      ins outs : List (Fin S.nV)
      origin   : Maybe (Fin S.nE)     -- `nothing` = the hole edge

  complementO : List EdgeO
  complementO = keep (range S.nE)
    where
      keep : List (Fin S.nE) → List EdgeO
      keep []       = []
      keep (e ∷ es) with ψ⁻¹ e
      ... | just _  = keep es
      ... | nothing = edgeO (S.ein e) (S.eout e) (just e) ∷ keep es

  holeEdgeO : EdgeO
  holeEdgeO = edgeO boundary-dom boundary-cod nothing

  -- kahn mirror (verbatim from Deep.agda, minus labels).
  private
    remove1 : Fin S.nV → List (Fin S.nV) → Maybe (List (Fin S.nV))
    remove1 v []       = nothing
    remove1 v (w ∷ ws) with v ≟F w
    ... | yes _ = just ws
    ... | no  _ = Maybe.map (w ∷_) (remove1 v ws)

    consume : List (Fin S.nV) → List (Fin S.nV) → Maybe (List (Fin S.nV))
    consume []       avail = just avail
    consume (v ∷ vs) avail = remove1 v avail >>= consume vs

    findReady : List (Fin S.nV) → List EdgeO
              → Maybe (EdgeO × List (Fin S.nV) × List EdgeO)
    findReady avail []       = nothing
    findReady avail (e ∷ es) with consume (EdgeO.ins e) avail
    ... | just avail' = just (e , avail' , es)
    ... | nothing     =
          Maybe.map (λ { (r , av , rest) → (r , av , e ∷ rest) })
                    (findReady avail es)

    kahn : ℕ → List (Fin S.nV) → List EdgeO → Maybe (List EdgeO)
    kahn _          _     []      = just []
    kahn zero       _     _       = nothing
    kahn (suc fuel) avail pending with findReady avail pending
    ... | nothing                  = nothing
    ... | just (e , avail' , rest) =
          Maybe.map (e ∷_) (kahn fuel (avail' ++ EdgeO.outs e) rest)

  -- The carved graph's per-edge origins, in its (kahn) edge order.
  originsO : Maybe (List (Maybe (Fin S.nE)))
  originsO = Maybe.map (map EdgeO.origin) (kahn (suc (length pending)) S.dom pending)
    where pending = holeEdgeO ∷ complementO

  -- Predicted (H-edge , J-edge) index pairs for H = S, J = ⟪frame⟫:
  -- walk the origin list with a running J-index; the hole slot expands to
  -- the embedding's ψ-image in ⟪lᵗ⟫-edge order (= ⟪mid⟫'s edges).
  private
    midPairs : ℕ → List (ℕ × ℕ)
    midPairs k = map (λ i → toℕ (ψ i) , k + toℕ i) (range L.nE)

    walk : ℕ → List (Maybe (Fin S.nE)) → List (ℕ × ℕ)
    walk k []             = []
    walk k (just o  ∷ os) = (toℕ o , k) ∷ walk (suc k) os
    walk k (nothing ∷ os) = midPairs k ++ walk (k + L.nE) os

  pairsO : Maybe (List (ℕ × ℕ))
  pairsO = Maybe.map (walk 0) originsO

--------------------------------------------------------------------------------
-- Predicted pairs for the FIRST embedding whose carve succeeds (mirrors
-- deepFocAll's retry).  deepFocAll may additionally skip an embedding on a
-- later decode/focus/glue failure that this mirror does not see; in that case
-- the predicted pairs no longer match and the downstream Verify gate fails
-- closed.

pairsFor : (L S : Hypergraph FlatGen) → Maybe (List (ℕ × ℕ))
pairsFor L S = first (subMatchAll L S)
  where
    first : List (L ↪ᴴ S) → Maybe (List (ℕ × ℕ))
    first []         = nothing
    first (emb ∷ es) with BuildO.pairsO L S emb
    ... | just ps = just ps
    ... | nothing = first es

--------------------------------------------------------------------------------
-- Guided findIso: seed from the interfaces, then a single deterministic
-- pass folding `tryEdge` over the predicted pairs (this both checks edge
-- compatibility and propagates the vertex bijection), then full Verify.
-- No backtracking search.

findIsoGuided : (H J : Hypergraph FlatGen) → List (ℕ × ℕ) → Maybe (H ≅ᴴ J)
findIsoGuided H J ps =
  seedFromInterfaces H J  >>= λ φ₀ →
  goEdges φ₀ emptyBij ps  >>= λ { (φ , ψ) →
  Verify.verify H J φ ψ }
  where
    goEdges : VertexBij H J → EdgeBij H J → List (ℕ × ℕ)
            → Maybe (VertexBij H J × EdgeBij H J)
    goEdges φ ψ []                = just (φ , ψ)
    goEdges φ ψ ((e , e') ∷ rest) =
      toFin? (Hypergraph.nE H) e  >>= λ eF →
      toFin? (Hypergraph.nE J) e' >>= λ e'F →
      tryEdge H J φ ψ eF e'F >>= λ { (φ' , ψ') → goEdges φ' ψ' rest }

--------------------------------------------------------------------------------
-- End-to-end gate #1 replacement: S = ⟪ s ⟫, J = ⟪ deepFrame s lᵗ lᵗ n _ ⟫,
-- L = ⟪ lᵗ ⟫.  Sound by construction: Verify gates every candidate.

findIsoFromCarve : (S J L : Hypergraph FlatGen) → Maybe (S ≅ᴴ J)
findIsoFromCarve S J L = pairsFor L S >>= findIsoGuided S J

--------------------------------------------------------------------------------
-- Tabulated variant: run BOTH the provenance computation and the guided
-- pass + Verify on `tabH`-tabulated graphs (vector-backed fields, each
-- original field value computed at most once), and transport the iso back
-- along `tab-≅ᴴ` exactly as `findIsoᵀ` does.  `tabH` preserves nV/nE and
-- index sets, so the ℕ-pairs are unaffected.

findIsoFromCarveᵀ : (S J L : Hypergraph FlatGen) → Maybe (S ≅ᴴ J)
findIsoFromCarveᵀ S J L =
  Maybe.map
    (λ iso → trans-≅ᴴ (sym-≅ᴴ (tab-≅ᴴ S)) (trans-≅ᴴ iso (tab-≅ᴴ J)))
    (go (tabH S) (tabH J) (tabH L))
  where
    -- tabbed graphs bound ONCE as arguments (shared thunks).
    go : (Sᵗ Jᵗ Lᵗ : Hypergraph FlatGen) → Maybe (Sᵗ ≅ᴴ Jᵗ)
    go Sᵗ Jᵗ Lᵗ = pairsFor Lᵗ Sᵗ >>= findIsoGuided Sᵗ Jᵗ
