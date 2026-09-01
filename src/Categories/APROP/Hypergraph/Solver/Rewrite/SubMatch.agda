{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- Sub-hypergraph matching (TensorRocq §4.2, the matcher half of DPO
-- rewriting).  Where `findIso` decides a *full* isomorphism `H ≅ᴴ J`, this
-- module finds an *embedding* of a (rule-LHS) hypergraph `L` as a
-- sub-hypergraph of a (target) hypergraph `S`:
--
--     subMatch : (L S : Hypergraph FlatGen) → Maybe (L ↪ᴴ S)
--
-- An embedding is a vertex map `φ` together with the partial inverse `ψ⁻¹` of
-- the edge map — exactly what carving the rewrite context needs: delete the
-- `ψ`-image edges (the `e` with `ψ⁻¹ e ≡ just _`) and expose the boundary
-- vertices `map φ L.dom` / `map φ L.cod` as new interface holes.
--
-- Unlike `_≅ᴴ_`, `_↪ᴴ_` carries no proofs: it is the *raw output of the
-- search*, verified downstream.  The search is injective and label-preserving
-- by construction (`extend-bij` refuses conflicts, `tryEdge` culls on the edge
-- label), and there is no consumer of a proof that it is: `Deep.Build`
-- re-decides the one boundary fact it needs, and the engine's soundness rests
-- solely on the `findIso` re-check in `rewriteH!`.  A rogue candidate can
-- therefore only cost a wasted rewrite attempt, never unsoundness.
--
-- The search reuses the full-iso machinery verbatim: `searchIso` already tries
-- *every* S-edge for L's first edge (it only looked interface-pinned because
-- `findIso` pre-seeds the boundary).  We start from the *empty* vertex seed;
-- the sole remaining check is forward-totalisation of `φ` (the edge map is
-- total by the search's own exit condition).
--
-- NB: an `L` with no edges (e.g. a pure identity/swap LHS) has no edge
-- constraints to bind its vertices, so forward-totalisation fails and
-- `subMatch` returns `nothing` for it.  Rule LHSs always carry generator
-- content, so this is not a limitation in practice.
--------------------------------------------------------------------------------

open import Categories.APROP.Hypergraph.Solver.Signature using (APROPSignatureDec)

module Categories.APROP.Hypergraph.Solver.Rewrite.SubMatch (sig-dec : APROPSignatureDec) where

open APROPSignatureDec sig-dec
open import Categories.APROP.Hypergraph.Model.Core using (Hypergraph)
open import Categories.APROP.Hypergraph.Model.FromAPROP sig using (FlatGen)
open import Categories.APROP.Hypergraph.Solver.Match.PBij
  using (PBij; forward; backward; emptyBij; totalise)
open import Categories.APROP.Hypergraph.Solver.Match.Search sig-dec using (searchAll-default)

open import Data.Fin using (Fin)
open import Data.List.Base using (List; head; map; mapMaybe)
open import Data.Maybe.Base using (Maybe; just; _>>=_)
open import Data.Product using (_,_)

--------------------------------------------------------------------------------
-- The embedding relation `L ↪ᴴ S`.

module _ {X : Set} {Gen : List X → List X → Set} where

  infix 4 _↪ᴴ_

  record _↪ᴴ_ (L S : Hypergraph Gen) : Set where
    private
      module L = Hypergraph L
      module S = Hypergraph S
    field
      φ   : Fin L.nV → Fin S.nV
      ψ⁻¹ : Fin S.nE → Maybe (Fin L.nE)

    -- The boundary (cut) vertices of S that are the images of L's interface;
    -- a caller carves the rewrite context around these.
    boundary-dom : List (Fin S.nV)
    boundary-dom = map φ L.dom

    boundary-cod : List (Fin S.nV)
    boundary-cod = map φ L.cod

--------------------------------------------------------------------------------
-- Read a search-produced `(φB, ψB)` off as an `L ↪ᴴ S`.  Only `φ` needs a
-- check: it must be defined at every L-vertex, which for an edge-free `L` it
-- is not (see the NB above).

verifySub : (L S : Hypergraph FlatGen)
          → PBij (Hypergraph.nV L) (Hypergraph.nV S)
          → PBij (Hypergraph.nE L) (Hypergraph.nE S)
          → Maybe (L ↪ᴴ S)
verifySub L S φB ψB =
  totalise (forward φB) >>= λ φ → just record { φ = φ ; ψ⁻¹ = backward ψB }

--------------------------------------------------------------------------------
-- Top-level: search (no interface seed) then verify.
--
-- `subMatchAll` enumerates every verified embedding, in the DFS's order.
-- Consumers with acceptance criteria beyond the embedding itself — notably
-- the rewrite carve, which also needs the occurrence to be *convex* — must
-- retry down this list rather than committing to the first match.

subMatchAll : (L S : Hypergraph FlatGen) → List (L ↪ᴴ S)
subMatchAll L S =
  mapMaybe (λ { (φB , ψB) → verifySub L S φB ψB })
           (searchAll-default L S emptyBij emptyBij)

subMatch : (L S : Hypergraph FlatGen) → Maybe (L ↪ᴴ S)
subMatch L S = head (subMatchAll L S)
