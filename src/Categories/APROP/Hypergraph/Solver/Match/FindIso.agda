{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- Top-level decision procedure.
--
-- Wires together interface seeding, backtracking edge-matching search, and
-- the record-assembly verification stage into a single
--
--   findIso : H J → Maybe (H ≅ᴴ J)
--
-- SOUND but not complete: a `just _` result is a genuine isomorphism, but
-- the search may fail to locate a real iso due to fuel exhaustion or
-- cull-by-label pruning.  (In practice complete on `⟪_⟫`-translated graphs.)
--------------------------------------------------------------------------------

open import Categories.APROP.Hypergraph.Solver.Signature using (APROPSignatureDec)

module Categories.APROP.Hypergraph.Solver.Match.FindIso (sig-dec : APROPSignatureDec) where

open APROPSignatureDec sig-dec
open import Categories.APROP.Hypergraph.Model.Core using (Hypergraph)
open import Categories.APROP.Hypergraph.Model.FromAPROP sig using (FlatGen)
open import Categories.APROP.Hypergraph.Model.Iso using (_≅ᴴ_)
open import Categories.APROP.Hypergraph.Solver.Match.PBij
  using (PBij; emptyBij; pairUp)
open import Categories.APROP.Hypergraph.Solver.Match.Search sig-dec
  using (searchIso)
open import Categories.APROP.Hypergraph.Solver.Match.Verify sig-dec
  using (module Verify)

open import Data.Maybe.Base using (Maybe; _>>=_)
open import Data.Product using (_,_)

--------------------------------------------------------------------------------
-- Stage 1: interface seeding.
--
-- Seed a partial vertex bijection from the interfaces by pointwise pairing
-- `H.dom ↔ J.dom` and `H.cod ↔ J.cod`, pinning the boundary of the
-- isomorphism before edge matching begins.
--
-- Returns `nothing` when the interfaces have inconsistent length.  There is
-- deliberately NO vertex-label check here: `Search.tryEdge` compares
-- `map vlab` of both endpoint lists at every candidate edge and `Verify`
-- re-checks `φ-lab` at every vertex, so a seed-time sweep can only change
-- WHEN a doomed query fails, never WHETHER it does — and it costs one
-- `∀F?`-plus-`Dec` pass over `Fin H.nV` on every query, including the
-- succeeding ones.

seedFromInterfaces
  : ∀
    (H J : Hypergraph FlatGen)
  → Maybe (PBij (Hypergraph.nV H) (Hypergraph.nV J))
seedFromInterfaces H J =
  pairUp emptyBij (Hypergraph.dom H) (Hypergraph.dom J) >>= λ b →
  pairUp b        (Hypergraph.cod H) (Hypergraph.cod J)

--------------------------------------------------------------------------------
-- Pipeline:
--   1. Seed φ₀ from `H.dom ↔ J.dom` and `H.cod ↔ J.cod`.
--   2. Search for an edge-bijection extension.
--   3. Verify every `_≅ᴴ_` invariant.
-- Each stage returns `nothing` on failure.

findIso : ∀ (H J : Hypergraph FlatGen) → Maybe (H ≅ᴴ J)
findIso H J =
  seedFromInterfaces H J             >>= λ φ₀ →
  searchIso H J φ₀ emptyBij          >>= λ { (φ , ψ) →
  Verify.verify H J φ ψ }
