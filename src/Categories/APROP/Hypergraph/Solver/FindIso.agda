{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- Phase 4a.6: Top-level decision procedure.
--
-- Wires together interface seeding (Phase 4a.2), backtracking edge-
-- matching search (Phase 4a.3–4a.4), and the record-assembly
-- verification stage (Phase 4a.5) into a single
--
--   findIso : H J → Maybe (H ≅ᴴ J)
--
-- The result is either a proof `H ≅ᴴ J`, or `nothing`. It is a
-- *sound* procedure — a `just _` result is a genuine isomorphism —
-- not a complete one: the search can fail to locate a real iso due
-- to fuel exhaustion or cull-by-label pruning that rules out a
-- viable candidate. For APROP translations (§4) the procedure is
-- in practice complete on hypergraphs coming from `⟦_⟧`.
--------------------------------------------------------------------------------

open import Categories.APROP.Hypergraph.Solver.Signature using (APROPSignatureDec)

module Categories.APROP.Hypergraph.Solver.FindIso (sig-dec : APROPSignatureDec) where

open APROPSignatureDec sig-dec
open import Categories.APROP.Hypergraph.Core using (Hypergraph)
open import Categories.APROP.Hypergraph.FromAPROP sig using (FlatGen)
open import Categories.APROP.Hypergraph.Iso using (_≅ᴴ_)
open import Categories.APROP.Hypergraph.Solver.PBij using (PBij; emptyBij)
open import Categories.APROP.Hypergraph.Solver.Seed sig-dec
  using (seedFromInterfaces)
open import Categories.APROP.Hypergraph.Solver.Search sig-dec
  using (searchIso-default)
open import Categories.APROP.Hypergraph.Solver.Verify sig-dec
  using (module Verify)

open import Data.List using (List)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Product using (_,_)

--------------------------------------------------------------------------------
-- Pipeline:
--   1. Seed φ₀ from `H.dom ↔ J.dom` and `H.cod ↔ J.cod`.
--   2. Search (fuel = nEH * nEJ) for an edge-bijection extension.
--   3. Verify every `_≅ᴴ_` invariant.
-- Each stage returns `nothing` on failure.

findIso
  : ∀
    (H J : Hypergraph FlatGen)
  → Maybe (H ≅ᴴ J)
findIso H J = stage-seed (seedFromInterfaces H J)
  where
    stage-verify
      : PBij (Hypergraph.nV H) (Hypergraph.nV J)
      → PBij (Hypergraph.nE H) (Hypergraph.nE J)
      → Maybe (H ≅ᴴ J)
    stage-verify φ ψ = Verify.verify H J φ ψ

    stage-search
      : PBij (Hypergraph.nV H) (Hypergraph.nV J)
      → Maybe (H ≅ᴴ J)
    stage-search φ₀ with searchIso-default H J φ₀ emptyBij
    ... | nothing        = nothing
    ... | just (φ , ψ)  = stage-verify φ ψ

    stage-seed
      : Maybe (PBij (Hypergraph.nV H) (Hypergraph.nV J))
      → Maybe (H ≅ᴴ J)
    stage-seed nothing  = nothing
    stage-seed (just φ₀) = stage-search φ₀
