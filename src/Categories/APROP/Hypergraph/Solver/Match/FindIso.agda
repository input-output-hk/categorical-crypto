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
open import Categories.APROP.Hypergraph.Solver.Match.PBij using (emptyBij)
open import Categories.APROP.Hypergraph.Solver.Match.Seed sig-dec
  using (seedFromInterfaces)
open import Categories.APROP.Hypergraph.Solver.Match.Search sig-dec
  using (searchIso-default)
open import Categories.APROP.Hypergraph.Solver.Match.Verify sig-dec using (module Verify)

open import Data.Maybe.Base using (Maybe; just; _>>=_)
open import Data.Product using (_,_)

--------------------------------------------------------------------------------
-- Pipeline:
--   1. Seed φ₀ from `H.dom ↔ J.dom` and `H.cod ↔ J.cod`.
--   2. Search (fuel = nEH * nEJ) for an edge-bijection extension.
--   3. Verify every `_≅ᴴ_` invariant.
-- Each stage returns `nothing` on failure.

findIso : ∀ (H J : Hypergraph FlatGen) → Maybe (H ≅ᴴ J)
findIso H J =
  seedFromInterfaces H J             >>= λ φ₀ →
  searchIso-default H J φ₀ emptyBij  >>= λ { (φ , ψ) →
  Verify.verify H J φ ψ }
