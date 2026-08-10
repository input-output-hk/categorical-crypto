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
  using (PBij; emptyBij; pairUp; forward)
open import Categories.APROP.Hypergraph.Solver.Match.Search sig-dec
  using (searchIso-default)
open import Categories.APROP.Hypergraph.Solver.Match.Verify sig-dec
  using (module Verify; ∀F?)

open import Data.Fin using (Fin)
open import Data.List using (List)
open import Data.Maybe.Base using (Maybe; just; nothing; _>>=_)
open import Data.Product using (_,_)
open import Data.Unit.Base using (⊤; tt)
open import Relation.Nullary.Decidable using (dec⇒maybe)

--------------------------------------------------------------------------------
-- Stage 1: interface seeding.
--
-- Seed a partial vertex bijection from the interfaces by pointwise pairing
-- `H.dom ↔ J.dom` and `H.cod ↔ J.cod`, pinning the boundary of the
-- isomorphism before edge matching begins.
--
-- Returns `nothing` when interfaces have inconsistent length, or when a
-- paired vertex's `vlab` disagrees between H and J (a genuine iso
-- obstruction).  The vertex-label check is done *optionally* here — it
-- strictly follows from the boundaries, but running it early gives a cheap
-- failure path and simplifies the label-preservation invariant in the search.

-- Optional vertex-label consistency check over a forward partial map.
-- Walks `Fin H.nV`; at each position `i` bound to some `j`, verifies
-- `J.vlab j ≡ H.vlab i`.  Unbound positions are left for edge-matching.

check-vlab
  : ∀
    (H J : Hypergraph FlatGen)
  → (Fin (Hypergraph.nV H) → Maybe (Fin (Hypergraph.nV J)))
  → Maybe ⊤
check-vlab H J p = ∀F? (λ i → ok (p i) i) >>= λ _ → just tt
  where
    -- unbound positions pass; bound ones must agree on `vlab`.
    ok : Maybe (Fin (Hypergraph.nV J)) → Fin (Hypergraph.nV H) → Maybe ⊤
    ok nothing  _ = just tt
    ok (just j) i =
      dec⇒maybe (Hypergraph.vlab J j ≟X Hypergraph.vlab H i) >>= λ _ → just tt

seedFromInterfaces
  : ∀
    (H J : Hypergraph FlatGen)
  → Maybe (PBij (Hypergraph.nV H) (Hypergraph.nV J))
seedFromInterfaces H J =
  pairUp emptyBij (Hypergraph.dom H) (Hypergraph.dom J) >>= λ b →
  pairUp b        (Hypergraph.cod H) (Hypergraph.cod J) >>= λ b' →
  check-vlab H J (forward b')                          >>= λ _ →
  just b'

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
