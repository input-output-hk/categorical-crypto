{-# OPTIONS --without-K #-}

--------------------------------------------------------------------------------
-- Phases 3.5c-d (and the missing piece of 3.5e) — `decode` and its
-- properties.
--
-- `decode` reconstructs a HomTerm from a hypergraph (Phase 3.5c).  Two
-- properties — both currently postulated — make it useful for
-- completeness:
--
--   * ~decode-roundtrip~ (Phase 3.5d): on a translated term,
--     ~decode ⟪ f ⟫ ≈Term bridge f~, where ~bridge~ is ~f~
--     composed with the ~unflatten-flatten-≈~ coherence iso on each
--     side.  Constructive proof is by induction on ~f~ (~3-5 days).
--
--   * ~decode-resp-≅ᴴ~ (consumed by Phase 3.5e):
--     ~H ≅ᴴ H' → decode H ≈Term decode H'~.  Constructive proof
--     might be possible directly by induction on the hypergraph
--     iso (without going through canonical form — see TODO.org
--     Phase 3.5b open question).
--
-- The intended construction of `decode` itself is the "cospan form"
-- from TensorRocq §3.2:
--
--   1. Topologically sort the edges (each edge's inputs must be
--      produced before the edge runs).
--   2. Thread a "stack" of currently-live vertices (initially `dom`,
--      finally `cod`).
--   3. For each edge `e`, reshuffle the stack so `ein e` is at the
--      front, emit `Agen (elab e)`, then replace the front with
--      `eout e`.
--   4. Final reshuffle from the end-of-edges stack to `cod`.
--
-- Linearity (each vertex appears exactly once on each side of every
-- ein/eout/dom/cod position) means only symmetries are needed for the
-- reshuffles — no duplication or discarding primitives are required.
--------------------------------------------------------------------------------

open import Categories.APROP

module Categories.APROP.Hypergraph.Completeness.Decoder (sig : APROPSignature) where

open APROP sig
open import Categories.APROP.Hypergraph.Core
open import Categories.APROP.Hypergraph.Iso
open import Categories.APROP.Hypergraph.FromAPROP sig using (FlatGen; ⟪_⟫; flatten)
open import Categories.APROP.Hypergraph.Completeness.Unflatten sig
  using (unflatten; unflatten-flatten-≈)

open import Categories.Morphism FreeMonoidal using (_≅_)

open import Data.List using (List)

private
  variable
    As Bs : List X

--------------------------------------------------------------------------------
-- The decoder.

postulate
  decode
    : Hypergraph FlatGen As Bs → HomTerm (unflatten As) (unflatten Bs)

--------------------------------------------------------------------------------
-- The bridge: `f` composed with the unflatten-flatten coherence isos
-- on each side.  When `flatten`/`unflatten` were definitional inverses
-- this would just be `f`; under propositional/iso-only inversion we
-- need the explicit bridge.

bridge
  : ∀ {A B}
  → HomTerm A B
  → HomTerm (unflatten (flatten A)) (unflatten (flatten B))
bridge {A} {B} f =
  _≅_.from (unflatten-flatten-≈ B) ∘ f ∘ _≅_.to (unflatten-flatten-≈ A)

--------------------------------------------------------------------------------
-- Properties of decode.

postulate
  -- Round-trip on translated terms (Phase 3.5d).
  decode-roundtrip
    : ∀ {A B} (f : HomTerm A B)
    → decode ⟪ f ⟫ ≈Term bridge f

  -- decode preserves hypergraph iso (consumed by Phase 3.5e).
  decode-resp-≅ᴴ
    : ∀ {H H' : Hypergraph FlatGen As Bs}
    → H ≅ᴴ H' → decode H ≈Term decode H'
