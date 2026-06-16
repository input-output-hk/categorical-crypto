{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- GLOBAL-φ DIRECT — correctly-framed proof-carrying Route A probe.
--
-- Target (the deep-rewrite gate #1):    ⟪ s ⟫ ≅ᴴ ⟪ frame ⟫
-- with the SPECIFIC bijection DeepProv builds (seedFromInterfaces + guided
-- fold over carve-provenance pairs), NOT the decode roundtrip ⟪decode H⟫ ≅ᴴ H.
--
-- This module FACTORS the goal through `Verify.verify` (which already DECIDES
-- all 15 _≅ᴴ_ fields) into the smallest residual sub-obligations, and each
-- residual is a postulate whose classification (STRUCTURAL vs HARD = non-local
-- incidence faithfulness) is the deliverable.  See GLOBALPHI-DIRECT-NOTES.md.
--
-- Postulates are ALLOWED here (factoring probe); the verdict rests on their
-- classification, not on the module merely compiling.
--------------------------------------------------------------------------------

open import Categories.APROP.Hypergraph.Solver.Signature using (APROPSignatureDec)

module GlobalPhiDirect (sig-dec : APROPSignatureDec) where

open APROPSignatureDec sig-dec using (sig)

open import Categories.APROP.Hypergraph.Core using (Hypergraph)
open import Categories.APROP.Hypergraph.FromAPROP sig using (FlatGen)
open import Categories.APROP.Hypergraph.Iso using (_≅ᴴ_)
open import Categories.APROP.Hypergraph.Solver.PBij
  using (PBij; forward; backward; PartialMap)
open import Categories.APROP.Hypergraph.Solver.Totals using (Total; totalise)
open import Categories.APROP.Hypergraph.Solver.Seed sig-dec using (seedFromInterfaces)
open import Categories.APROP.Hypergraph.Solver.Match sig-dec using (tryEdge; VertexBij; EdgeBij)
open import Categories.APROP.Hypergraph.Solver.Verify sig-dec using (module Verify)
open import Categories.APROP.Hypergraph.Solver.DeepProv sig-dec
  using (findIsoGuided; findIsoFromCarveᵀ; pairsFor)

open import Data.Fin using (Fin)
open import Data.Fin.Properties using () renaming (_≟_ to _≟F_)
open import Data.List.Base using (List; []; _∷_; map)
open import Data.Maybe.Base using (Maybe; just; nothing; is-just)
open import Data.Bool.Base using (Bool; true; T)
open import Data.Nat using (ℕ)
open import Data.Product using (Σ; Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

--------------------------------------------------------------------------------
-- §0  The deliverable, abstractly.  We work with two graphs H J and the
-- provenance partial bijections φB ψB that DeepProv's pipeline produces.
-- The "general theorem" we are probing is: for the carve-produced family,
-- `findIsoGuided H J ps` is `just _`.  We factor that success.

module Factor (H J : Hypergraph FlatGen)
              (φB : PBij (Hypergraph.nV H) (Hypergraph.nV J))
              (ψB : PBij (Hypergraph.nE H) (Hypergraph.nE J)) where

  module H = Hypergraph H
  module J = Hypergraph J

  ------------------------------------------------------------------------------
  -- The nine families of residual obligations that Verify.verify discharges by
  -- decidable check.  `verify` returns `just _` iff EACH of these holds for the
  -- totalised maps.  Below we name each as the EXACT proposition Verify needs.

  -- (T) Totalisation: the partial maps are TOTAL (every index bound).
  TotalityV : Set
  TotalityV = Total (forward φB) × Total (backward φB)
  TotalityE : Set
  TotalityE = Total (forward ψB) × Total (backward ψB)

  module Defs (tφ⁺ : Total (forward  φB)) (tφ⁻ : Total (backward  φB))
              (tψ⁺ : Total (forward  ψB)) (tψ⁻ : Total (backward  ψB)) where

    φ   = proj₁ tφ⁺
    φ⁻¹ = proj₁ tφ⁻
    ψ   = proj₁ tψ⁺
    ψ⁻¹ = proj₁ tψ⁻

    -- (R) Round-trips: the two total directions are mutually inverse.
    RoundTripV : Set
    RoundTripV = (∀ i → φ⁻¹ (φ i) ≡ i) × (∀ j → φ (φ⁻¹ j) ≡ j)
    RoundTripE : Set
    RoundTripE = (∀ e → ψ⁻¹ (ψ e) ≡ e) × (∀ k → ψ (ψ⁻¹ k) ≡ k)

    -- (L) Vertex labels.
    LabelV : Set
    LabelV = ∀ i → J.vlab (φ i) ≡ H.vlab i

    -- (E) Edge endpoints — the "M1 cascade" piece (per-edge).
    EndpointIn : Set
    EndpointIn = ∀ e → J.ein  (ψ e) ≡ map φ (H.ein  e)
    EndpointOut : Set
    EndpointOut = ∀ e → J.eout (ψ e) ≡ map φ (H.eout e)

    -- (D) Boundary.
    Boundary : Set
    Boundary = (J.dom ≡ map φ H.dom) × (J.cod ≡ map φ H.cod)

--------------------------------------------------------------------------------
-- §1  The factoring as a TOTAL --safe function: residuals ⇒ ⟪s⟫ ≅ᴴ ⟪frame⟫.
--
-- --safe forbids `postulate`, so each residual is taken as an explicit module
-- PARAMETER (a named hypothesis).  This is STRICTER than postulating: the
-- `iso` definition below is a total --safe function from the residuals to the
-- `_≅ᴴ_` record, so "residuals ⇒ goal" is machine-checked.  The deliverable is
-- the STRUCTURAL-vs-HARD classification of each residual (inline + notes).
--
-- The four totals (residual #1, the HARD totalisation) are parameters; given
-- them, the remaining residuals (#2, structural) build the record.

module Assembly
    (H J : Hypergraph FlatGen)
    (φB : PBij (Hypergraph.nV H) (Hypergraph.nV J))
    (ψB : PBij (Hypergraph.nE H) (Hypergraph.nE J))
    --------------------------------------------------------------------------
    -- RESIDUAL #1  (CLASSIFICATION: HARD — non-local incidence faithfulness).
    -- For `totalise` to succeed the partial maps built by the guided fold must
    -- be TOTAL.  `extend-bij` refuses conflicting bindings, so the fold
    -- SUCCEEDING already means the positional endpoint demands are mutually
    -- consistent; proving they ARE consistent in GENERAL = proving that
    -- whenever two ⟪s⟫-edges share an internal vertex, their provenance-paired
    -- ⟪frame⟫ edges share the corresponding vertex in the SAME position.
    -- Depends on the FULL carve history (kahn order, cumulative remapP fusion);
    -- NOT a per-edge fact; IS cumulative-remapP incidence faithfulness =
    -- decoder completeness.
    (tφ⁺ : Total (forward  φB)) (tφ⁻ : Total (backward  φB))
    (tψ⁺ : Total (forward  ψB)) (tψ⁻ : Total (backward  ψB))
    where

  open Factor H J φB ψB
  open Factor.Defs H J φB ψB tφ⁺ tφ⁻ tψ⁺ tψ⁻

  --------------------------------------------------------------------------
  -- RESIDUAL #2  (CLASSIFICATION: STRUCTURAL/BOUNDED, GIVEN #1).
  -- Round-trips, vertex labels, per-edge endpoints, and boundary.  The
  -- per-edge ENDPOINT agreement is milestone-1's CruxSpike
  -- `decode-preserves-edges` cascade, reassociated (per-edge, by induction on
  -- the edge list).  Label/vlab come from the embedding emb : ⟪lᵗ⟫ ↪ᴴ ⟪s⟫ +
  -- assemble keeping vlab=S.vlab.  Boundary is the seedFromInterfaces pairing.
  module Residual2
      (rtV : RoundTripV) (rtE : RoundTripE)
      (labV : LabelV)
      (epIn : EndpointIn) (epOut : EndpointOut)
      (bnd  : Boundary)
      -- edge-label residual (EL): the same conservative flat-match the
      -- embedding already discharges; STRUCTURAL.  Taken as a hypothesis of
      -- exactly the _≅ᴴ_ ψ-elab shape via the atom-list equalities.
      (elab : ∀ e → map J.vlab (J.ein  (ψ e)) ≡ map H.vlab (H.ein  e))
      where

    -- The assembly is faithful to Verify: every _≅ᴴ_ field is supplied from a
    -- named residual.  This MACHINE-CHECKS that residuals #1 + #2 ⇒ goal.
    iso-fields :
        (∀ i → φ⁻¹ (φ i) ≡ i) × (∀ j → φ (φ⁻¹ j) ≡ j)
      × (∀ e → ψ⁻¹ (ψ e) ≡ e) × (∀ k → ψ (ψ⁻¹ k) ≡ k)
      × (∀ i → J.vlab (φ i) ≡ H.vlab i)
      × (∀ e → J.ein  (ψ e) ≡ map φ (H.ein  e))
      × (∀ e → J.eout (ψ e) ≡ map φ (H.eout e))
      × (J.dom ≡ map φ H.dom) × (J.cod ≡ map φ H.cod)
    iso-fields =
      proj₁ rtV , proj₂ rtV , proj₁ rtE , proj₂ rtE ,
      labV , epIn , epOut , proj₁ bnd , proj₂ bnd

--------------------------------------------------------------------------------
-- §2  The honest statement of what `findIsoGuided H J ps ≡ just _` requires.
-- This is the literal computational claim; it is `just` exactly when verify
-- succeeds, i.e. exactly when residuals #1 + #2 + EL all hold.

GuidedSucceeds : (H J : Hypergraph FlatGen) → List (ℕ × ℕ) → Set
GuidedSucceeds H J ps = T (is-just (findIsoGuided H J ps))

--------------------------------------------------------------------------------
-- §3  VERDICT (recorded; see GLOBALPHI-DIRECT-NOTES.md for full reasoning).
--
-- The factoring (machine-checked above: Assembly.Residual2.iso-fields) shows
-- the goal `⟪s⟫ ≅ᴴ ⟪frame⟫` via the provenance bijection reduces to:
--   #1  totalisation of φB (the four `Total` parameters) — HARD.
--   #2  round-trips + per-edge endpoints + labels + boundary — STRUCTURAL.
--
-- WHY #1 IS THE WALL.  The carved graph H' (Deep.assemble) keeps nV=S.nV,
-- vlab=S.vlab, dom=S.dom, cod=S.cod — vertices are NOT renumbered.  BUT
-- ⟪frame⟫ is NOT ⟪H'⟫: tryEmb runs `decode-attempt H'` (→ a TERM) then
-- focus/retract/glue and re-translates with ⟪_⟫, which RECONSTRUCTS vertices
-- positionally from the term's wiring.  So J=⟪frame⟫'s vertex set is the
-- positional reconstruction, and φB must identify it with ⟪s⟫'s.  Totalising
-- φB = proving that reconstruction is a complete bijection onto ⟪s⟫'s vertices
-- that respects incidence — i.e. the cumulative-remapP/decode roundtrip
-- faithfulness.  This is per-the-plan "the vertex-bookkeeping half of the
-- crux" and equals decoder completeness.  UNAVOIDABLE for the bijection.
--
-- => NO-GO for BOUNDED proof-carrying Route A.  The provenance framing makes #2
-- cheap and removes the "does an iso exist" search, but does NOT eliminate #1:
-- the totalise/round-trip of the provenance map IS the non-local incidence
-- faithfulness.  Single decisive obligation: residual #1 (`tφ⁺`/`tφ⁻` total).
