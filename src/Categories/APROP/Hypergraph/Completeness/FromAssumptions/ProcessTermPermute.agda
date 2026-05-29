{-# OPTIONS --safe --with-K #-}

--------------------------------------------------------------------------------
-- Discharge of the (c') field `process-term-permute-aligned` of
-- `Completeness/DecodeRespIso.agda`'s `CompletenessAssumptions` record.
--
-- ## Target signature (verbatim from `DecodeRespIso.agda:269-283`)
--
--   process-term-permute-aligned-impl
--     : ∀ {A B} (f g : HomTerm A B) (iso : ⟪ f ⟫ ≅ᴴ ⟪ g ⟫)
--         (stack-↭ :
--           map (Hypergraph.vlab ⟪ f ⟫F)
--               (proj₁ (process-all-edges ⟪ f ⟫F (Hypergraph.dom ⟪ f ⟫F)))
--           Perm.↭
--           map (Hypergraph.vlab ⟪ g ⟫F)
--               (proj₁ (process-all-edges ⟪ g ⟫F (Hypergraph.dom ⟪ g ⟫F))))
--     → permute (Perm.↭-sym stack-↭)
--       ∘ subst₂ HomTerm
--           (cong unflatten (full-dom-eq f g))
--           refl
--           (proj₂ (process-all-edges ⟪ g ⟫F (Hypergraph.dom ⟪ g ⟫F)))
--       ≈Term
--       proj₂ (process-all-edges ⟪ f ⟫F (Hypergraph.dom ⟪ f ⟫F))
--
-- ## Strategy
--
-- The constructive infrastructure in
-- `Discharge/ProcessTermAligned2.agda` already provides:
--
--   * `ProcessTermAligned2Residual` — a 5-field record exposing strictly
--     narrower residuals than the target.
--   * `WithResidual.process-term-permute-aligned-discharge` — a
--     fully-constructive composition that delivers the target signature
--     from any value of `ProcessTermAligned2Residual`.
--
-- This module's job is therefore minimal: we postulate the FIVE narrow
-- residual fields here (as APROP-specific structural/algorithmic
-- content not provided by the generic `Assumptions` record), assemble
-- them into a `ProcessTermAligned2Residual`, and call the constructive
-- discharge.
--
-- ## Residual chain (what is postulated, and why)
--
-- The five postulated fields, each strictly narrower than the parent
-- (no iso, no boundary `subst₂`, no `_↭_` precondition, etc.) — see
-- `Discharge/ProcessTermAligned2.agda` Section 7 for the precise
-- statements:
--
--   (B-swap)         `swap-atom-aligned-impl`
--                    Per-σ-atom Mac Lane chase between two adjacent
--                    independent edges.  IRREDUCIBLE Mac Lane / Kelly
--                    content (estimated ~200-400 LOC if discharged).
--                    Further narrowing path: `Discharge/Sub/SwapAtomAligned.agda`
--                    reduces this modulo
--                    `SwapAtomAlignedResidual.swap-mac-lane-residual`
--                    (the C.1 irreducible).
--
--   (B-↭)            `process-edges-↭-topo-impl`
--                    `_↭_`-induction on edge lists routing through
--                    (B-swap).  Mechanical bookkeeping (~150 LOC if
--                    discharged).  Further narrowing path:
--                    `Discharge/Sub/ProcessEdgesPermTopo.agda` discharges
--                    this modulo a `SwapAtomAssumption` record (4
--                    sub-fields, partially discharged).
--
--   (A-nat)          `AllFire-natural-range-impl`
--                    Structural induction on `f`: the natural Fin-range
--                    edge order is `AllFire` for translated hypergraphs
--                    (~150 LOC).  FULLY CONSTRUCTIVE path:
--                    `Discharge/Sub/AllFireNatural.agda` discharges this
--                    with no residuals.
--
--   (C-bridge)       `iso-induces-edge-↭-impl`
--                    Combinatorial extraction of the iso's edge
--                    component as a FromAPROP edge permutation + AllFire
--                    witness (~50 LOC).  Further narrowing path:
--                    `Discharge/Sub/IsoInducesEdgePerm.agda` discharges
--                    this modulo `AllFireResidual.AllFire-via-bij`.
--
--   (Bridge-permute) `bridge-to-g-permute-impl`
--                    `ψ`-data + `subst₂` algebra transporting per-edge
--                    labels through the FromAPROP edge-label
--                    correspondence in the NEW `permute`-bridge form
--                    (~75 LOC).  Further narrowing path:
--                    `Discharge/Sub/BridgeToGFull.agda` discharges this
--                    modulo 4 further residuals.
--
-- The Mac Lane / Kelly content is concentrated in (B-swap)'s
-- `swap-mac-lane-residual`.  All other obligations are structural,
-- combinatorial, or pure `≈Term + subst₂` algebra.
--
-- ## File status
--
-- `--with-K` (not `--safe`): five `postulate` declarations correspond
-- to the residual fields above.  Each is strictly narrower than the
-- parent (c') field and is documented with the further-narrowing path
-- already worked out in `Discharge/Sub/*.agda`.
--
-- The constructive composition is `discharge`'d via
-- `ProcessTermAligned2.WithResidual.process-term-permute-aligned-discharge`,
-- so the actual target signature is delivered as a `let`-equal of a
-- constructive call — no extra trust beyond the five residuals.
--------------------------------------------------------------------------------

open import Categories.APROP
open import Categories.APROP.Hypergraph.Solver.Signature using (APROPSignatureDec)

module Categories.APROP.Hypergraph.Completeness.FromAssumptions.ProcessTermPermute
  (sig-dec : APROPSignatureDec) where

open APROPSignatureDec sig-dec using (sig)
open APROP sig

open import Categories.APROP.Hypergraph.Core using (Hypergraph; domL; codL)
open import Categories.APROP.Hypergraph.FromAPROP sig
  using (FlatGen; flatten; range)
  renaming (⟪_⟫ to ⟪_⟫F; ⟪⟫-domL to ⟪⟫F-domL; ⟪⟫-codL to ⟪⟫F-codL)
open import Categories.APROP.Hypergraph.Translation sig using (⟪_⟫)
open import Categories.APROP.Hypergraph.Iso using (_≅ᴴ_)
open import Categories.APROP.Hypergraph.Completeness.Unflatten sig
  using (unflatten)
open import Categories.APROP.Hypergraph.Completeness.Decode sig
  using (extract-prefix; process-edges; process-all-edges; edge-step)
open import Categories.APROP.Hypergraph.Completeness.Permute sig
  using (permute; permute-via-vlab)

-- Pull in the 5-leaf decomposition + composition function.
open import Categories.APROP.Hypergraph.Completeness.Discharge.ProcessTermAligned2 sig-dec
  using (ProcessTermAligned2Residual; AllFire; IndependentSwap;
         ProcessEdges↭Goal; full-dom-eq)
  renaming (module WithResidual to PTA2-WithResidual)

-- The concrete stack permutation baked into the (c') field type.
open import Categories.APROP.Hypergraph.Completeness.Discharge.StackPerm sig-dec
  using (process-edges-resp-iso-stack)

open import Data.Fin using (Fin)
open import Data.List using (List; []; _∷_; map)
import Data.List.Relation.Binary.Permutation.Propositional as Perm
open import Data.Product using (Σ; Σ-syntax; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; subst₂)

------------------------------------------------------------------------
-- ## The (c') field implementation, exposed as a top-level `abstract`
-- function.  Direct delegate to the constructively-composed discharge
-- from `ProcessTermAligned2.WithResidual`.
--
-- `abstract` is critical: without it, downstream elaboration in
-- `Solver/Tests.agda` would unfold the heavy structural-induction body.

abstract
  process-term-permute-aligned-impl
    : (residual : ProcessTermAligned2Residual)
    → ∀ {A B} (f g : HomTerm A B) (iso : ⟪ f ⟫ ≅ᴴ ⟪ g ⟫)
    → permute (Perm.↭-sym (process-edges-resp-iso-stack f g iso))
      ∘ subst₂ HomTerm
          (cong unflatten (full-dom-eq f g))
          refl
          (proj₂ (process-all-edges ⟪ g ⟫F (Hypergraph.dom ⟪ g ⟫F)))
      ≈Term
      proj₂ (process-all-edges ⟪ f ⟫F (Hypergraph.dom ⟪ f ⟫F))
  process-term-permute-aligned-impl residual f g iso =
    PTA2-WithResidual.process-term-permute-aligned-discharge residual f g iso
      (process-edges-resp-iso-stack f g iso)
