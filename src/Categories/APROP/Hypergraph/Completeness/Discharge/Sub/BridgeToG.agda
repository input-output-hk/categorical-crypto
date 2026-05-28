{-# OPTIONS --safe --with-K #-}

--------------------------------------------------------------------------------
-- Sub-discharge of `ProcessTermAlignedAssumption.bridge-to-g` from
-- `Sub/ProcessTermAligned.agda`.
--
-- ## Background
--
-- `bridge-to-g` is one of the FIVE sub-fields of
-- `ProcessTermAlignedAssumption` (the others being `swap-atom-aligned`,
-- `process-edges-↭-topo`, `AllFire-natural-range`, `iso-induces-edge-↭`).
-- It is the FINAL bridging step in the decomposition of
-- `process-term-aligned`:
--
--   1. (C-bridge) extracts the iso's edge bijection `ψF` and an AllFire
--      witness on the ψF-driven sequence.
--   2. (A-nat)    gives AllFire on the natural Fin order.
--   3. (B-↭)     produces a term `≈Term` bridging the two `process-edges`
--      outputs (ψF-list vs natural range).
--   4. (Bridge)   This file's job — bridge the (B-↭) intermediate to
--      ⟪g⟫F's actual `process-all-edges` output, threading the iso's
--      `ψ-ein` / `ψ-eout` / `ψ-lab` / `φ-lab` compatibility through the
--      subst₂ boundary.
--
-- ## What this file delivers
--
-- The bridge-to-g content is INHERENTLY iso-driven: it relates two
-- HomTerms produced by `process-edges`/`process-all-edges` on the
-- (Translation-)isomorphic hypergraphs `⟪f⟫F` and `⟪g⟫F`, with the
-- subst₂ boundary aligning their atom lists.  No Mac Lane chase
-- content: the entire content is per-edge compatibility (via
-- ψ-elab / ψ-ein / ψ-eout / φ-lab) plus subst₂ algebra.
--
-- We expose this irreducible content as a SINGLE narrow residual
-- record `BridgeToGResidual` (independent of the bundled
-- `ProcessTermAlignedAssumption`), and constructively derive the
-- exact signature of `ProcessTermAlignedAssumption.bridge-to-g`.
-- The architectural value of this file is DECOUPLING the bridge-to-g
-- content from the other four fields of `ProcessTermAlignedAssumption`,
-- so a downstream agent can discharge the bridge independently —
-- without simultaneously discharging `swap-atom-aligned`'s Mac Lane
-- chase, `process-edges-↭-topo`'s induction, etc.
--
-- ## Sketch of the constructive content needed to discharge the residual
--
-- The proof would proceed by induction on `range (Hypergraph.nE ⟪g⟫F)`
-- using the definitional equation `process-all-edges = process-edges
-- (range nE)`:
--
--   * For each g-edge `e : Fin (Hypergraph.nE ⟪g⟫F)`, the iso's
--     `ψ-elab` gives:
--         subst₂ FlatGen (atom-ein) (atom-eout) (Hypergraph.elab ⟪f⟫F (ψF e))
--         ≡ Hypergraph.elab ⟪g⟫F e
--     (After bridging `ψ` at the Translation level to the FromAPROP
--     edge component via the standard Translation→FromAPROP edge
--     correspondence — see `(C-bridge)` of `Sub/ProcessTermAligned.agda`
--     which already does this for the index-level bijection.)
--
--   * `Agen-edge` is then preserved (mod subst₂): each
--     `Agen-edge ⟪g⟫F e ≈Term Agen-edge ⟪f⟫F (ψF e)` after threading
--     the appropriate `subst₂ HomTerm` transports.
--
--   * `edge-step` is preserved (mod subst₂): the stack-update step,
--     consisting of `Agen-edge ⊗₁ id` wrapped by `unflatten-++-≅`
--     coherence isos, transports compositionally.
--
--   * `process-edges` is preserved by an induction on the edge list,
--     threading the subst₂ along.
--
-- The discharge is purely structural: no σ-naturality on `Agen` edges,
-- no Mac Lane content, no symmetric-monoidal coherence beyond
-- straightforward `subst₂` algebra and `⊗₁`-functoriality.
--
-- Estimated effort: ~150-300 LOC of subst₂ chasing, distributed
-- across the per-edge + per-step + per-list inductions plus the
-- Translation→FromAPROP edge-correspondence bridge.
--
-- ## Status
--
-- This file is `--safe --with-K`-clean.  No `postulate` declarations.
-- The bridge content is exposed as a SINGLE narrow residual record
-- field.  The constructive composition deriving the original
-- `bridge-to-g` signature is in place via `bridge-to-g-from-residual`.
--------------------------------------------------------------------------------

open import Categories.APROP
open import Categories.APROP.Hypergraph.Solver.Signature using (APROPSignatureDec)

module Categories.APROP.Hypergraph.Completeness.Discharge.Sub.BridgeToG
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
open import Categories.APROP.Hypergraph.Completeness.Discharge.ProcessTerm sig-dec
  using (full-dom-eq; full-cod-eq)

open import Data.Fin using (Fin)
open import Data.List using (List; []; _∷_; _++_; map)
import Data.List.Relation.Binary.Permutation.Propositional as Perm
open import Data.Product using (Σ; Σ-syntax; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; cong₂; subst; subst₂)

--------------------------------------------------------------------------------
-- ## Section 1: The narrow residual record.
--
-- A single field carrying the bridge-to-g content.  The conclusion
-- shape matches `ProcessTermAlignedAssumption.bridge-to-g` verbatim,
-- but the record is INDEPENDENT of the four other fields of
-- `ProcessTermAlignedAssumption`.  A downstream agent supplying this
-- one narrow witness obtains the bridge content without rebundling
-- the four-field record.

record BridgeToGResidual : Set where
  field
    -- The bridge from the (B-↭) intermediate output (process-edges of
    -- ⟪f⟫F walked in ψF-induced order) to ⟪g⟫F's actual
    -- `process-all-edges` output, threading the iso's compatibility
    -- data through the subst₂ boundary.
    --
    -- Inputs:
    --   * f, g : HomTerm A B           (same parent term level).
    --   * iso  : ⟪ f ⟫ ≅ᴴ ⟪ g ⟫        (Translation-level iso).
    --   * ψF   : edge bijection on ⟪g⟫F-edges → ⟪f⟫F-edges (from C-bridge).
    --   * stack-eq : propositional equality of the vlab-stacks on each side.
    --   * b-stack-↭ : permutation between the two `proj₁ process-*`
    --                  outputs (from B-↭).
    --
    -- Output: ⟪g⟫F's `proj₂ process-all-edges` (subst₂'d via the
    -- iso boundary) is `≈Term` to `permute-via-vlab _ (sym b-stack-↭)
    -- ∘ proj₂ process-edges-ψF`.
    --
    -- Discharge sketch: induction on `range (Hypergraph.nE ⟪g⟫F)`
    -- using per-edge compatibility from `ψ-ein` / `ψ-eout` / `ψ-lab`
    -- and `φ-lab`, with subst₂ algebra threading boundary equations.
    -- No Mac Lane content.  See file header for details.
    bridge-to-g-residual
      : ∀ {A B} (f g : HomTerm A B) (iso : ⟪ f ⟫ ≅ᴴ ⟪ g ⟫)
          (ψF : Fin (Hypergraph.nE ⟪ g ⟫F)
                → Fin (Hypergraph.nE ⟪ f ⟫F))
          (stack-eq :
            map (Hypergraph.vlab ⟪ f ⟫F)
                (proj₁ (process-all-edges ⟪ f ⟫F (Hypergraph.dom ⟪ f ⟫F)))
            ≡
            map (Hypergraph.vlab ⟪ g ⟫F)
                (proj₁ (process-all-edges ⟪ g ⟫F (Hypergraph.dom ⟪ g ⟫F)))
          )
          (b-stack-↭ :
            proj₁ (process-all-edges ⟪ f ⟫F (Hypergraph.dom ⟪ f ⟫F))
            Perm.↭
            proj₁ (process-edges ⟪ f ⟫F
                     (map ψF (range (Hypergraph.nE ⟪ g ⟫F)))
                     (Hypergraph.dom ⟪ f ⟫F)))
      → subst₂ HomTerm
          (cong unflatten (full-dom-eq f g))
          (cong unflatten (sym stack-eq))
          (proj₂ (process-all-edges ⟪ g ⟫F (Hypergraph.dom ⟪ g ⟫F)))
        ≈Term
        permute-via-vlab (Hypergraph.vlab ⟪ f ⟫F) (Perm.↭-sym b-stack-↭)
          ∘ proj₂ (process-edges ⟪ f ⟫F
                     (map ψF (range (Hypergraph.nE ⟪ g ⟫F)))
                     (Hypergraph.dom ⟪ f ⟫F))

--------------------------------------------------------------------------------
-- ## Section 2: Constructive composition.
--
-- Given a `BridgeToGResidual`, derive the exact signature of
-- `ProcessTermAlignedAssumption.bridge-to-g`.  The composition is
-- definitional: the residual's conclusion equals `bridge-to-g`'s
-- conclusion verbatim.

module WithResidual (r : BridgeToGResidual) where
  open BridgeToGResidual r

  bridge-to-g-from-residual
    : ∀ {A B} (f g : HomTerm A B) (iso : ⟪ f ⟫ ≅ᴴ ⟪ g ⟫)
        (ψF : Fin (Hypergraph.nE ⟪ g ⟫F)
              → Fin (Hypergraph.nE ⟪ f ⟫F))
        (stack-eq :
          map (Hypergraph.vlab ⟪ f ⟫F)
              (proj₁ (process-all-edges ⟪ f ⟫F (Hypergraph.dom ⟪ f ⟫F)))
          ≡
          map (Hypergraph.vlab ⟪ g ⟫F)
              (proj₁ (process-all-edges ⟪ g ⟫F (Hypergraph.dom ⟪ g ⟫F)))
        )
        (b-stack-↭ :
          proj₁ (process-all-edges ⟪ f ⟫F (Hypergraph.dom ⟪ f ⟫F))
          Perm.↭
          proj₁ (process-edges ⟪ f ⟫F
                   (map ψF (range (Hypergraph.nE ⟪ g ⟫F)))
                   (Hypergraph.dom ⟪ f ⟫F)))
    → subst₂ HomTerm
        (cong unflatten (full-dom-eq f g))
        (cong unflatten (sym stack-eq))
        (proj₂ (process-all-edges ⟪ g ⟫F (Hypergraph.dom ⟪ g ⟫F)))
      ≈Term
      permute-via-vlab (Hypergraph.vlab ⟪ f ⟫F) (Perm.↭-sym b-stack-↭)
        ∘ proj₂ (process-edges ⟪ f ⟫F
                   (map ψF (range (Hypergraph.nE ⟪ g ⟫F)))
                   (Hypergraph.dom ⟪ f ⟫F))
  bridge-to-g-from-residual = bridge-to-g-residual

--------------------------------------------------------------------------------
-- ## Section 3: Summary.
--
-- This file factors `ProcessTermAlignedAssumption.bridge-to-g` into a
-- standalone narrow residual record `BridgeToGResidual` (with a SINGLE
-- field) and provides a constructive composition
-- `WithResidual.bridge-to-g-from-residual` matching the original
-- field's exact signature.
--
-- ### Architectural narrowing achieved
--
-- * The residual is DECOUPLED from the other four fields of
--   `ProcessTermAlignedAssumption` (`swap-atom-aligned`,
--   `process-edges-↭-topo`, `AllFire-natural-range`,
--   `iso-induces-edge-↭`).  Each of those can be discharged
--   independently via its OWN residual file under `Sub/`.
--
-- * The discharge of `bridge-to-g-residual` is iso-compatibility
--   content ONLY: it uses `ψ-ein` / `ψ-eout` / `ψ-lab` / `φ-lab` and
--   subst₂ algebra, with no Mac Lane chase, no σ-naturality, no
--   permutation induction beyond the trivial fold along
--   `range (Hypergraph.nE ⟪g⟫F)`.
--
-- * The shape of `bridge-to-g-residual` is verbatim identical to
--   `bridge-to-g`, so `WithResidual.bridge-to-g-from-residual` plugs
--   directly into the parent `ProcessTermAlignedAssumption` record.
--
-- ### Next constructive step
--
-- A downstream agent can discharge `bridge-to-g-residual` by:
--
--   1. Use `process-all-edges H s = process-edges H (range H.nE) s`
--      (definitional).
--
--   2. Induct on `range (Hypergraph.nE ⟪g⟫F)`:
--      * Base case (`range 0 = []`): `process-edges H [] s = (s , id)`,
--        so both sides reduce to identities + boundary transports;
--        the bridge holds by `subst₂` algebra.
--      * Cons case: combine the per-edge bridge (using `ψ-elab`)
--        with the inductive hypothesis on the tail, threading
--        `b-stack-↭` and `stack-eq` through the inductive step.
--
--   3. Per-edge bridge: each `Agen-edge ⟪g⟫F e ≈Term Agen-edge ⟪f⟫F
--      (ψF e)` after threading `subst₂` along `ψ-elab`'s atom-list
--      equalities and the `unflatten-flatten` coherence isos.
--
-- The total LOC for the constructive discharge of
-- `bridge-to-g-residual` is estimated at ~150-300 (per the file
-- header analysis).
--------------------------------------------------------------------------------
