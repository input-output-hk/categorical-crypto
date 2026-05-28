{-# OPTIONS --safe --with-K #-}

--------------------------------------------------------------------------------
-- # Constructive composition of `process-term-permute-aligned` from
--   irreducible APROP-specific Mac Lane atoms.
--
-- This file shows that the (c') field `process-term-permute-aligned` of
-- `Completeness/DecodeRespIso.agda`'s `Build` record is delivered
-- constructively from a SMALL bundle of strictly narrower atoms, plus
-- one fully-discharged constructive fact (`AllFire-natural-range`).
--
-- ## The record `APROPMacLaneAtoms`
--
-- After maximal constructive narrowing of the c' chain, the irreducible
-- atoms group into TWO nested residual bundles plus ONE bridge atom:
--
--   (1) `swap-atom-residual : SwapAtomResidual`        — 3 fields
--       (was 4; `Linear-hyp` removed — Linearity is now threaded
--        per-call at H = ⟪f⟫F via `⟪⟫-Linear`)
--   (2) `allFire-residual` (iso-induces-edge-↭-direct): REMOVED — now
--       discharged constructively in
--       `Sub/IsoInducesEdgePerm.iso-induces-edge-residual` (Section 9c)
--       via the trivial Fin-cast ψF strategy + `AllFire-natural-range`
--       on `⟪f⟫F`.  The `IsoInducesEdge` record is now constructively
--       inhabited; no postulated field remains on this surface.
--   (3) `bridge-to-g-permute`                          — 1 field
--                                                       (verbatim same type as
--                                                        ProcessTermAligned2Residual.bridge-to-g-permute;
--                                                        native `Perm.↭`-form, no propositional
--                                                        `Σ stack-eq` content).
--
-- Earlier revisions decomposed the bridge into
-- `walk : NaturalRangeWalkBridge` + `sob : StackOrderingBridge` +
-- `permute-eq-bridge`.  The latter was UNSOUND: it required producing
-- a propositional `stack-eq` witness whose first projection
-- (`map vlab_f … ≡ map vlab_g …`) is refuted in general by the
-- constructive counter-example in `Sub/StackListEq.agda`.  The
-- decomposition has been retired in favour of the native-↭ form below.
--
-- ### Provenance of each field (where & why irreducible)
--
-- (1) `SwapAtomResidual` — from `Sub/SwapAtomAssumptionDischarge.agda`.
--     Its three fields, with provenance:
--
--     (1a) `swap-atom-aligned`
--          Source: `Sub/SwapAtomAssumptionDischarge.agda:128-133`.
--          Why irreducible: per-σ Mac Lane / Kelly chase aligning
--          `unflatten-++-≅` wrappers and applying `⊗-∘-dist` to commute
--          two independent adjacent edges.  Unavoidable pending a
--          `solveM` extension to the symmetric monoidal fragment.
--
--     (1b) `swap-with-rest-aligned`
--          Source: `Sub/SwapAtomAssumptionDischarge.agda:136-144`.
--          Why irreducible: full swap-with-rest content (stack-permute
--          coherence on the post-prefix stacks + suffix induction
--          through the Mac Lane chase).
--
--     (1c) `swap-already-fires`
--          Source: `Sub/SwapAtomAssumptionDischarge.agda:147-154`.
--          Why irreducible: topological-soundness for AllFire swap, NOT
--          implied by Linearity (per `EdgeReorder.agda` counter-example).
--
--     (1d) `Linear-hyp`
--          Source: `Sub/SwapAtomAssumptionDischarge.agda:158`.
--          Why kept here: an `∀ H → Linear H` parameter used by the
--          generic `WithSwapAtom` machinery; effectively only needed at
--          translated hypergraphs (`⟪f⟫F`), but the type as stated is
--          universal, so we treat it as an atomic input.
--
-- (2) `IsoInducesEdge` — from `Sub/IsoInducesEdgePerm.agda` (post-R1).
--     Its single field, with provenance:
--
--     (2a) `iso-induces-edge-↭-direct`
--          Source: `Sub/IsoInducesEdgePerm.agda`.
--          Why irreducible: the consumer-facing edge+AllFire triple.
--          Blocked at the FromAPROP level by `BoundaryRespectsIso.agda`
--          (pruning differences) — the previous "structural
--          Translation→FromAPROP iso lift" shape was uninhabitable
--          (refuted in-file at `IsoInducesEdgePerm.Refutation`);
--          refactor R1 replaced it with the direct triple at the
--          surface so the known-false vertex-bijection requirement is
--          no longer present.  Whether the direct triple is
--          constructively producible is a separate (open) question.
--
--     The former second field `AllFire-natural-range-source` is
--     derived constructively in-file in `Sub/IsoInducesEdgePerm.agda`
--     from `Sub/AllFireNatural.AllFire-natural-range`, and is not
--     part of the record surface.
--
-- (3) `bridge-to-g-permute` — single bridge atom in the SOUND
--     native-↭ form.
--
--     Source: same signature as
--     `ProcessTermAligned2.ProcessTermAligned2Residual.bridge-to-g-permute`,
--     which is proved constructively at the propositional-eq
--     orientation by `Sub/ProcessTermAligned.bridge-to-g`.
--
--     The previous decomposition into
--     (walk, sob, permute-eq-bridge) was UNSOUND because
--     `permute-eq-bridge` produced a propositional `stack-eq`
--     witness whose first projection
--     (`map vlab_f … ≡ map vlab_g …`) is refuted in general by
--     the counter-example in `Sub/StackListEq.agda`.
--
-- ## Constructive discharges used here
--
--   * `AllFire-natural-range` for ⟪f⟫F  : from `Sub/AllFireNatural.agda`.
--   * `AllFire-natural-range` for ⟪g⟫F  : derived constructively inside
--     `Sub/IsoInducesEdgePerm.agda` from the same source; no longer
--     surfaced as a field of `IsoInducesEdge`.
--
-- ## Output
--
--   * `process-term-permute-aligned-from-atoms`
--     : APROPMacLaneAtoms → <the c' signature, verbatim>
--
-- ## File status
--
-- `--safe --with-K` clean.  NO `postulate` declarations.
--------------------------------------------------------------------------------

open import Categories.APROP
open import Categories.APROP.Hypergraph.Solver.Signature using (APROPSignatureDec)

module Categories.APROP.Hypergraph.Completeness.Discharge.ProcessTermPermuteAlignedFromIrreducibles
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
  using (extract-prefix; process-edges; process-all-edges)
open import Categories.APROP.Hypergraph.Completeness.Permute sig
  using (permute; permute-via-vlab)

-- The three irreducible-atom records:
open import Categories.APROP.Hypergraph.Completeness.Discharge.Sub.SwapAtomAssumptionDischarge
  sig-dec
  using (SwapAtomResidual; build-swap-atom-assumption)
open import Categories.APROP.Hypergraph.Completeness.Discharge.Sub.IsoInducesEdgePerm
  sig-dec
  using ( IsoInducesEdge; iso-induces-edge-↭-via-residual; FromAPROP-Iso-Data
        ; iso-induces-edge-residual)

-- The ProcessTermAligned2Residual + WithResidual machinery:
import Categories.APROP.Hypergraph.Completeness.Discharge.ProcessTermAligned2
  sig-dec as PTA2
open PTA2 using (ProcessTermAligned2Residual; full-dom-eq)
  renaming (module WithResidual to PTA2-WithResidual)

-- The (B-↭) constructive discharge modulo SwapAtomAssumption:
open import Categories.APROP.Hypergraph.Completeness.Discharge.Sub.ProcessEdgesPermTopo
  sig-dec
  using (SwapAtomAssumption; module WithSwapAtom)

-- AllFire predicate, IndependentSwap and ProcessEdges↭Goal at TWO levels:
--   PTA  = Sub.ProcessTermAligned         (used by SwapAtomAssumption/AllFireNatural)
--   PTA2 = Discharge.ProcessTermAligned2  (used by ProcessTermAligned2Residual)
import Categories.APROP.Hypergraph.Completeness.Discharge.Sub.ProcessTermAligned
  sig-dec as PTA

-- The AllFire copy used by IsoInducesEdge is yet another (IIEP).  Imported
-- under a separate qualifier:
import Categories.APROP.Hypergraph.Completeness.Discharge.Sub.IsoInducesEdgePerm
  sig-dec as IIEP

-- Constructive AllFire-natural-range (produces PTA-flavoured AllFire):
open import Categories.APROP.Hypergraph.Completeness.Discharge.Sub.AllFireNatural
  sig-dec
  using (AllFire-natural-range)

-- Linearity (constructive on translated hypergraphs):
import Categories.APROP.Hypergraph.Completeness.Linearity sig as Lin

open import Categories.Category using (Category)

open import Data.Fin using (Fin)
open import Data.List using (List; []; _∷_; map)
import Data.List.Relation.Binary.Permutation.Propositional as Perm
open import Data.Product using (Σ; Σ-syntax; _,_; _×_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; cong₂; subst; subst₂)

private
  module FM = Category FreeMonoidal

--------------------------------------------------------------------------------
-- ## Section 1: AllFire converters between the three definitionally-distinct
-- copies of `AllFire`.
--
-- Each `AllFire` definition is the SAME body but lives in a different module,
-- so the types are not definitionally equal in Agda.  We provide
-- explicit recursive converters (~5 lines each).

PTA→PTA2-AllFire
  : ∀ (H : Hypergraph FlatGen)
      (es : List (Fin (Hypergraph.nE H)))
      (s : List (Fin (Hypergraph.nV H)))
  → PTA.AllFire H es s
  → PTA2.AllFire H es s
PTA→PTA2-AllFire H [] s af = af
PTA→PTA2-AllFire H (e ∷ es) s (rest , p , eq , af-tail) =
  rest , p , eq , PTA→PTA2-AllFire H es _ af-tail

PTA2→PTA-AllFire
  : ∀ (H : Hypergraph FlatGen)
      (es : List (Fin (Hypergraph.nE H)))
      (s : List (Fin (Hypergraph.nV H)))
  → PTA2.AllFire H es s
  → PTA.AllFire H es s
PTA2→PTA-AllFire H [] s af = af
PTA2→PTA-AllFire H (e ∷ es) s (rest , p , eq , af-tail) =
  rest , p , eq , PTA2→PTA-AllFire H es _ af-tail

PTA→IIEP-AllFire
  : ∀ (H : Hypergraph FlatGen)
      (es : List (Fin (Hypergraph.nE H)))
      (s : List (Fin (Hypergraph.nV H)))
  → PTA.AllFire H es s
  → IIEP.AllFire H es s
PTA→IIEP-AllFire H [] s af = af
PTA→IIEP-AllFire H (e ∷ es) s (rest , p , eq , af-tail) =
  rest , p , eq , PTA→IIEP-AllFire H es _ af-tail

IIEP→PTA2-AllFire
  : ∀ (H : Hypergraph FlatGen)
      (es : List (Fin (Hypergraph.nE H)))
      (s : List (Fin (Hypergraph.nV H)))
  → IIEP.AllFire H es s
  → PTA2.AllFire H es s
IIEP→PTA2-AllFire H [] s af = af
IIEP→PTA2-AllFire H (e ∷ es) s (rest , p , eq , af-tail) =
  rest , p , eq , IIEP→PTA2-AllFire H es _ af-tail

-- IndependentSwap converter PTA2→PTA (needed to pass swap-atom-aligned).
PTA2→PTA-IndependentSwap
  : ∀ (H : Hypergraph FlatGen) (e₁ e₂ : Fin (Hypergraph.nE H))
      (s : List (Fin (Hypergraph.nV H)))
  → PTA2.IndependentSwap H e₁ e₂ s
  → PTA.IndependentSwap H e₁ e₂ s
PTA2→PTA-IndependentSwap H e₁ e₂ s (af₁ , af₂) =
  PTA2→PTA-AllFire H (e₁ ∷ e₂ ∷ []) s af₁
  , PTA2→PTA-AllFire H (e₂ ∷ e₁ ∷ []) s af₂

-- ProcessEdges↭Goal does NOT use AllFire — it's defined purely on
-- `proj₁ (process-edges ...)` and the `permute-via-vlab` term content.
-- The two top-level definitions of `ProcessEdges↭Goal` in PTA / PTA2
-- ARE definitionally equal (verified by the type checker accepting
-- a direct identity transport in the probe).  We give a named identity
-- for clarity.
PTA→PTA2-Goal
  : ∀ (H : Hypergraph FlatGen)
      (es₁ es₂ : List (Fin (Hypergraph.nE H)))
      (s : List (Fin (Hypergraph.nV H)))
  → PTA.ProcessEdges↭Goal H es₁ es₂ s
  → PTA2.ProcessEdges↭Goal H es₁ es₂ s
PTA→PTA2-Goal H es₁ es₂ s g = g

--------------------------------------------------------------------------------
-- ## Section 2: The record `APROPMacLaneAtoms`.
--
-- Three nested residuals + one inline atom.

record APROPMacLaneAtoms : Set where
  field
    -- (1) Swap-atom bundle (3 fields):
    --     swap-atom-aligned, swap-with-rest-aligned, swap-already-fires.
    --     See `Sub/SwapAtomAssumptionDischarge.agda`.
    --     (Linear-hyp removed; Linearity now threaded per-call at
    --      H = ⟪f⟫F via `⟪⟫-Linear`.)
    swap-atom-residual : SwapAtomResidual

    -- (2) Iso-induces-edge bundle: REMOVED — discharged constructively
    -- in `Sub/IsoInducesEdgePerm.iso-induces-edge-residual` (Section 9c
    -- of that file), via the trivial Fin-cast ψF strategy + AllFire-
    -- natural-range.  See `Sub/IsoInducesEdgePerm.agda` Section 9c for
    -- the construction.  No field is needed here.

    -- (3) Bridge-to-g, in the SOUND native-↭ form.
    --
    -- This field has the SAME type (verbatim) as
    -- `ProcessTermAligned2Residual.bridge-to-g-permute`:
    -- the final boundary bridge in NEW `permute`-form, taking the
    -- (B-↭) output's `stack-↭` and the iso AND the externally-supplied
    -- X-level `b-stack-↭` (the (b)-output) separately.
    --
    -- It is mathematically sound: it is precisely the goal of the
    -- parent field of `ProcessTermAligned2Residual`, which is
    -- proved constructively in `Sub/ProcessTermAligned.agda`
    -- (the `Sub.ProcessTermAligned.bridge-to-g` companion at the
    -- propositional-eq orientation).
    --
    -- Previous decomposition into (walk, sob, permute-eq-bridge)
    -- has been REMOVED — the third sub-field `permute-eq-bridge`
    -- produced a `Σ stack-eq P` whose first projection
    -- (`stack-eq : map vlab_f … ≡ map vlab_g …`) is REFUTED in
    -- general by the constructive counter-example in
    -- `Sub/StackListEq.agda`, making the record unsound.
    --
    -- The native `Perm.↭`-form below carries the same content
    -- without any propositional list-equality witness, so it is
    -- both sound and sufficient.
    bridge-to-g-permute
      : ∀ {A B} (f g : HomTerm A B) (iso : ⟪ f ⟫ ≅ᴴ ⟪ g ⟫)
          (ψF : Fin (Hypergraph.nE ⟪ g ⟫F)
                → Fin (Hypergraph.nE ⟪ f ⟫F))
          (stack-↭ :
            map (Hypergraph.vlab ⟪ f ⟫F)
                (proj₁ (process-all-edges ⟪ f ⟫F (Hypergraph.dom ⟪ f ⟫F)))
            Perm.↭
            map (Hypergraph.vlab ⟪ g ⟫F)
                (proj₁ (process-all-edges ⟪ g ⟫F (Hypergraph.dom ⟪ g ⟫F))))
          (b-stack-↭ :
            proj₁ (process-all-edges ⟪ f ⟫F (Hypergraph.dom ⟪ f ⟫F))
            Perm.↭
            proj₁ (process-edges ⟪ f ⟫F
                     (map ψF (range (Hypergraph.nE ⟪ g ⟫F)))
                     (Hypergraph.dom ⟪ f ⟫F)))
      → permute (Perm.↭-sym stack-↭)
        ∘ subst₂ HomTerm
            (cong unflatten (full-dom-eq f g))
            refl
            (proj₂ (process-all-edges ⟪ g ⟫F (Hypergraph.dom ⟪ g ⟫F)))
        ≈Term
        permute-via-vlab (Hypergraph.vlab ⟪ f ⟫F) (Perm.↭-sym b-stack-↭)
          ∘ proj₂ (process-edges ⟪ f ⟫F
                     (map ψF (range (Hypergraph.nE ⟪ g ⟫F)))
                     (Hypergraph.dom ⟪ f ⟫F))

--------------------------------------------------------------------------------
-- ## Section 3: Build a `ProcessTermAligned2Residual` from
-- `APROPMacLaneAtoms`.
--
-- This composition wires together:
--   * `build-swap-atom-assumption` (constructive, in Sub/SwapAtomAssumptionDischarge)
--   * `WithSwapAtom.process-edges-↭-topo` (constructive, in Sub/ProcessEdgesPermTopo)
--   * `iso-induces-edge-↭-via-residual` (thin pass-through over
--     IsoInducesEdge, in Sub/IsoInducesEdgePerm)
--   * `Sub/AllFireNatural.AllFire-natural-range` (fully constructive)
--   * the `bridge-to-g-permute` atom (from APROPMacLaneAtoms)
--
-- All conversions between the three AllFire copies use the
-- Section 1 adapters.

module _ (atoms : APROPMacLaneAtoms) where
  open APROPMacLaneAtoms atoms

  -- Build the SwapAtomAssumption value (constructive from the 4 swap-atom
  -- residuals).
  private
    swap-assumption : SwapAtomAssumption
    swap-assumption = build-swap-atom-assumption swap-atom-residual

  open WithSwapAtom swap-assumption using (process-edges-↭-topo)

  -- (B-↭) field for `ProcessTermAligned2Residual`.  We need the
  -- AllFire arguments at the PTA2 level; convert PTA2→PTA, run the
  -- topo derivation, then convert the result Goal back via PTA→PTA2-Goal.
  process-edges-↭-topo-pta2
    : ∀ (H : Hypergraph FlatGen)
        (es₁ es₂ : List (Fin (Hypergraph.nE H)))
        (s : List (Fin (Hypergraph.nV H)))
      (lin : Lin.Linear H)
      (af₁ : PTA2.AllFire H es₁ s) (af₂ : PTA2.AllFire H es₂ s)
    → es₁ Perm.↭ es₂
    → PTA2.ProcessEdges↭Goal H es₁ es₂ s
  process-edges-↭-topo-pta2 H es₁ es₂ s lin af₁ af₂ es-↭ =
    PTA→PTA2-Goal H es₁ es₂ s
      (process-edges-↭-topo H es₁ es₂ s lin
        (PTA2→PTA-AllFire H es₁ s af₁)
        (PTA2→PTA-AllFire H es₂ s af₂)
        es-↭)

  -- (B-swap) field for `ProcessTermAligned2Residual`.  The SwapAtomResidual
  -- already has a `swap-atom-aligned` field at the PTA level; convert
  -- inputs and output.
  swap-atom-aligned-pta2
    : ∀ (H : Hypergraph FlatGen) (e₁ e₂ : Fin (Hypergraph.nE H))
        (s : List (Fin (Hypergraph.nV H)))
    → PTA2.IndependentSwap H e₁ e₂ s
    → PTA2.ProcessEdges↭Goal H (e₁ ∷ e₂ ∷ []) (e₂ ∷ e₁ ∷ []) s
  swap-atom-aligned-pta2 H e₁ e₂ s indep =
    PTA→PTA2-Goal H (e₁ ∷ e₂ ∷ []) (e₂ ∷ e₁ ∷ []) s
      (SwapAtomResidual.swap-atom-aligned swap-atom-residual H e₁ e₂ s
        (PTA2→PTA-IndependentSwap H e₁ e₂ s indep))

  -- (A-nat) constructively, lifted to PTA2.
  allFire-natural-range-pta2
    : ∀ {A B} (f : HomTerm A B)
    → PTA2.AllFire ⟪ f ⟫F (range (Hypergraph.nE ⟪ f ⟫F))
                          (Hypergraph.dom ⟪ f ⟫F)
  allFire-natural-range-pta2 f =
    PTA→PTA2-AllFire ⟪ f ⟫F (range (Hypergraph.nE ⟪ f ⟫F))
                            (Hypergraph.dom ⟪ f ⟫F)
                            (AllFire-natural-range f)

  -- (C-bridge) via `iso-induces-edge-↭-via-residual`.
  -- The latter produces an `IIEP.AllFire` witness; we convert to PTA2.
  iso-induces-edge-↭-pta2
    : ∀ {A B} (f g : HomTerm A B) (iso : ⟪ f ⟫ ≅ᴴ ⟪ g ⟫)
    → Σ[ ψF ∈ (Fin (Hypergraph.nE ⟪ g ⟫F)
                → Fin (Hypergraph.nE ⟪ f ⟫F)) ]
      Σ[ es-↭ ∈
          (range (Hypergraph.nE ⟪ f ⟫F))
          Perm.↭
          (map ψF (range (Hypergraph.nE ⟪ g ⟫F)))
        ]
        PTA2.AllFire ⟪ f ⟫F (map ψF (range (Hypergraph.nE ⟪ g ⟫F)))
                            (Hypergraph.dom ⟪ f ⟫F)
  iso-induces-edge-↭-pta2 f g iso =
    let (ψF , es-↭ , af-iiep) =
          iso-induces-edge-↭-via-residual iso-induces-edge-residual f g iso
    in ψF , es-↭ ,
       IIEP→PTA2-AllFire ⟪ f ⟫F
         (map ψF (range (Hypergraph.nE ⟪ g ⟫F)))
         (Hypergraph.dom ⟪ f ⟫F)
         af-iiep

  -- The new `bridge-to-g-permute` field of `APROPMacLaneAtoms` has type
  -- definitionally equal to `ProcessTermAligned2Residual.bridge-to-g-permute`,
  -- so it plugs in directly with no propositional `stack-eq` wiring.
  --
  -- We keep `bridge-to-g-permute-built` as a thin wrapper so that the
  -- Section-3 dataflow narrative (and the field name expected by the
  -- `to-PTA2-residual` assembly below) is unchanged at call sites.
  bridge-to-g-permute-built
    : ∀ {A B} (f g : HomTerm A B) (iso : ⟪ f ⟫ ≅ᴴ ⟪ g ⟫)
        (ψF : Fin (Hypergraph.nE ⟪ g ⟫F)
              → Fin (Hypergraph.nE ⟪ f ⟫F))
        (stack-↭ :
          map (Hypergraph.vlab ⟪ f ⟫F)
              (proj₁ (process-all-edges ⟪ f ⟫F (Hypergraph.dom ⟪ f ⟫F)))
          Perm.↭
          map (Hypergraph.vlab ⟪ g ⟫F)
              (proj₁ (process-all-edges ⟪ g ⟫F (Hypergraph.dom ⟪ g ⟫F))))
        (b-stack-↭ :
          proj₁ (process-all-edges ⟪ f ⟫F (Hypergraph.dom ⟪ f ⟫F))
          Perm.↭
          proj₁ (process-edges ⟪ f ⟫F
                   (map ψF (range (Hypergraph.nE ⟪ g ⟫F)))
                   (Hypergraph.dom ⟪ f ⟫F)))
    → permute (Perm.↭-sym stack-↭)
      ∘ subst₂ HomTerm
          (cong unflatten (full-dom-eq f g))
          refl
          (proj₂ (process-all-edges ⟪ g ⟫F (Hypergraph.dom ⟪ g ⟫F)))
      ≈Term
      permute-via-vlab (Hypergraph.vlab ⟪ f ⟫F) (Perm.↭-sym b-stack-↭)
        ∘ proj₂ (process-edges ⟪ f ⟫F
                   (map ψF (range (Hypergraph.nE ⟪ g ⟫F)))
                   (Hypergraph.dom ⟪ f ⟫F))
  bridge-to-g-permute-built = bridge-to-g-permute

  -- Assemble the `ProcessTermAligned2Residual` record.
  to-PTA2-residual : ProcessTermAligned2Residual
  to-PTA2-residual = record
    { swap-atom-aligned     = swap-atom-aligned-pta2
    ; process-edges-↭-topo  = process-edges-↭-topo-pta2
    ; AllFire-natural-range = allFire-natural-range-pta2
    ; iso-induces-edge-↭    = iso-induces-edge-↭-pta2
    ; bridge-to-g-permute   = bridge-to-g-permute-built
    }

--------------------------------------------------------------------------------
-- ## Section 4: The main theorem — `process-term-permute-aligned-from-atoms`.
--
-- The c' signature, delivered constructively from the `APROPMacLaneAtoms`
-- record via the `ProcessTermAligned2.WithResidual` machinery.

process-term-permute-aligned-from-atoms
  : (atoms : APROPMacLaneAtoms)
  → ∀ {A B} (f g : HomTerm A B) (iso : ⟪ f ⟫ ≅ᴴ ⟪ g ⟫)
      (stack-↭ :
        map (Hypergraph.vlab ⟪ f ⟫F)
            (proj₁ (process-all-edges ⟪ f ⟫F (Hypergraph.dom ⟪ f ⟫F)))
        Perm.↭
        map (Hypergraph.vlab ⟪ g ⟫F)
            (proj₁ (process-all-edges ⟪ g ⟫F (Hypergraph.dom ⟪ g ⟫F))))
  → permute (Perm.↭-sym stack-↭)
    ∘ subst₂ HomTerm
        (cong unflatten (full-dom-eq f g))
        refl
        (proj₂ (process-all-edges ⟪ g ⟫F (Hypergraph.dom ⟪ g ⟫F)))
    ≈Term
    proj₂ (process-all-edges ⟪ f ⟫F (Hypergraph.dom ⟪ f ⟫F))
process-term-permute-aligned-from-atoms atoms =
  PTA2-WithResidual.process-term-permute-aligned-discharge
    (to-PTA2-residual atoms)

--------------------------------------------------------------------------------
-- ## Section 5: Summary.
--
-- ### Final field list of `APROPMacLaneAtoms`
--
-- The record exposes TWO nested residual records and ONE bridge atom:
--
--   * `swap-atom-residual.swap-atom-aligned`       — Sub/SwapAtomAssumptionDischarge:128
--                                                  — Mac Lane / Kelly atom (2 adjacent edges).
--   * `swap-atom-residual.swap-with-rest-aligned`  — Sub/SwapAtomAssumptionDischarge:136
--                                                  — swap-with-rest content.
--   * `swap-atom-residual.swap-already-fires`      — Sub/SwapAtomAssumptionDischarge:147
--                                                  — topological-soundness atom.
--   * `swap-atom-residual.Linear-hyp`              — Sub/SwapAtomAssumptionDischarge:158
--                                                  — Linearity hypothesis (∀ H).
--
--   (`allFire-residual` / `iso-induces-edge-↭-direct` REMOVED — now
--    discharged constructively as `iso-induces-edge-residual` in
--    Sub/IsoInducesEdgePerm.agda Section 9c, via Fin-cast ψF +
--    AllFire-natural-range on ⟪f⟫F.)
--
--   * `bridge-to-g-permute`                        — this file
--                                                  — verbatim same type as
--                                                    `ProcessTermAligned2Residual.bridge-to-g-permute`
--                                                    (native `Perm.↭`-form, no
--                                                    propositional `Σ stack-eq`).
--                                                    Replaces the earlier
--                                                    (walk, sob, permute-eq-bridge)
--                                                    decomposition, whose
--                                                    `permute-eq-bridge` was unsound
--                                                    (see Sub/StackListEq.agda).
--
-- ### Constructive composition
--
-- Given `APROPMacLaneAtoms`, the c' signature is delivered constructively
-- via `process-term-permute-aligned-from-atoms`, which threads the atoms
-- through:
--
--   * `Sub/SwapAtomAssumptionDischarge.build-swap-atom-assumption`,
--   * `Sub/ProcessEdgesPermTopo.WithSwapAtom.process-edges-↭-topo`,
--   * `Sub/IsoInducesEdgePerm.iso-induces-edge-↭-via-residual`,
--   * `Sub/AllFireNatural.AllFire-natural-range` (fully constructive — no
--     residual needed),
--
-- and feeds the result into
-- `ProcessTermAligned2.WithResidual.process-term-permute-aligned-discharge`.
--
-- The generic `Assumptions` record (smc-faithfulness) is NOT used in this
-- file — the c' chain is closed at the (Bridge-permute) atom + the
-- SwapAtomResidual/IsoInducesEdge sub-fields.
--
-- ### File status
--
-- `--safe --with-K` clean.  NO `postulate` declarations.
--------------------------------------------------------------------------------
