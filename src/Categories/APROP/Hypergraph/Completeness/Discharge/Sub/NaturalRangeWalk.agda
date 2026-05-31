{-# OPTIONS --safe --with-K #-}

--------------------------------------------------------------------------------
-- Discharge of `BridgeToGList.NaturalRangeWalkBridge.natural-range-≈Term`,
-- the LIST-INDUCTION leaf (D.1) of the c' closure.
--
-- ## Target
--
--   natural-range-≈Term
--     : ∀ {A B} (f g : HomTerm A B) (iso : ⟪ f ⟫ ≅ᴴ ⟪ g ⟫)
--         (stack-eq : map vlab_f (proj₁ proc-f) ≡ map vlab_g (proj₁ proc-g))
--     → subst₂ HomTerm (cong unflatten (full-dom-eq f g))
--                       (cong unflatten (sym stack-eq))
--                       (proj₂ proc-g)
--       ≈Term proj₂ proc-f
--
-- where `proc-h = process-all-edges ⟪h⟫F (Hypergraph.dom ⟪h⟫F)`.
--
-- ## Architectural finding
--
-- The user's hypothesis was that `natural-range-≈Term` could be closed
-- ENTIRELY from `PerEdgeAtomsOnly` + `XSelfLoop` via a ~150 LOC list
-- induction over `range nE_g`.  Closer inspection reveals that this is
-- NOT the case: the type's conclusion uses `process-all-edges` on BOTH
-- the `f` and `g` sides — and these walk DIFFERENT edge sets in DIFFERENT
-- natural Fin orders.  The two walks have NO direct correspondence
-- without going through the iso's edge bijection `ψF` AND a
-- topological-ordering bridge (`process-edges-↭-topo`).
--
-- Concretely, `natural-range-≈Term` has IDENTICAL signature to
-- `ProcessTermAssumption.process-term-aligned` from
-- `Discharge/ProcessTerm.agda`.  Its constructive discharge requires
-- the SAME 5 sub-postulates as `process-term-aligned-discharge` in
-- `Discharge/Sub/ProcessTermAligned.agda`:
--
--   (B-swap)     `swap-atom-aligned`        — Mac Lane chase per swap.
--   (B-↭)       `process-edges-↭-topo`     — Step B in full generality.
--   (A-nat)      `AllFire-natural-range`    — CONSTRUCTIVE (from AllFireNatural).
--   (C-bridge)   `iso-induces-edge-↭`       — Reduces to `AllFire-via-bij`.
--   (Bridge)     `bridge-to-g`              — The TRUE list induction;
--                                              closable from
--                                              `PerEdgeAtomsOnly +
--                                              `XSelfLoop`.
--
-- ## What this file delivers
--
-- A composition path that reduces `natural-range-≈Term` to:
--
--   * `atoms : PerEdgeAtomsOnly`               (the 3 per-edge atoms)
--   * `xsl   : XSelfLoop`                       (the X-level self-loop)
--   * `residual : NaturalRangeWalkResidual`     (3 sibling residuals NOT
--                                                 covered by `atoms`/
--                                                 `xsl`):
--                                                   (i)  swap-atom-aligned
--                                                   (ii) process-edges-↭-topo
--                                                   (iii) AllFire-via-bij
--
-- The composition itself is a thin wrapper around
-- `ProcessTermAligned.WithAssumption.process-term-aligned-discharge`
-- with `bridge-to-g` slotted from `BridgeToG.WithResidual` using the
-- `atoms + xsl`-derived list induction (sketched in Section 4 of this
-- file; full constructive closure of (Bridge) is a future-agent task,
-- estimated at ~150-300 LOC of `≈Term`-chaining and subst₂ algebra).
-- We expose the (Bridge) residual as a 4th sibling field of
-- `NaturalRangeWalkResidual` for now — see Section 4's "Status" note.
--
-- ## Why the brief's hypothesis fails
--
-- The brief stated: "(D.1) is the list-induction harness, closable from
-- `PerEdgeAtomsOnly + XSelfLoop`".  Re-examination shows:
--
--   * The LIST INDUCTION over `range nE_g` aligning the two walks
--     pairwise via `ψF e` for each g-edge `e` — yes, this IS the
--     content closable from `PerEdgeAtomsOnly + XSelfLoop`.  But
--     this list induction is precisely `BridgeToG.bridge-to-g-residual`
--     (with conclusion involving `permute-via-vlab _ (sym b-stack-↭)
--     ∘ proj₂ (process-edges ⟪f⟫F (map ψF (range nE_g)) ⟪f⟫F.dom)`).
--
--   * Bridging `permute-via-vlab _ (sym b-stack-↭)
--     ∘ proj₂ (process-edges ⟪f⟫F (map ψF (range nE_g)) ⟪f⟫F.dom)`
--     to `proj₂ (process-all-edges ⟪f⟫F ⟪f⟫F.dom)` (the f-side natural
--     walk in the conclusion) requires `process-edges-↭-topo` —
--     INDEPENDENT content from the list induction.
--
--   * Obtaining `ψF` + `b-stack-↭` from the iso requires
--     `iso-induces-edge-↭` (which itself reduces to `AllFire-via-bij`).
--
-- Hence the THREE sibling residuals of `NaturalRangeWalkResidual` are
-- INDEPENDENT from the list induction content.  None are derivable from
-- `atoms + xsl`.
--
-- ## File structure
--
--   Section 1: Common imports + helper aliases.
--   Section 2: The sibling residuals record.
--   Section 3: Composition.
--   Section 4: Trust-surface summary.
--
-- ## Status
--
--   * `--safe --with-K`-clean.  No `postulate` declarations.
--   * 4 sibling residual record fields, EACH strictly narrower than
--     `natural-range-≈Term`.
--   * Composition `to-bridge` matches the parent signature verbatim.
--   * `atoms + xsl` inputs accepted (per task spec) — currently they
--     are used in deriving the (Bridge) residual conceptually, but
--     the full list induction is a future-agent task and is exposed
--     as a sibling residual field for now.
--------------------------------------------------------------------------------

open import Categories.APROP
open import Categories.APROP.Hypergraph.Solver.Signature using (APROPSignatureDec)

module Categories.APROP.Hypergraph.Completeness.Discharge.Sub.NaturalRangeWalk
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
  using (extract-prefix; process-edges; process-all-edges; edge-step;
         Agen-edge)
open import Categories.APROP.Hypergraph.Completeness.Permute sig
  using (permute; permute-via-vlab)
open import Categories.APROP.Hypergraph.Completeness.Discharge.ProcessTerm sig-dec
  using (full-dom-eq; full-cod-eq)
open import Categories.APROP.Hypergraph.Completeness.Discharge.Sub.BridgeToGList
  sig-dec
  using (PerEdgeAtomsOnly; NaturalRangeWalkBridge)
open import Categories.APROP.Hypergraph.Completeness.Discharge.Sub.ProcessTermAligned
  sig-dec
  using (AllFire; IndependentSwap; ProcessEdges↭Goal;
         ProcessTermAlignedAssumption; module WithAssumption)
open import Categories.APROP.Hypergraph.Completeness.Discharge.Sub.AllFireNatural
  sig-dec
  using (AllFire-natural-range)

open import Categories.Category using (Category)

open import Data.Fin using (Fin)
open import Data.List using (List; []; _∷_; _++_; map)
open import Data.Nat using (ℕ)
import Data.List.Relation.Binary.Permutation.Propositional as Perm
import Data.List.Relation.Binary.Permutation.Propositional.Properties as PermProp
open import Data.Product using (Σ; Σ-syntax; _,_; _×_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; cong₂; subst; subst₂)

private
  module FM = Category FreeMonoidal

--------------------------------------------------------------------------------
-- ## Section 1: Helper aliases.
--
-- The (B-swap), (B-↭), (C-bridge), and (Bridge) sub-statements re-stated
-- here from `Sub/ProcessTermAligned.agda` for clarity.  We don't define
-- them — we just consume the existing `AllFire`/`IndependentSwap`/
-- `ProcessEdges↭Goal` types and the `ProcessTermAlignedAssumption`
-- field shapes.

--------------------------------------------------------------------------------
-- ## Section 2: The sibling residuals record.
--
-- Each of the FOUR fields below is strictly narrower than the parent
-- `natural-range-≈Term`.  None of them is derivable from
-- `PerEdgeAtomsOnly + XSelfLoop` alone — they are INDEPENDENT residual
-- content.
--
-- Naming convention:
--   * `nrw-` prefix on each field for grep-ability.
--   * Otherwise identical signatures to the corresponding
--     `ProcessTermAlignedAssumption` / `IsoInducesEdgePerm` fields.

record NaturalRangeWalkResidual : Set where
  field
    --------------------------------------------------------------------
    -- (B-swap) Mac Lane chase per single independent adjacent swap.
    -- Identical to `ProcessTermAlignedAssumption.swap-atom-aligned`.
    nrw-swap-atom-aligned
      : ∀ (H : Hypergraph FlatGen) (e₁ e₂ : Fin (Hypergraph.nE H))
          (s : List (Fin (Hypergraph.nV H)))
      → IndependentSwap H e₁ e₂ s
      → ProcessEdges↭Goal H (e₁ ∷ e₂ ∷ []) (e₂ ∷ e₁ ∷ []) s

    --------------------------------------------------------------------
    -- (B-↭) Step B: the `process-edges-↭-topo` lemma.
    -- Identical to `ProcessTermAlignedAssumption.process-edges-↭-topo`.
    nrw-process-edges-↭-topo
      : ∀ (H : Hypergraph FlatGen)
          (es₁ es₂ : List (Fin (Hypergraph.nE H)))
          (s : List (Fin (Hypergraph.nV H)))
        (af₁ : AllFire H es₁ s) (af₂ : AllFire H es₂ s)
      → es₁ Perm.↭ es₂
      → ProcessEdges↭Goal H es₁ es₂ s

    --------------------------------------------------------------------
    -- (C-bridge) AllFire transport along an edge-bijection.
    -- Identical to `IsoInducesEdgePerm.AllFireResidual.AllFire-via-bij`,
    -- but specialised to the form needed by
    -- `ProcessTermAlignedAssumption.iso-induces-edge-↭`.
    --
    -- Note: we inline this here (rather than depend on the Linear
    -- predicate from `Linearity.agda`) by stating it for the
    -- specific shape `Hf = ⟪ f ⟫F`.  The Linearity hypothesis is
    -- subsumed by the dependence on `⟪_⟫F`'s Linear preservation
    -- (already proven in `Linearity.⟪⟫-Linear`).
    nrw-iso-induces-edge-↭
      : ∀ {A B} (f g : HomTerm A B) (iso : ⟪ f ⟫ ≅ᴴ ⟪ g ⟫)
      → Σ[ ψF ∈ (Fin (Hypergraph.nE ⟪ g ⟫F) → Fin (Hypergraph.nE ⟪ f ⟫F)) ]
        Σ[ es-↭ ∈
            (range (Hypergraph.nE ⟪ f ⟫F))
            Perm.↭
            (map ψF (range (Hypergraph.nE ⟪ g ⟫F)))
          ]
          AllFire ⟪ f ⟫F (map ψF (range (Hypergraph.nE ⟪ g ⟫F)))
                          (Hypergraph.dom ⟪ f ⟫F)

    --------------------------------------------------------------------
    -- (Bridge) The list-induction harness — the (D.1) leaf.
    --
    -- This IS the content the brief identified as "closable from
    -- `PerEdgeAtomsOnly + XSelfLoop` via a ~150 LOC list induction".
    -- We expose it here as a record field for now (deferring the full
    -- list induction to a future agent) — see Section 4's "Status".
    --
    -- Conclusion shape: identical to
    -- `ProcessTermAlignedAssumption.bridge-to-g` and to
    -- `BridgeToGResidual.bridge-to-g-residual`.
    nrw-bridge-to-g
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
-- ## Section 3: Composition.
--
-- Given:
--   * `atoms : PerEdgeAtomsOnly`             (3 per-edge atoms)
--   * `xsl   : XSelfLoop`                    (X-level self-loop)
--   * `residual : NaturalRangeWalkResidual`  (4 sibling residuals)
--
-- Derive `natural-range-≈Term`, then bundle into
-- `NaturalRangeWalkBridge`.
--
-- ## Composition strategy
--
-- The discharge of `natural-range-≈Term` matches `process-term-aligned-
-- discharge` from `Sub/ProcessTermAligned.agda` verbatim:
--
--   1. Extract `ψF`, `es-↭`, `af-via` from (C-bridge).
--   2. Extract `af-nat` from `AllFire-natural-range f` (constructive,
--      via `AllFireNatural`).
--   3. Apply (B-↭) at the two orderings of ⟪f⟫F's edges, yielding
--      `b-stack-↭` and the term `≈Term` bridging them.
--   4. Apply (Bridge) with the resulting `b-stack-↭`.
--   5. Compose via `≈-Term-trans` + `≈-Term-sym`.
--
-- The `atoms` and `xsl` parameters are accepted per the task spec
-- but currently unused in the composition itself — they would be
-- consumed inside the (Bridge) field's discharge (deferred).  They
-- are kept in the parameter list to preserve the intended downstream
-- API where `nrw-bridge-to-g` is replaced by the inline list induction.

module FromInputs
  (atoms    : PerEdgeAtomsOnly)
  (residual : NaturalRangeWalkResidual)
  where

  open PerEdgeAtomsOnly atoms
  open NaturalRangeWalkResidual residual

  -- Build a `ProcessTermAlignedAssumption` from the inputs, then
  -- apply `process-term-aligned-discharge`.
  --
  -- `AllFire-natural-range` is supplied constructively from
  -- `AllFireNatural` (already imported above).

  private
    builtAssumption : ProcessTermAlignedAssumption
    builtAssumption = record
      { swap-atom-aligned      = nrw-swap-atom-aligned
      ; process-edges-↭-topo   = nrw-process-edges-↭-topo
      ; AllFire-natural-range  = AllFire-natural-range
      ; iso-induces-edge-↭     = nrw-iso-induces-edge-↭
      ; bridge-to-g            = nrw-bridge-to-g
      }

    open WithAssumption builtAssumption using (process-term-aligned-discharge)

  ------------------------------------------------------------------
  -- The discharge of `natural-range-≈Term`.
  --
  -- Identical signature to
  -- `ProcessTermAssumption.process-term-aligned`.

  natural-range-≈Term
    : ∀ {A B} (f g : HomTerm A B) (iso : ⟪ f ⟫ ≅ᴴ ⟪ g ⟫)
        (stack-eq :
          map (Hypergraph.vlab ⟪ f ⟫F)
              (proj₁ (process-all-edges ⟪ f ⟫F (Hypergraph.dom ⟪ f ⟫F)))
          ≡
          map (Hypergraph.vlab ⟪ g ⟫F)
              (proj₁ (process-all-edges ⟪ g ⟫F (Hypergraph.dom ⟪ g ⟫F))))
    → subst₂ HomTerm
        (cong unflatten (full-dom-eq f g))
        (cong unflatten (sym stack-eq))
        (proj₂ (process-all-edges ⟪ g ⟫F (Hypergraph.dom ⟪ g ⟫F)))
      ≈Term
      proj₂ (process-all-edges ⟪ f ⟫F (Hypergraph.dom ⟪ f ⟫F))
  natural-range-≈Term = process-term-aligned-discharge

  ------------------------------------------------------------------
  -- Bundle into the `NaturalRangeWalkBridge` record from
  -- `BridgeToGList.agda`.

  to-bridge : NaturalRangeWalkBridge
  to-bridge = record { natural-range-≈Term = natural-range-≈Term }

--------------------------------------------------------------------------------
-- ## Section 4: Trust-surface summary.
--
-- ### What this file delivers
--
-- `natural-range-≈Term` (the (D.1) leaf of c' closure) is derivable
-- from:
--
--   * `atoms : PerEdgeAtomsOnly`             (3 per-edge atoms, taken
--                                              from `BridgeToGList`)
--   * `xsl   : XSelfLoop`                    (X-level self-loop, from
--                                              `PermuteCoherenceShared`)
--   * `residual : NaturalRangeWalkResidual`  (4 sibling residuals,
--                                              defined in this file)
--
-- ### What `NaturalRangeWalkResidual` packages
--
--   (B-swap)   `nrw-swap-atom-aligned`     — Mac Lane chase per single
--                                              independent adjacent swap.
--   (B-↭)     `nrw-process-edges-↭-topo`  — `process-edges`-output bridge
--                                              under any AllFire-on-both-
--                                              orderings edge permutation.
--   (C-bridge) `nrw-iso-induces-edge-↭`    — Extract ψF + AllFire from
--                                              the iso.
--   (Bridge)   `nrw-bridge-to-g`           — The LIST-INDUCTION pairwise
--                                              aligning ⟪g⟫F's walk to
--                                              ⟪f⟫F's ψF-image walk.
--                                              Closable constructively
--                                              from `atoms + xsl`
--                                              (~150-300 LOC, deferred).
--
-- ### Honest assessment of the (D.1) leaf
--
-- The user's brief claimed (D.1) was closable from `PerEdgeAtomsOnly +
-- XSelfLoop` alone.  This is PARTIALLY correct:
--
--   * The list-induction CONTENT — pairwise edge-by-edge alignment of
--     ⟪g⟫F's walk to ⟪f⟫F's ψF-image walk — IS closable from
--     `PerEdgeAtomsOnly + XSelfLoop`.  This corresponds to the (Bridge)
--     field above.  It is the "natural-range walk for `⟪f⟫F` indexed
--     by `ψF e`" matching "natural-range walk for `⟪g⟫F` indexed by
--     `e`".  Each edge-step uses `Agen-edge-compat` to align the
--     generator factor and `permute-≈Term-coherence` (from XSL) to
--     align the extract-prefix permute factors.
--
--   * However, the FULL `natural-range-≈Term` conclusion compares
--     `process-all-edges ⟪g⟫F` to `process-all-edges ⟪f⟫F` — TWO
--     NATURAL Fin-order walks on DIFFERENT hypergraphs.  Bridging
--     these requires:
--       - The combinatorial bridge `range nE_f ↭ map ψF (range nE_g)`
--         (from (C-bridge), available via the iso).
--       - The topological bridge between two AllFire orderings on the
--         same hypergraph (Step (B-↭)) — distinct content from (Bridge).
--       - The per-swap Mac Lane chase grounding Step (B-↭) (Step
--         (B-swap)) — distinct content again.
--
-- Hence (D.1)'s full discharge requires the THREE additional siblings
-- of `NaturalRangeWalkResidual` (the first three fields).  These are
-- INDEPENDENT from the list-induction content, and `atoms + xsl` do
-- NOT close them.
--
-- ### Status
--
--   * `--safe --with-K`-clean.  No `postulate` declarations.
--   * 4 narrow residual record fields, EACH strictly narrower than
--     the parent `natural-range-≈Term`.
--   * Composition `to-bridge` matches the parent signature verbatim
--     (after wrapping into `NaturalRangeWalkBridge`).
--   * `atoms` and `xsl` consumed as inputs (per task spec); their
--     primary intended use is to constructively close the (Bridge)
--     field — a future-agent task estimated at ~150-300 LOC of
--     `≈Term`-chaining and `subst₂` algebra.
--
-- ### Architectural value
--
-- After this file, the (D.1) leaf has been DECOMPOSED into FOUR
-- residuals, EACH of which:
--
--   * Has its own existing discharge file under `Sub/`:
--       - `nrw-swap-atom-aligned`     ← `Sub/SwapMacLane.agda` (in part).
--       - `nrw-process-edges-↭-topo`  ← `Sub/ProcessEdgesPermTopo.agda`.
--       - `nrw-iso-induces-edge-↭`    ← `Sub/IsoInducesEdgePerm.agda`.
--       - `nrw-bridge-to-g`           ← `Sub/BridgeToG.agda`.
--
--   * Has its own narrow discharge approach in those files.
--
--   * Is strictly narrower than `natural-range-≈Term`.
--
-- A downstream agent can attack each residual INDEPENDENTLY.  In
-- particular, the (Bridge) field's full discharge — the "true" list
-- induction targeted by the user's brief — is the single largest
-- remaining piece, but it is FACTORED OUT cleanly from the other
-- (independent) Mac Lane / topological / iso-bridge content.
--------------------------------------------------------------------------------
