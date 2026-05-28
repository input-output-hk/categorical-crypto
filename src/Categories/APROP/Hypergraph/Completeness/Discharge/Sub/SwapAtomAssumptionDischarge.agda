{-# OPTIONS --safe --with-K #-}

--------------------------------------------------------------------------------
-- ## Constructive discharge of `SwapAtomAssumption`
--
-- The parent record `SwapAtomAssumption` (in `ProcessEdgesPermTopo.agda`)
-- has four fields:
--
--   (1) `swap-atom-aligned`         — Mac Lane / Kelly coherence atom on
--                                     two adjacent edges (irreducible).
--   (2) `swap-with-rest-aligned`    — single swap with a non-trivial rest
--                                     list (Mac Lane + stack-↭ + suffix
--                                     induction).
--   (3) `prep-aligned`              — same-head edge-step bridging.
--   (4) `trans-intermediate-allfire` — intermediate AllFire witness.
--
-- ## What this file delivers
--
-- We construct a `SwapAtomAssumption` from a strictly NARROWER residual
-- record `SwapAtomResidual` whose fields are the genuinely-irreducible
-- atoms (Mac Lane + topological soundness + linearity).
--
-- Concretely:
--
--   * Field (3) `prep-aligned` — CONSTRUCTIVELY discharged here.
--     Routes through `process-edges-cons-success` (`SwapMacLane.agda`)
--     and `just`-injectivity for Σ-pairs.  No new postulates.
--
--   * Field (4) `trans-intermediate-allfire` — CONSTRUCTIVELY discharged
--     here.  Routes through `WithSwap.AllFire-edge-↭` from
--     `AllFireEdgePerm.agda`, in turn discharged from
--     `AllFireEdgeSwap.WithTopoSoundness` (which packages the
--     `swap-already-fires` topological-soundness atom).
--
--   * Fields (1) `swap-atom-aligned` and (2) `swap-with-rest-aligned`
--     are NOT closed.  They remain in the residual record:
--
--       - (1) is the irreducible Mac Lane / Kelly atom; per the task
--         brief it cannot be discharged without symmetric-fragment
--         `solveM`-style normalisation.
--       - (2) `swap-with-rest-aligned` requires either an auxiliary
--         `process-edges-stack-↭` lemma (≥150 LOC of Mac Lane +
--         naturality content; see `ProcessEdgesStackPerm.agda`) or a
--         re-implementation of the `_↭_`-induction with the swap case
--         handled by direct decomposition.  Either route needs Mac Lane
--         content beyond the parent `swap-atom-aligned` (specifically
--         the stack-permute coherence between the post-prefix stacks).
--
-- The residual record exposes THREE fields:
--
--   `swap-atom-aligned`      — Mac Lane atom (field 1)
--   `swap-with-rest-aligned` — full swap-with-rest (field 2)
--   `swap-already-fires`     — topological soundness for AllFire swap
--                              (needed for field 4 via `AllFire-edge-↭`)
--
-- The former `Linear-hyp : ∀ H → Linear H` field has been REMOVED.
-- Linearity is now threaded per-call through the
-- `SwapAtomAssumption.trans-intermediate-allfire` field's extra
-- `Linear H` argument, and supplied at the top-level consumer (where
-- H = ⟪f⟫F) via `Linearity.⟪⟫-Linear`.
--
-- The audit said fields 2-4 are ~175 LOC of constructive combinatorial
-- algebra.  In practice:
--
--   * Field 3 (prep-aligned)              — fully constructive (~50 LOC)
--   * Field 4 (trans-intermediate-allfire) — derivable from
--      `AllFire-edge-↭` (`AllFireEdgePerm`), which depends on
--      `AllFire-edge-↭-swap`.  The latter is FALSE under just Linearity
--      (per `EdgeReorder.agda`'s counter-example).  It needs an
--      additional `swap-already-fires` premise — this is the
--      irreducible topological-soundness atom NOT implied by Linearity
--      or AllFire on the original order alone.  Hence Field 4's
--      "AllFire algebra" decomposition retains this single residual.
--   * Field 2 (swap-with-rest-aligned) — genuinely requires Mac Lane
--     content beyond `swap-atom-aligned` (stack-permute coherence on
--     the post-prefix stacks + suffix induction).  Retained as a
--     residual.
--
-- ## File is `--safe --with-K`-clean.  NO postulate declarations.
--------------------------------------------------------------------------------

open import Categories.APROP
open import Categories.APROP.Hypergraph.Solver.Signature using (APROPSignatureDec)

module Categories.APROP.Hypergraph.Completeness.Discharge.Sub.SwapAtomAssumptionDischarge
  (sig-dec : APROPSignatureDec) where

open APROPSignatureDec sig-dec using (sig)
open APROP sig

open import Categories.APROP.Hypergraph.Core using (Hypergraph)
open import Categories.APROP.Hypergraph.FromAPROP sig using (FlatGen)
open import Categories.APROP.Hypergraph.Completeness.Linearity sig using (Linear)
open import Categories.APROP.Hypergraph.Completeness.Discharge.Sub.ProcessTermAligned sig-dec
  using (AllFire; IndependentSwap; ProcessEdges↭Goal)
open import Categories.APROP.Hypergraph.Completeness.Discharge.Sub.ProcessEdgesPermTopo sig-dec
  using (SwapAtomAssumption)
open import Categories.APROP.Hypergraph.Completeness.Discharge.Sub.AllFireEdgePerm sig-dec
  using (AllFireEdgePermSwap; module WithSwap)
open import Categories.APROP.Hypergraph.Completeness.Discharge.Sub.AllFireEdgeSwap sig-dec
  using (AllFireEdgePermSwapTopo; module WithTopoSoundness)
open import Categories.APROP.Hypergraph.Completeness.Discharge.Sub.SwapAtomCombinatorial sig-dec
  using (SwapAtomInput; module FromInputs)

open import Data.Fin using (Fin)
open import Data.List using (List; []; _∷_)
import Data.List.Relation.Binary.Permutation.Propositional as Perm

--------------------------------------------------------------------------------
-- ## Section 1: the minimal residual record.
--
-- The three fields are:
--
--   (i)   `swap-atom-aligned`      — Mac Lane / Kelly atom on a 2-edge
--                                    independent swap (irreducible).
--   (ii)  `swap-with-rest-aligned` — full swap-with-rest content
--                                    (Mac Lane + stack-↭ coherence +
--                                    suffix induction).
--   (iii) `swap-already-fires`     — topological-soundness for AllFire
--                                    swap (NOT implied by Linearity,
--                                    per `EdgeReorder.agda`).
--
-- The former `Linear-hyp : ∀ H → Linear H` field has been REMOVED.
--
-- A downstream consumer (e.g., `ProcessTermAligned.agda`) supplies these
-- conditionally on `H = ⟪ f ⟫F`-shape: for translated hypergraphs,
-- `Linear ⟪ f ⟫F` is constructive (`Linearity.⟪⟫-Linear`), and the
-- topological-soundness and Mac Lane atoms are provided by the
-- corresponding sub-discharge modules.

record SwapAtomResidual : Set where
  field
    -- (i) The Mac Lane / Kelly coherence atom.
    swap-atom-aligned
      : ∀ (H : Hypergraph FlatGen) (e₁ e₂ : Fin (Hypergraph.nE H))
          (s : List (Fin (Hypergraph.nV H)))
      → IndependentSwap H e₁ e₂ s
      → ProcessEdges↭Goal H (e₁ ∷ e₂ ∷ []) (e₂ ∷ e₁ ∷ []) s

    -- (ii) Single swap with non-trivial rest list.
    swap-with-rest-aligned
      : ∀ (H : Hypergraph FlatGen)
          (e₁ e₂ : Fin (Hypergraph.nE H))
          (xs ys : List (Fin (Hypergraph.nE H)))
          (s : List (Fin (Hypergraph.nV H)))
        (rest-↭ : xs Perm.↭ ys)
        (af₁ : AllFire H (e₁ ∷ e₂ ∷ xs) s)
        (af₂ : AllFire H (e₂ ∷ e₁ ∷ ys) s)
      → ProcessEdges↭Goal H (e₁ ∷ e₂ ∷ xs) (e₂ ∷ e₁ ∷ ys) s

    -- (iii) Topological-soundness atom for AllFire swap.
    swap-already-fires
      : ∀ (H : Hypergraph FlatGen)
          (e₁ e₂ : Fin (Hypergraph.nE H))
          (xs : List (Fin (Hypergraph.nE H)))
          (s : List (Fin (Hypergraph.nV H)))
      → Linear H
      → AllFire H (e₁ ∷ e₂ ∷ xs) s
      → AllFire H (e₂ ∷ e₁ ∷ []) s

    -- (iv) FORMER `Linear-hyp` field has been REMOVED.  The Linearity
    -- hypothesis is now threaded per-call through
    -- `SwapAtomAssumption.trans-intermediate-allfire` (which takes
    -- `Linear H` as an explicit argument).  At the top-level consumer
    -- (`ProcessTermAligned2.WithResidual`), Linearity is instantiated
    -- at `H = ⟪f⟫F` via `Linearity.⟪⟫-Linear f` — no `∀ H → Linear H`
    -- universal hypothesis is needed.

--------------------------------------------------------------------------------
-- ## Section 2: the constructive composition.
--
-- Given a `SwapAtomResidual`, build a full `SwapAtomAssumption` by
-- composing:
--
--   * `SwapAtomInput`              from `swap-atom-aligned`
--   * `AllFireEdgePermSwapTopo`    from `swap-already-fires`
--   * `WithTopoSoundness`          to derive `AllFireEdgePermSwap`
--   * `FromInputs`                 (in `SwapAtomCombinatorial.agda`),
--                                  parameterised by the SwapAtomInput,
--                                  the derived AllFireEdgePermSwap, and
--                                  `Linear-hyp`
--   * `FromInputs.FromSwapWithRest` with `swap-with-rest-aligned`.

module SwapAtomAssumptionDischarge where

  build-swap-atom-assumption : SwapAtomResidual → SwapAtomAssumption
  build-swap-atom-assumption res = result
    where
      open SwapAtomResidual res

      -- Wrap the Mac Lane atom into a SwapAtomInput.
      swp : SwapAtomInput
      swp = record { swap-atom-aligned = swap-atom-aligned }

      -- Wrap the topological-soundness atom into an
      -- AllFireEdgePermSwapTopo, then derive an AllFireEdgePermSwap.
      topo : AllFireEdgePermSwapTopo
      topo = record { swap-already-fires = swap-already-fires }

      allFireSwap : AllFireEdgePermSwap
      allFireSwap = WithTopoSoundness.to-AllFireEdgePermSwap topo

      -- Apply `FromInputs` to obtain the partial discharge (fields 1,
      -- 3, 4 closed; field 2 = `swap-with-rest-aligned` exposed as a
      -- sub-module parameter).  Linearity is no longer threaded as a
      -- universal hypothesis — it is supplied per-call through
      -- `SwapAtomAssumption.trans-intermediate-allfire`'s extra
      -- `Linear H` parameter.
      open FromInputs swp allFireSwap

      -- Open the `FromSwapWithRest` sub-module with the residual's
      -- `swap-with-rest-aligned` field.  This yields the complete
      -- `to-swap-atom-assumption : SwapAtomAssumption`.
      open FromSwapWithRest swap-with-rest-aligned

      result : SwapAtomAssumption
      result = to-swap-atom-assumption

--------------------------------------------------------------------------------
-- ## Section 3: convenience re-export.
--
-- Expose the discharge function at the top level for direct consumption.

open SwapAtomAssumptionDischarge public using (build-swap-atom-assumption)

--------------------------------------------------------------------------------
-- ## Summary of constructive closure
--
-- Field 1 (`swap-atom-aligned`):
--   NOT closed.  Irreducible Mac Lane atom (per the task brief).
--
-- Field 2 (`swap-with-rest-aligned`):
--   NOT closed.  Requires Mac Lane content beyond `swap-atom-aligned`
--   (stack-permute coherence on post-prefix stacks + structural
--   induction on the suffix).  Per the audit's "175 LOC of constructive
--   combinatorial algebra" estimate, this is achievable in principle —
--   see `ProcessEdgesStackPerm.agda` for the relevant infrastructure
--   (`StepStackPermResidual` + `SuffixPermResidual` + closure).  In
--   practice the closure routes through additional residuals (the
--   `StepStackPermResidual` is itself a non-trivial Mac Lane atom),
--   leaving the original `swap-with-rest-aligned` as the most compact
--   single residual.
--
-- Field 3 (`prep-aligned`):
--   CLOSED constructively via `SwapAtomCombinatorial.FromInputs.prep-aligned`,
--   which uses `process-edges-cons-success` + Σ-injectivity of `just`.
--
-- Field 4 (`trans-intermediate-allfire`):
--   CLOSED constructively via `SwapAtomCombinatorial.FromInputs
--   .trans-intermediate-allfire`, which routes through
--   `WithSwap.AllFire-edge-↭` + `WithTopoSoundness` + the
--   `swap-already-fires` topological-soundness atom.  The "AllFire
--   algebra" the audit refers to does indeed bottom out in a single
--   topological-soundness atom (not implied by Linearity) — captured
--   here as the residual field `swap-already-fires`.
--
-- ## Final residual record: THREE fields.
--
--   (i)   `swap-atom-aligned`       — irreducible Mac Lane atom.
--   (ii)  `swap-with-rest-aligned`  — full swap-with-rest content.
--   (iii) `swap-already-fires`      — topological-soundness for swap.
--
-- The former `Linear-hyp : ∀ H → Linear H` field has been REMOVED;
-- Linearity is now supplied per-call at H = ⟪f⟫F via `⟪⟫-Linear` from
-- `Categories.APROP.Hypergraph.Completeness.Linearity`.
--
-- File is `--safe --with-K`-clean.  No `postulate` declarations.
--------------------------------------------------------------------------------
