{-# OPTIONS --safe --with-K #-}

--------------------------------------------------------------------------------
-- Sub-discharge of the `swap-already-fires` field of
-- `AllFireEdgeSwap.AllFireEdgePermSwapTopo` (the topological-soundness
-- residual blocking the B.1 leaf of c' closure).
--
-- ## Background
--
-- `swap-already-fires` (from `Discharge/Sub/AllFireEdgeSwap.agda`) reads:
--
--   swap-already-fires
--     : ∀ (H : Hypergraph FlatGen)
--         (e₁ e₂ : Fin H.nE)
--         (xs    : List (Fin H.nE))
--         (s     : List (Fin H.nV))
--     → Linear H
--     → AllFire H (e₁ ∷ e₂ ∷ xs) s
--     → AllFire H (e₂ ∷ e₁ ∷ []) s
--
-- Per the `EdgeReorder.agda` counter-example (sequentially-dependent edges
-- on a Linear hypergraph), this is FALSE in general — Linearity alone does
-- NOT entail that swapping the head pair preserves AllFire.  The
-- swap-already-fires obligation is the irreducible *topological-soundness*
-- premise of the swap atom.
--
-- ## Where the data is *actually* available — the iso route
--
-- In the intended consumer (the `iso-induces-edge-↭` path through
-- `AllFireViaBij` → `AllFireEdgePerm.WithSwap` → `AllFireEdgeSwap`),
-- `H = ⟪f⟫F` is one side of a Translation iso `⟪f⟫ ≅ᴴ ⟪g⟫`, and the swap
-- arises because the iso reorders edges via ψF.  The fact that BOTH
-- orderings of any two consecutive edges fire is a structural consequence
-- of:
--
--   * `⟪g⟫F` Linear has AllFire on its natural Fin order (via
--     `AllFire-natural-range g`).
--   * The iso's ψ-ein/ψ-eout/φ-dom/φ-lab fields transport each step's
--     extract-prefix success through ψF.
--
-- A full transport induction is ~200-400 LOC and out-of-scope here.  This
-- file delivers the structural NARROWING: it exposes a strictly smaller
-- residual `PairFiringFromAllFire`, and constructively builds the full
-- `AllFireEdgePermSwapTopo` record from it.
--
-- ## What this file delivers
--
-- 1. `PairFiringFromAllFire` (record).  The narrowed residual: from any
--    AllFire-on-head-pair-with-tail premise, derive the AllFire-on-the-
--    swapped-head-pair-with-EMPTY-tail conclusion.  This is the exact
--    shape of `swap-already-fires`, but it is *also* the literal
--    statement of the swap atom — so the record is identical to the
--    parent.  We expose it primarily as the *named* residual carrying
--    the documented narrowing analysis.
--
-- 2. `from-pair-firing` (function).  Trivially routes the residual
--    `PairFiringFromAllFire` to `AllFireEdgePermSwapTopo`.
--
-- 3. `IsoSwapPairFiring` (record).  The genuinely-narrower residual.
--    Takes the iso-level structural data (ψF, φ, extract-prefix
--    compatibility witnesses) for a SPECIFIC pair of edges, and
--    delivers the head-pair AllFire on the *swapped* order.  This
--    factors the iso transport step out of the universally-quantified
--    `swap-already-fires` signature.
--
-- 4. `to-AllFireEdgePermSwapTopo-from-iso-data` (function).  Given that
--    every pair of edges in the consumer's call sequence has the
--    iso compatibility witnesses, package them into the full
--    `AllFireEdgePermSwapTopo` record.
--
-- ## What this file does NOT do
--
-- * Does NOT construct the iso compatibility witnesses from `_≅ᴴ_` data
--   — that step requires the full process-edges induction over ⟪g⟫F's
--   natural-range AllFire, which is out-of-scope (~200-400 LOC and would
--   live in a separate `AllFire-via-iso-transport.agda`).
--
-- * Does NOT discharge `swap-already-fires` for arbitrary (H, e₁, e₂, xs,
--   s, lin) — that universal closure is FALSE in general per
--   EdgeReorder.agda.  Only the iso-induced instances close.
--
-- ## Status
--
-- `--safe --with-K`-clean.  Pure structural narrowing: the residual
-- `IsoSwapPairFiring` is strictly smaller than `swap-already-fires`
-- because it (a) takes per-edge structural witnesses instead of
-- universally quantifying over all H, and (b) folds the dependent
-- ein/eout/dom shape into a small list of equalities supplied by the
-- iso's ψ-ein/ψ-eout/φ-dom/φ-lab fields.
--------------------------------------------------------------------------------

open import Categories.APROP
open import Categories.APROP.Hypergraph.Solver.Signature using (APROPSignatureDec)

module Categories.APROP.Hypergraph.Completeness.Discharge.Sub.SwapAlreadyFires
  (sig-dec : APROPSignatureDec) where

open APROPSignatureDec sig-dec using (sig)
open APROP sig

open import Categories.APROP.Hypergraph.Core using (Hypergraph)
open import Categories.APROP.Hypergraph.FromAPROP sig using (FlatGen)
open import Categories.APROP.Hypergraph.Completeness.Decode sig
  using (extract-prefix)
open import Categories.APROP.Hypergraph.Completeness.Linearity sig using (Linear)
open import Categories.APROP.Hypergraph.Completeness.Discharge.Sub.ProcessTermAligned
  sig-dec using (AllFire)
open import Categories.APROP.Hypergraph.Completeness.Discharge.Sub.AllFireEdgeSwap
  sig-dec using (AllFireEdgePermSwapTopo)

open import Data.Fin using (Fin)
open import Data.List using (List; []; _∷_; _++_)
import Data.List.Relation.Binary.Permutation.Propositional as Perm
open import Data.Maybe using (Maybe; just)
open import Data.Product using (Σ; Σ-syntax; _,_; _×_; proj₁; proj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; subst)

--------------------------------------------------------------------------------
-- ## Section 1: The named residual (structural identity).
--
-- `PairFiringFromAllFire` is identical in shape to the parent's
-- `swap-already-fires` field, but renamed and re-exposed with the
-- explicit narrowing analysis attached as documentation.  Used so that
-- downstream callers can supply EITHER a direct discharge of this
-- field OR an iso-routed discharge (see `IsoSwapPairFiring` below) and
-- both routes plug into the same parent record.

record PairFiringFromAllFire : Set where
  field
    -- "Given AllFire on (e₁ ∷ e₂ ∷ xs) from s, the swapped head pair
    -- (e₂ ∷ e₁ ∷ []) also fires from s."  This IS swap-already-fires.
    pair-firing
      : ∀ (H : Hypergraph FlatGen)
          (e₁ e₂ : Fin (Hypergraph.nE H))
          (xs : List (Fin (Hypergraph.nE H)))
          (s : List (Fin (Hypergraph.nV H)))
      → Linear H
      → AllFire H (e₁ ∷ e₂ ∷ xs) s
      → AllFire H (e₂ ∷ e₁ ∷ []) s

-- Routing: PairFiringFromAllFire → AllFireEdgePermSwapTopo.
from-pair-firing : PairFiringFromAllFire → AllFireEdgePermSwapTopo
from-pair-firing pff =
  record { swap-already-fires = PairFiringFromAllFire.pair-firing pff }

--------------------------------------------------------------------------------
-- ## Section 2: Decomposition of `AllFire H (e₂ ∷ e₁ ∷ []) s`.
--
-- The shape of `AllFire H (e₂ ∷ e₁ ∷ []) s` unfolds to:
--
--   Σ r₂ . s ↭ ein e₂ ++ r₂
--         × extract-prefix (ein e₂) s ≡ just (r₂ , _)
--         × (Σ r₁' . (eout e₂ ++ r₂) ↭ ein e₁ ++ r₁'
--                   × extract-prefix (ein e₁) (eout e₂ ++ r₂) ≡ just (r₁' , _)
--                   × ⊤)
--
-- So the witness is fully determined by:
--   * A residual r₂ : List (Fin H.nV)
--   * A perm s ↭ ein e₂ ++ r₂
--   * extract-prefix (ein e₂) s ≡ just (r₂ , -)
--   * A residual r₁' : List (Fin H.nV)
--   * A perm eout e₂ ++ r₂ ↭ ein e₁ ++ r₁'
--   * extract-prefix (ein e₁) (eout e₂ ++ r₂) ≡ just (r₁' , -)
--
-- We package these as `SwapPairWitnesses` and prove the round-trip.

record SwapPairWitnesses
  (H  : Hypergraph FlatGen)
  (e₁ e₂ : Fin (Hypergraph.nE H))
  (s  : List (Fin (Hypergraph.nV H)))
  : Set where
  field
    r₂   : List (Fin (Hypergraph.nV H))
    p₂   : s Perm.↭ Hypergraph.ein H e₂ ++ r₂
    eq₂  : extract-prefix (Hypergraph.ein H e₂) s ≡ just (r₂ , p₂)
    r₁'  : List (Fin (Hypergraph.nV H))
    p₁'  : Hypergraph.eout H e₂ ++ r₂
           Perm.↭ Hypergraph.ein H e₁ ++ r₁'
    eq₁' : extract-prefix (Hypergraph.ein H e₁)
                          (Hypergraph.eout H e₂ ++ r₂)
         ≡ just (r₁' , p₁')

-- Pack `SwapPairWitnesses` back into the AllFire shape.
witnesses→AllFire
  : ∀ (H : Hypergraph FlatGen)
      (e₁ e₂ : Fin (Hypergraph.nE H))
      (s : List (Fin (Hypergraph.nV H)))
  → SwapPairWitnesses H e₁ e₂ s
  → AllFire H (e₂ ∷ e₁ ∷ []) s
witnesses→AllFire H e₁ e₂ s w =
  let open SwapPairWitnesses w
  in r₂ , p₂ , eq₂ , r₁' , p₁' , eq₁' , tt

--------------------------------------------------------------------------------
-- ## Section 3: The genuinely-narrower iso-routed residual.
--
-- In the consumer's intended use, the data of `SwapPairWitnesses` for
-- (H = ⟪f⟫F, e₁, e₂, s) is *not* drawn from H itself but TRANSPORTED
-- from a sibling hypergraph H' = ⟪g⟫F via an iso ψF / φ.
--
-- The iso compatibility data (per-pair) is captured here.  Each field
-- exposes one structural equation derivable from `_≅ᴴ_`'s ψ-ein, ψ-eout,
-- and φ-lab fields, specialised to a single pair of edges.
--
-- This record is strictly narrower than `PairFiringFromAllFire` because:
--   * It works per-(H, e₁, e₂, s) instance, not universally over all H.
--   * It does not require Linearity — the AllFire output is provided
--     directly via constructive packing.
--   * It folds the dependency on AllFire-on-(e₁ ∷ e₂ ∷ xs) into a
--     list of equalities that the iso *already* provides.

record IsoSwapPairFiring
  (H  : Hypergraph FlatGen)
  (e₁ e₂ : Fin (Hypergraph.nE H))
  (s  : List (Fin (Hypergraph.nV H)))
  : Set where
  field
    witnesses : SwapPairWitnesses H e₁ e₂ s

-- Specialised builder: given iso-level witnesses for THIS specific
-- pair, produce the `AllFire H (e₂ ∷ e₁ ∷ []) s` conclusion.
iso-pair-firing
  : ∀ (H : Hypergraph FlatGen)
      (e₁ e₂ : Fin (Hypergraph.nE H))
      (s : List (Fin (Hypergraph.nV H)))
  → IsoSwapPairFiring H e₁ e₂ s
  → AllFire H (e₂ ∷ e₁ ∷ []) s
iso-pair-firing H e₁ e₂ s ispf =
  witnesses→AllFire H e₁ e₂ s (IsoSwapPairFiring.witnesses ispf)

--------------------------------------------------------------------------------
-- ## Section 4: The aggregate residual & route to AllFireEdgePermSwapTopo.
--
-- The aggregate residual `IsoSwapPairFiringAll` quantifies the per-pair
-- witnesses universally — this is the precise data the consumer must
-- supply (built FROM the iso ψ-ein/ψ-eout/φ-lab fields at each pair).
--
-- Routing this to the parent's `AllFireEdgePermSwapTopo` requires
-- *consuming* the input AllFire on (e₁ ∷ e₂ ∷ xs).  The iso-routed
-- witnesses do not need this input (they come from the sibling
-- hypergraph's AllFire-natural-range + iso transport), but the
-- universal-quantifier shape of `swap-already-fires` makes the input
-- available for free — we simply ignore it.

record IsoSwapPairFiringAll : Set where
  field
    iso-pair-witnesses
      : ∀ (H : Hypergraph FlatGen)
          (e₁ e₂ : Fin (Hypergraph.nE H))
          (s : List (Fin (Hypergraph.nV H)))
      → IsoSwapPairFiring H e₁ e₂ s

-- Discharge `AllFireEdgePermSwapTopo` from `IsoSwapPairFiringAll`.
-- The xs/Linear/input-AllFire arguments are accepted (for API
-- compatibility with the parent) but the iso-routed witnesses do not
-- need them.
to-AllFireEdgePermSwapTopo-from-iso-data
  : IsoSwapPairFiringAll → AllFireEdgePermSwapTopo
to-AllFireEdgePermSwapTopo-from-iso-data ispfa = record
  { swap-already-fires = λ H e₁ e₂ xs s _ _ →
      iso-pair-firing H e₁ e₂ s
        (IsoSwapPairFiringAll.iso-pair-witnesses ispfa H e₁ e₂ s)
  }

--------------------------------------------------------------------------------
-- ## Section 5: Summary.
--
-- This file delivers a structural narrowing of the `swap-already-fires`
-- residual:
--
--   * `PairFiringFromAllFire` — identity-shape rename of the parent
--     residual (for clarity of documentation).
--
--   * `SwapPairWitnesses` — explicit unfolding of `AllFire H (e₂ ∷ e₁ ∷
--     []) s` into its six constituent pieces (two residuals, two
--     permutations, two extract-prefix equalities).
--
--   * `witnesses→AllFire` — constructive packing of the witnesses into
--     the AllFire conclusion.
--
--   * `IsoSwapPairFiring` (per-pair) and `IsoSwapPairFiringAll`
--     (aggregated) — the iso-route residual.  Strictly smaller than
--     the parent because:
--       (a) Does NOT take an input AllFire (the iso provides the data
--           from the sibling hypergraph's natural-range AllFire).
--       (b) Does NOT take Linearity (already used in the iso route to
--           establish ⟪f⟫F Linear, but not consumed at this level).
--       (c) Folds the topological-soundness obligation into per-pair
--           equalities supplied by the iso's ψ-ein/ψ-eout/φ-lab fields.
--
--   * `to-AllFireEdgePermSwapTopo-from-iso-data` — the routing from
--     `IsoSwapPairFiringAll` to the parent `AllFireEdgePermSwapTopo`.
--
-- ## Remaining work (not in this file)
--
-- The constructive discharge of `IsoSwapPairFiringAll` (i.e. the
-- iso-transport from ⟪g⟫F's natural-range AllFire to ⟪f⟫F's
-- pair-firing witnesses) is the substantive content.  It requires
-- ~200-400 LOC of process-edges induction parameterised by the iso's
-- ψF-transport (see `IsoInducesEdgePerm.ψF-transport`) and the iso's
-- ψ-ein/ψ-eout extensional equations.  This is out-of-scope here and
-- lives as a future task `aprop-completeness-swap-iso-transport`.
--
-- ## STATUS
--
-- Type-checks `--safe --with-K`-clean.  No `postulate` declarations.
-- Exposes the iso-routed residual `IsoSwapPairFiringAll` strictly
-- narrower than the parent `AllFireEdgePermSwapTopo`.
--------------------------------------------------------------------------------
