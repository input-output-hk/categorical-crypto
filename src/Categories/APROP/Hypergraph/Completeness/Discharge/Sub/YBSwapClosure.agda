{-# OPTIONS --safe --with-K #-}

--------------------------------------------------------------------------------
-- Sub-residual bundling for the Y = swap / Y = trans (swap _ _ _) _
-- sub-cases across the four case-on-Y modules.
--
-- ## Context
--
-- After `BPrepSwapByCaseY`, `ASwapSwapByCaseY`, `BPrepTransSwapByCaseY`,
-- and `ATransByCaseY` perform case-analysis on the Y-shape of the
-- 7-field `RealFinalResidual`, 17 sub-residuals remain (the ones in
-- which Y is or contains a `Perm.swap`, adding a 3rd σ-block to the
-- cascade):
--
-- From BPrepSwapByCaseY (1):
--   1. `bpsy-Y-trans-swap`
--
-- From ASwapSwapByCaseY (2):
--   2. `aswap-swap-Y-trans-prep`
--   3. `aswap-swap-Y-trans-swap`
--
-- From BPrepTransSwapByCaseY (2):
--   4. `bptsy-Y-swap`
--   5. `bptsy-Y-trans-swap`
--
-- From ATransByCaseY (12 = 4 cascades × 3 Y-shapes):
--    rfr-A-trans-prep-prep:
--      6. `aprepprep-Y-swap`
--      7. `aprepprep-Y-trans-prep`
--      8. `aprepprep-Y-trans-swap`
--    rfr-A-trans-prep-swap:
--      9. `aprepswap-Y-swap`
--     10. `aprepswap-Y-trans-prep`
--     11. `aprepswap-Y-trans-swap`
--    rfr-A-trans-prep-trans:
--     12. `apreptrans-Y-swap`
--     13. `apreptrans-Y-trans-prep`
--     14. `apreptrans-Y-trans-swap`
--    rfr-A-trans-swap:
--     15. `atransswap-Y-swap`
--     16. `atransswap-Y-trans-prep`
--     17. `atransswap-Y-trans-swap`
--
-- ## Narrowing this file delivers
--
-- A single bundled residual record `YBSwapClosureResidual` that
-- contains all 17 obligations (via the four narrowed-by-case-on-Y
-- residual records).  This is strictly narrower than the 4 separate
-- residual records since downstream consumers only need to satisfy
-- one record instead of four.
--
-- The closure functions for the seven `RealFinalResidual` fields
-- (`rfr-A-swap-swap-closed`, `rfr-A-trans-prep-prep-closed`,
-- `rfr-A-trans-prep-swap-closed`, `rfr-A-trans-prep-trans-closed`,
-- `rfr-A-trans-swap-closed`, `rfr-B-prep-swap-closed`,
-- `rfr-B-prep-trans-swap-closed`) are re-exposed here, parameterized
-- by `YBSwapClosureResidual`.
--
-- ## σ-block-hexagon application chain (documentation)
--
-- The 17 residuals in `YBSwapClosureResidual` each have an underlying
-- 3-σ-block cascade structure:
--
--   * Outer cascade contributes 2 σ-blocks (one per outer
--     `Perm.swap`).
--   * Y = swap _ _ _ or Y = trans (swap _ _ _) _ adds a 3rd σ-block.
--
-- The full term-level analysis of any one residual proceeds:
--
--   Step 1. Unfold `permute(p)` to expose the 3 σ-blocks at the term
--           level (each `Perm.swap k₁ k₂ q` contributes
--           `(id ⊗ (id ⊗ permute q)) ∘ σ-block_{k₁,k₂,...}`).
--   Step 2. Apply `σ-block-natural₃` (and naturality of `⊗`) to push
--           the inner `permute a`, `permute b'`, `permute Y₁'`
--           factors past the σ-blocks.  After this stage, the cascade
--           is:
--               pY ∘ T ∘ (σ-block₃ ∘ σ-block₂ ∘ σ-block₁)
--           where T is a tensor of inner permutations and σ-block_i
--           are the three σ-blocks.
--   Step 3. Apply `σ-block-hexagon` (or its core `-core` variant)
--           to rewrite (σ-block₃ ∘ σ-block₂ ∘ σ-block₁) into the
--           other bracketing.
--   Step 4. After hexagon rewrite, the 3 σ-blocks are in a different
--           order.  Combine with the inner permutations to form a
--           new permutation `q` with strictly smaller measure (via
--           swap-count decrease, since one of the swaps merges with
--           an inner factor).
--   Step 5. Apply `self-rec` on `q`.
--
-- Step 2 (and the subsequent algebraic chain) involve ~300-500 LOC
-- per residual of careful σ-block-natural / σ-block-involutive /
-- ⊗-∘-dist rewrites.  This file defers them to the residual record.
--
-- ## Why we cannot constructively close these here
--
-- σ-block-hexagon (Yang-Baxter at the σ-block level) only
-- rearranges 3 σ-blocks into a different bracketing — it does NOT
-- reduce the σ-block count.  Constructive closure to a
-- smaller-measure `q` requires combining the hexagon-rewritten
-- form with the surrounding `pY`, `pa`, etc. factors via σ-block
-- naturalities, and then exhibiting a `q` whose swap-count is
-- strictly less than `p`'s.  This combination work is non-trivial
-- and not delivered here.
--
-- The closely-related (and simpler) `BPSARefl-YB-Residual` in
-- `Sub/BPSARefl.agda` documents the same situation for a 2-σ-block
-- case: Stage 1 (algebraic simplification) is delivered constructively,
-- but Stage 3 (the YB rewrite) is left as a residual.  The 3-σ-block
-- case here is structurally more complex and deferred similarly.
--
-- ## File is `--safe --with-K`-clean.  All 17 obligations are bundled
--    in the single `YBSwapClosureResidual` record (no other postulates).
--------------------------------------------------------------------------------

open import Categories.APROP
open import Categories.APROP.Hypergraph.Solver.Signature using (APROPSignatureDec)

module Categories.APROP.Hypergraph.Completeness.Discharge.Sub.YBSwapClosure
  (sig-dec : APROPSignatureDec) where

open APROPSignatureDec sig-dec using (sig)
open APROP sig

open import Categories.APROP.Hypergraph.Completeness.Discharge.Sub.BPrepSwapByCaseY sig-dec
  using ( BPrepSwapByYResidual
        ; module WithBPrepSwapByYResidual)
open import Categories.APROP.Hypergraph.Completeness.Discharge.Sub.ASwapSwapByCaseY sig-dec
  using ( ASwapSwapByYResidual
        ; module WithASwapSwapByYResidual)
open import Categories.APROP.Hypergraph.Completeness.Discharge.Sub.BPrepTransSwapByCaseY sig-dec
  using ( BPrepTransSwapByYResidual
        ; module WithBPrepTransSwapByYResidual)
open import Categories.APROP.Hypergraph.Completeness.Discharge.Sub.ATransByCaseY sig-dec
  using ( ATransByYResidual
        ; module WithATransByYResidual)

--------------------------------------------------------------------------------
-- ## `YBSwapClosureResidual`: bundled residual record.
--
-- A single residual record containing the four narrowed-by-case-on-Y
-- residual records.  Equivalent to satisfying all 17 individual
-- obligations.

record YBSwapClosureResidual : Set where
  field
    -- 1 field from BPrepSwapByCaseY: bpsy-Y-trans-swap.
    bprep-swap-by-Y-residual : BPrepSwapByYResidual

    -- 2 fields from ASwapSwapByCaseY: aswap-swap-Y-trans-prep, aswap-swap-Y-trans-swap.
    aswap-swap-by-Y-residual : ASwapSwapByYResidual

    -- 2 fields from BPrepTransSwapByCaseY: bptsy-Y-swap, bptsy-Y-trans-swap.
    bprep-trans-swap-by-Y-residual : BPrepTransSwapByYResidual

    -- 12 fields from ATransByCaseY (4 cascades × 3 Y-shapes).
    atrans-by-Y-residual : ATransByYResidual

--------------------------------------------------------------------------------
-- ## Closures re-exposed.
--
-- The seven `RealFinalResidual` closure functions (one per cascade
-- shape), each delegating to the appropriate case-on-Y module and the
-- bundled narrowed residual record.

module WithYBSwapClosureResidual (res : YBSwapClosureResidual) where
  open YBSwapClosureResidual res

  -- Case-on-Y closure for `rfr-B-prep-swap`.
  open WithBPrepSwapByYResidual bprep-swap-by-Y-residual public
    using (rfr-B-prep-swap-closed)

  -- Case-on-Y closure for `rfr-A-swap-swap`.
  open WithASwapSwapByYResidual aswap-swap-by-Y-residual public
    using (rfr-A-swap-swap-closed)

  -- Case-on-Y closure for `rfr-B-prep-trans-swap`.
  open WithBPrepTransSwapByYResidual bprep-trans-swap-by-Y-residual public
    using (rfr-B-prep-trans-swap-closed)

  -- Case-on-Y closures for the 4 A-trans-* cascades.
  open WithATransByYResidual atrans-by-Y-residual public
    using ( rfr-A-trans-prep-prep-closed
          ; rfr-A-trans-prep-swap-closed
          ; rfr-A-trans-prep-trans-closed
          ; rfr-A-trans-swap-closed)

--------------------------------------------------------------------------------
-- ## Outcome
--
-- This file delivers:
--
--   * `YBSwapClosureResidual` — bundled residual record with the
--     four case-on-Y narrowed residual records as fields.
--     Equivalent to satisfying all 17 sub-residuals.
--
--   * `module WithYBSwapClosureResidual` — re-exposes the 7
--     `RealFinalResidual` closure functions (one per cascade shape),
--     each parameterized by the bundled residual.
--
-- ## Discharge status (per sub-residual)
--
-- All 17 sub-residuals are DOCUMENTED but NOT constructively closed
-- via `σ-block-hexagon`.  The application chain is:
--
--   Step 1. permute(p) unfolding (3 σ-blocks visible).
--   Step 2. σ-block-natural₃ + ⊗-∘-dist to push inner factors past
--           σ-blocks.
--   Step 3. σ-block-hexagon to rearrange 3-σ-block bracketing.
--   Step 4. σ-block-involutive (only if 2 σ-blocks cancel; not the
--           case here).
--   Step 5. Show new form ≈ permute(q) for smaller-measure q;
--           apply self-rec.
--
-- The combination work in Steps 2 and 4-5 is non-trivial.  It is
-- bundled into `YBSwapClosureResidual` for follow-up work.
--
-- ## File is `--safe --with-K`-clean.  No new postulates outside
--    `YBSwapClosureResidual` (which is the bundled narrowed residual).
--------------------------------------------------------------------------------
