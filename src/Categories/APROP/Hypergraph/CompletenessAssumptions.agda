{-# OPTIONS --safe #-}

--------------------------------------------------------------------------------
-- Generic assumptions sufficient to construct
-- `Categories.APROP.Hypergraph.Completeness.DecodeRespIso.CompletenessAssumptions`.
--
-- This module is not allowed to import any files from the
-- `Categories.APROP` subtree. All fields must be stated in terms of
-- generic concepts (free monoidal categories, FinBij, etc.)  and must
-- be mathematically true.
--------------------------------------------------------------------------------

module Categories.APROP.Hypergraph.CompletenessAssumptions where

open import Categories.FreeMonoidal using (FreeMonoidalData; Variant; Symm; _≤_)
open import Categories.PermuteCoherence.Faithfulness using (FaithfulnessResidual)

record Assumptions : Set₁ where
  field
    -- Kelly's symmetric monoidal coherence on the permutation fragment.
    -- For every free symmetric monoidal category, two parallel
    -- `permute`-derivations whose underlying FinBij bijections agree
    -- yield `≈Term`-equal terms.  Standard categorical theorem
    -- (Mac Lane 1963, Kelly 1964).
    smc-faithfulness
      : (d : FreeMonoidalData) ⦃ s≤v : Symm ≤ FreeMonoidalData.v d ⦄
      → FaithfulnessResidual d
