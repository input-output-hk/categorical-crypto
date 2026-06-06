{-# OPTIONS --with-K #-}

--------------------------------------------------------------------------------
-- Trust module for `Solver/Tests.agda`.
--
-- `Tests.WithAssumptions` is parameterized over the SINGLE Kelly assumption
-- `K-faithfulness : FaithfulnessResidual` (Kelly 1964 symmetric-monoidal
-- permutation coherence), routing every test through `CompletenessFullWired`.
-- That residual is the whole trust surface of the completeness chain.
--
-- This module postulates exactly that one residual and re-exports the
-- resulting per-test smoke-checks.  All trust is concentrated here.  (A proof
-- of the residual exists on a separate branch; dropping it in here turns the
-- tests into closed theorems.)
--------------------------------------------------------------------------------

module Categories.APROP.Hypergraph.Solver.TestsTrust where

open import Categories.APROP using (APROPSignature)
open import Categories.FreeMonoidal using (v≤v)
open import Categories.APROP.Hypergraph.Solver.Tests
  using (mySig; module WithAssumptions)
import Categories.PermuteCoherence.Faithfulness as Faith

postulate
  trusted-K
    : Faith.FaithfulnessResidual (APROPSignature.asFreeMonoidalData mySig) ⦃ v≤v ⦄

open WithAssumptions trusted-K public
