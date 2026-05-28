{-# OPTIONS --with-K #-}

--------------------------------------------------------------------------------
-- Trust module for `Solver/Tests.agda`.
--
-- `Tests.agda` is `--safe` and parameterized over a
-- `CompletenessAssumptions mySigDec` record instance.  The record
-- (defined in `Completeness/DecodeRespIso.agda`, re-exported via
-- `Completeness/DecodeRel/Inductive.agda`) has THREE narrow fields:
--   * `process-term-permute-aligned` (c')  — term-level ≈Term taking
--                                            the stack permutation as
--                                            an explicit parameter.
--   * `X-permute-self-loop-id`       (XSL) — Kelly's UNARY self-loop
--                                            coherence: `permute r ≈Term
--                                            id` for `r : xs ↭ xs`.
--                                            Binary form recovered in
--                                            `WithAssumptions`.
--   * `decode-rel-≈-decode`          (F)   — decoder agreement.
-- Each is strictly narrower than the original `decode-rel-resp-iso`.
--
-- FOUR sub-properties have been FULLY DISCHARGED CONSTRUCTIVELY and
-- are no longer fields of the record:
--   * `decode-attempt-Linear-extracts` — `Discharge/LinearExtracts.agda`.
--   * `process-edges-resp-iso-stack` (b) — `Discharge/StackPerm.agda`
--     (the iso is structurally redundant for the multiset statement).
--   * The OLD (c) and (d) field bodies — reconstructed in
--     `WithAssumptions` from the new (c') + (XSL) fields via
--     `Discharge/ProcessTermNew.agda` and
--     `Discharge/FinalPermuteNew.agda`.
--   * The OLD (K) binary `permute-≈Term-coherence` — reconstructed
--     in `WithAssumptions` from (XSL) via Path C in
--     `Discharge/PermuteCoherenceShared.agda` (`FromXSelfLoop`).
--
-- This module postulates the record and re-exports the resulting
-- per-test smoke-checks.  It is *not* `--safe`; the trust is
-- concentrated here, isolated from the rest of the codebase.
--------------------------------------------------------------------------------

module Categories.APROP.Hypergraph.Solver.TestsTrust where

import Categories.APROP.Hypergraph.Completeness.DecodeRel.Inductive as IND
open import Categories.APROP.Hypergraph.Solver.Tests
  using (mySigDec; module WithAssumptions)

postulate
  trusted-assumptions : IND.CompletenessAssumptions mySigDec

open WithAssumptions trusted-assumptions public
