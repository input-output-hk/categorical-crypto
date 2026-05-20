{-# OPTIONS --with-K #-}

--------------------------------------------------------------------------------
-- Trust module for `Solver/Tests.agda`.
--
-- `Tests.agda` is `--safe` and parameterized over a
-- `CompletenessAssumptions mySigDec` record instance.  Producing such an
-- instance requires the two narrow completeness postulates
-- (`single-agen-NF-coherence`, `nf-resp-≅ᴴ-residual`) — see the record
-- definition in `Completeness/DecodeRel/Inductive.agda`.
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
