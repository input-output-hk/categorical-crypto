{-# OPTIONS --safe --with-K #-}

--------------------------------------------------------------------------------
-- (Historically the trust module for `Solver/Tests.agda`.)
--
-- The completeness chain is now FULLY AXIOM-FREE — its Kelly residual is the
-- proven `FaithfulnessInductive.faithfulness` — so `Tests.WithAssumptions`
-- needs no assumption and this module no longer postulates anything.  It is
-- now `--safe` and simply re-exports the (closed) per-test smoke-checks.
--------------------------------------------------------------------------------

module Categories.APROP.Hypergraph.Solver.TestsTrust where

open import Categories.APROP.Hypergraph.Solver.Tests using (module WithAssumptions)

open WithAssumptions public
