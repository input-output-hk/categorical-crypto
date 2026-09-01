{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- The STRICT `EdgeStepRˢ` algebra bricks for the two-edge interchange.
--
--   * `fire-termˢ`/`EdgeStepRˢ`/`edge-stepˢ-graph` — the strict fired layer
--     and the inductive graph of `edge-stepˢ`, re-exported from the shared
--     `EdgeStepRel` leaf under this module's `(H)` telescope.
--   * `Incomp`, `pe-stackˢ`/`pe-termˢ` — incomparability + `process-edgesˢ`
--     projection abbreviations.
--------------------------------------------------------------------------------

open import Categories.APROP
open import Relation.Binary using (DecidableEquality)

module Categories.APROP.Hypergraph.Soundness.Strict.Interchange.SwapCore
  (sig : APROPSignature)
  (_≟X_ : DecidableEquality (APROPSignature.X sig))
  where

open import Categories.APROP.Hypergraph.Model.Core using (Hypergraph)
open import Categories.APROP.Hypergraph.Model.FromAPROP sig using (FlatGen)

open import Categories.APROP.Hypergraph.Soundness.Discharge.EdgeDependency using (Dep)

open import Categories.APROP.Hypergraph.Soundness.Strict.Decode.Decoder sig _≟X_
open import Categories.APROP.Hypergraph.Soundness.Strict.Interchange.EdgeStepRel sig _≟X_
  using (module EdgeStepView)

import Categories.Combinatorics.LinearExtension as LinExt

open import Data.Fin using (Fin)

--------------------------------------------------------------------------------

module _ (H : Hypergraph FlatGen) where
  private module H = Hypergraph H

  open StrictDecoder H

  --------------------------------------------------------------------
  -- The strict fired layer (`fire-termˢ`) + the `EdgeStepRˢ` graph of
  -- `edge-stepˢ`, re-exported from the shared `EdgeStepRel` leaf.
  --------------------------------------------------------------------

  open EdgeStepView H public

  --------------------------------------------------------------------
  -- Incomparability of two edges — the order-theory kernel's `Incomp` at
  -- this hypergraph's dependency relation, NOT a strict re-spelling: the
  -- non-strict wiring (`IsoInvarianceWiring.PerHG`) re-exports the SAME
  -- `LinExt.Incomp`, which is why `SwapStep.swap-validityˢ` can hand a
  -- `swap-step`'s incomparability straight to `SwapValidity.swap-validity`.
  --------------------------------------------------------------------

  open LinExt (Fin H.nE) (Dep H) public using (Incomp)


