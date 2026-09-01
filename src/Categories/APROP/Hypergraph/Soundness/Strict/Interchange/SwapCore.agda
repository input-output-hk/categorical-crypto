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

open import Data.Fin using (Fin)
open import Relation.Nullary using (¬_)

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
  -- Incomparability of two edges.
  --------------------------------------------------------------------

  Incomp : Fin H.nE → Fin H.nE → Set
  Incomp e e' = (¬ Dep H e e') × (¬ Dep H e' e)


