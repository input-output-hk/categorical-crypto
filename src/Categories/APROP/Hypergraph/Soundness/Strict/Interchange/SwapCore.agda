{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- The STRICT `EdgeStepRˢ` algebra bricks for the two-edge interchange.
--
--   * `fire-termˢ`/`EdgeStepRˢ`/`edge-stepˢ-graph` — the strict fired layer
--     and the inductive graph of `edge-stepˢ`, re-exported from the shared
--     `EdgeStepRel` leaf under this module's `(H)` telescope.
--   * `Incomp`, `pe-stackˢ`/`pe-termˢ` — incomparability + `process-edgesˢ`
--     projection abbreviations.
--   * `perm-rigidˢ` — the rigidity discharge for the located two-box
--     interchange kernel (the strict Kelly residual enters here).
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
import Categories.APROP.Hypergraph.Soundness.Strict.Perm.PermK sig _≟X_ as PK

open import Data.Fin using (Fin)
open import Data.Fin.Properties using () renaming (_≟_ to _≟F_)
open import Data.List using (List)
open import Data.List.Relation.Unary.Unique.Propositional using (Unique)
import Data.List.Relation.Binary.Permutation.Propositional as Perm
open import Data.Product using (_×_)
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

  --------------------------------------------------------------------
  -- RIGIDITY: any two derivations into a `Unique` stack are `permuteˢ`-equal.
  -- The strict Kelly residual enters here, and only here, at the concrete
  -- `Perm.PermK` (axiom-free for every vertex set).
  --------------------------------------------------------------------

  perm-rigidˢ
    : ∀ {xs ys : List (Fin H.nV)} → Unique ys
      → (p q : xs Perm.↭ ys) → permuteˢ p ≈ˢ permuteˢ q
  perm-rigidˢ = PK.perm-rigidˢ (Fin H.nV) _≟F_ H.vlab

