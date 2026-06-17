{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- The single deferred residual of the strict pipeline, `permˢ-K`, and the
-- `perm-rigidˢ` wrapper that all of parts (I)ˢ/(II)ˢ consume.
--
-- `permˢ-K` is the strict, VERTEX-LEVEL analogue of the proven
-- `FaithfulnessInductive.faithfulness` (the deep "K" ingredient):
-- two permutation derivations whose evaluated bijections coincide produce
-- `_≈ˢ_`-equal terms under `permuteˢ`.  It is threaded here as a module
-- PARAMETER and discharged axiom-free in `Strict.Perm.PermK` via
-- `PermDischarge` + `Braid.Generic.strict-braid` (NOT via `Strict.Embed`,
-- which is not imported on that route).
--
-- `perm-rigidˢ` specialises it to the form every decoder use actually
-- needs: two derivations into a `Unique` stack are identified (the
-- evaluated-bijection equality is then automatic via `eval-rigid`).
--------------------------------------------------------------------------------

open import Categories.APROP
open import Relation.Binary using (DecidableEquality)

module Categories.APROP.Hypergraph.Soundness.Strict.Perm.PermSupport
  (sig : APROPSignature)
  (_≟X_ : DecidableEquality (APROPSignature.X sig))
  where

open APROP sig using (X)

open import Categories.APROP.Hypergraph.Soundness.Strict.Core sig _≟X_

open import Data.List using (List)
open import Data.List.Relation.Unary.Unique.Propositional using (Unique)
import Data.List.Relation.Binary.Permutation.Propositional as Perm
open Perm using (_↭_)

open import Categories.PermuteCoherence.Eval using (eval-↭)
open import Categories.PermuteCoherence.FinBij using (_≈-fb_)
open import Categories.PermuteCoherence.Rigid using (eval-rigid)

--------------------------------------------------------------------------------
-- The residual, parameterised over a vertex set `V` and its labelling.

module Support (V : Set) (vlab : V → X) where

  open Perm′ V vlab public

  -- The strict Kelly residual: `permuteˢ` respects evaluated-bijection
  -- equality.  (`p ≅↭ q  :=  eval-↭ p ≈-fb eval-↭ q`, the same relation the
  -- non-strict `FaithfulnessResidual` uses, taken here at `V`.)
  PermK : Set
  PermK = ∀ {xs ys : List V} (p q : xs ↭ ys)
        → eval-↭ p ≈-fb eval-↭ q
        → permuteˢ p ≈ˢ permuteˢ q

  module _ (permˢ-K : PermK) where

    -- The form every decoder use needs: two derivations into a `Unique`
    -- stack are `permuteˢ`-equal.
    perm-rigidˢ
      : ∀ {xs ys : List V} → Unique ys → (p q : xs ↭ ys)
      → permuteˢ p ≈ˢ permuteˢ q
    perm-rigidˢ uniq p q = permˢ-K p q (eval-rigid uniq p q)
