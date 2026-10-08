{-# OPTIONS --safe --without-K #-}

-- Kelly faithfulness for strict permutation terms.

open import Categories.APROP.Internal.Prelude
open import Categories.PermuteCoherence.Eval using (eval-↭)
open import Categories.PermuteCoherence.FinBij using (_≈-fb_)
open import Categories.PermuteCoherence.Rigid using (eval-rigid)
open import Data.List.Relation.Unary.Unique.Propositional using (Unique)
open import Relation.Binary using (DecidableEquality)

module Categories.APROP.Hypergraph.Soundness.Strict.Perm.PermK
  (sig : APROPSignature)
  where

open APROP sig using (X; _≟X_)

open import Categories.APROP.Hypergraph.Model.FromAPROP sig using (FlatGen)
open import Categories.APROP.Hypergraph.Soundness.Strict.Core sig

import Categories.FreeStrictSMC.Perm.Braid X _≟X_ as BR
import Categories.FreeStrictSMC.Perm.Coherence X _≟X_ as PD

open Perm using (_↭_)

module Support (V : Set) (vlab : V → X) where

  open Perm′ V vlab public

  PermK : Set
  PermK = ∀ {xs ys : List V} (p q : xs ↭ ys)
        → eval-↭ p ≈-fb eval-↭ q
        → permuteˢ p ≈ˢ permuteˢ q

  module _ (permˢ-K : PermK) where

    -- `Unique` codomains make evaluated bijections coincide (`eval-rigid`).
    perm-rigidˢ
      : ∀ {xs ys : List V} → Unique ys → (p q : xs ↭ ys)
      → permuteˢ p ≈ˢ permuteˢ q
    perm-rigidˢ uniq p q = permˢ-K p q (eval-rigid uniq p q)

module _ (V : Set) (_≟V_ : DecidableEquality V) (vlab : V → X) where

  private
    module D = PD.Discharge V _≟V_ vlab FlatGen
    module M = D.Main (BR.Generic.strict-braid FlatGen)

  permˢ-K : Support.PermK V vlab
  permˢ-K = M.permˢ-K

  perm-rigidˢ = Support.perm-rigidˢ V vlab permˢ-K
