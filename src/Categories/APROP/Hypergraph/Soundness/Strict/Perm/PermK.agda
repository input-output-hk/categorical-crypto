{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- The strict Kelly residual `permˢ-K` — its TYPE, the `perm-rigidˢ` wrapper
-- that all of parts (I)ˢ/(II)ˢ consume, and the residual itself FULLY
-- DISCHARGED (axiom-free) at the pipeline's `FlatGen` instance.
--
-- `Support.PermK` is the strict, VERTEX-LEVEL analogue of the proven
-- `Coxeter.FaithfulnessInductive.complete` (the deep "K" ingredient):
-- two permutation derivations whose evaluated bijections coincide produce
-- `_≈ˢ_`-equal terms under `permuteˢ`.  It is a module PARAMETER inside
-- `Support` and only there; `Support.perm-rigidˢ` specialises it to the form
-- every decoder use actually needs — two derivations into a `Unique` stack are
-- identified (the evaluated-bijection equality is then automatic via
-- `eval-rigid`).
--
-- The discharge closes that parameter with no postulate left: `PermDischarge`
-- reduces `permˢ-K` to the single closed coherence `StrictBraid`, and
-- `Braid.Generic` proves `StrictBraid` for every generator family.  Wiring
-- them together (at `mor := FlatGen`) gives the constructed residual the
-- decoder shape lemmas and the part-(II)ˢ chain consume.
--------------------------------------------------------------------------------

open import Categories.APROP
open import Relation.Binary using (DecidableEquality)

module Categories.APROP.Hypergraph.Soundness.Strict.Perm.PermK
  (sig : APROPSignature)
  (_≟X_ : DecidableEquality (APROPSignature.X sig))
  where

open APROP sig using (X)

open import Categories.APROP.Hypergraph.Model.FromAPROP sig using (FlatGen)
open import Categories.APROP.Hypergraph.Soundness.Strict.Core sig _≟X_

import Categories.APROP.Hypergraph.Soundness.Strict.Perm.PermDischarge X _≟X_ as PD
import Categories.APROP.Hypergraph.Soundness.Strict.Perm.Braid X _≟X_ as BR

open import Data.List using (List)
open import Data.List.Relation.Unary.Unique.Propositional using (Unique)
open Perm using (_↭_)

open import Categories.PermuteCoherence.Eval using (eval-↭)
open import Categories.PermuteCoherence.FinBij using (_≈-fb_)
open import Categories.PermuteCoherence.Rigid using (eval-rigid)

--------------------------------------------------------------------------------
-- The residual's TYPE, parameterised over a vertex set `V` and its labelling.

module Support (V : Set) (vlab : V → X) where

  open Perm′ V vlab public

  -- The strict Kelly residual: `permuteˢ` respects evaluated-bijection
  -- equality.  (`p ≅↭ q  :=  eval-↭ p ≈-fb eval-↭ q`, the same relation the
  -- former non-strict `FaithfulnessResidual` uses, taken here at `V`.)
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

--------------------------------------------------------------------------------
-- For any vertex set `V` with a labelling, the constructed residual.

module _ (V : Set) (_≟V_ : DecidableEquality V) (vlab : V → X) where

  private
    module D = PD.Discharge V _≟V_ vlab FlatGen
    -- `StrictBraid` at `FlatGen` is proven by `Braid.Generic FlatGen`.
    module M = D.Main (BR.Generic.strict-braid FlatGen)

  permˢ-K : Support.PermK V vlab
  permˢ-K = M.permˢ-K

  -- The form every consumer needs: two derivations into a `Unique` stack are
  -- `permuteˢ`-equal (`eval-rigid` supplies the evaluated-bijection equality).
  perm-rigidˢ = Support.perm-rigidˢ V vlab permˢ-K
