{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- Generic labelling infrastructure over a FreeMonoidalData with Symm ≤ v.
--
-- Provides `permute-via-vlab` (a vertex-list permutation realised as a
-- HomTerm on the unflattened tensor products, parameterised only over a
-- labelling function `vlab : Fin n → X`, no APROP signature).  It is built
-- from the same `permute`/`unflatten` as `PermuteCoherence.Unflatten`, so
-- generic SMC code stays definitionally aligned with APROP's `Decode`.
--------------------------------------------------------------------------------

open import Categories.FreeMonoidal

module Categories.PermuteCoherence.Steps
  (d : FreeMonoidalData) ⦃ s≤v : Symm ≤ FreeMonoidalData.v d ⦄ where

open FreeMonoidalData d using (X)
open FreeMonoidal d

open import Categories.PermuteCoherence.Unflatten d
  using (unflatten; permute)

open import Data.Fin using (Fin)
open import Data.List using (List; map)
import Data.List.Relation.Binary.Permutation.Propositional as Perm
import Data.List.Relation.Binary.Permutation.Propositional.Properties as PermProp

--------------------------------------------------------------------------------
-- Generic `permute-via-vlab` — same definition as APROP's, but parameterised
-- only over a labelling function (no APROP signature).

permute-via-vlab
  : ∀ {n} {xs ys : List (Fin n)} (vlab : Fin n → X)
  → xs Perm.↭ ys
  → HomTerm (unflatten (map vlab xs)) (unflatten (map vlab ys))
permute-via-vlab vlab p = permute (PermProp.map⁺ vlab p)
