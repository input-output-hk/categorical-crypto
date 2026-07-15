{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- Generic labelling infrastructure over a FreeMonoidalData with Symm ≤ v.
--
-- Provides `permute-via-vlab` (a vertex-list permutation realised as a
-- HomTerm on the unflattened tensor products, parameterised only over a
-- labelling function `vlab : Fin n → X`, no APROP signature), and re-exports
-- the generic `unflatten` / `unflatten-++-≅` / `permute` (from
-- PermuteCoherence) and the list-locating `extract-elem` / `extract-prefix`
-- (from Hypergraph.ExtractPrefix).  Sharing these definitions with APROP's
-- `Decode`/`Permute` keeps generic SMC code definitionally aligned with APROP.
--------------------------------------------------------------------------------

open import Categories.FreeMonoidal

module Categories.Hypergraph.Steps
  (d : FreeMonoidalData) ⦃ s≤v : Symm ≤ FreeMonoidalData.v d ⦄ where

open FreeMonoidalData d using (X)
open FreeMonoidal d

-- Generic `unflatten`, `unflatten-++-≅`, and `permute` (already defined
-- parametrically there).
open import Categories.PermuteCoherence.Faithfulness d
  using (unflatten; unflatten-++-≅; permute) public

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

--------------------------------------------------------------------------------
-- Re-export the generic `extract-elem` / `extract-prefix` list-locating
-- primitives, shared with APROP's `Decode`.

open import Categories.Hypergraph.ExtractPrefix public
  using (extract-elem; extract-prefix)
