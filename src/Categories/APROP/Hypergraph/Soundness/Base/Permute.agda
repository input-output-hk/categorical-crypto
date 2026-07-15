{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- `permute`: realise a list permutation `xs ↭ ys` as a
-- `HomTerm (unflatten xs) (unflatten ys)`, using only the symmetric
-- monoidal structure (each `↭` step is a local rearrangement of the
-- right-associated tensor product).  Consumed by `decode` to reshuffle the
-- stack of live vertices; the `Linear` bound guarantees the relevant lists
-- really are permutations.
--------------------------------------------------------------------------------

open import Categories.APROP

module Categories.APROP.Hypergraph.Soundness.Base.Permute (sig : APROPSignature) where

open APROP sig

open import Data.Fin using (Fin)
open import Data.List using (List)
import Data.List.Relation.Binary.Permutation.Propositional as Perm
import Data.List.Relation.Binary.Permutation.Propositional.Properties as PermProp

--------------------------------------------------------------------------------
-- `permute` / `permute-via-vlab` are re-exported from
-- `Categories.Hypergraph.Steps` so APROP and generic SMC code observe
-- definitional equality on both.

open import Categories.Hypergraph.Steps asFreeMonoidalData public
  using (permute; permute-via-vlab)
