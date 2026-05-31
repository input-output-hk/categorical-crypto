{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- Phase 3.5f Step 2 — `permute`: realising a list permutation as a HomTerm.
--
-- Given two lists `xs ys : List X` related by the propositional permutation
-- relation `_↭_`, we construct a `HomTerm (unflatten xs) (unflatten ys)`
-- using only the symmetric monoidal structure (associators, braiding, and
-- identity).  No duplication or discarding is needed — `unflatten` is
-- right-associated, and each `_↭_` step corresponds to a local rearrangement
-- of the corresponding right-associated tensor product.
--
-- Consumed by `decode` (Phase 3.5f Step 3): the cospan-form algorithm
-- repeatedly reshuffles a stack of currently-live vertices, and each
-- reshuffle is built by `permute`.  The bound `Linear H` ensures that the
-- relevant lists are in fact permutations of each other (Step 1, Linearity).
--------------------------------------------------------------------------------

open import Categories.APROP

module Categories.APROP.Hypergraph.Completeness.Permute (sig : APROPSignature) where

open APROP sig
open import Categories.APROP.Hypergraph.Completeness.Unflatten sig
  using (unflatten)

open import Data.Fin using (Fin)
open import Data.List using (List; []; _∷_; map)
import Data.List.Relation.Binary.Permutation.Propositional as Perm
import Data.List.Relation.Binary.Permutation.Propositional.Properties as PermProp

--------------------------------------------------------------------------------
-- The core construction: by induction on the permutation proof.
--
--   refl     : id
--   prep x p : id ⊗₁ permute p
--   swap x y p :
--     unflatten (x ∷ y ∷ xs) = Var x ⊗₀ Var y ⊗₀ unflatten xs
--                            ↓ α⇐
--                              (Var x ⊗₀ Var y) ⊗₀ unflatten xs
--                            ↓ σ ⊗₁ id
--                              (Var y ⊗₀ Var x) ⊗₀ unflatten xs
--                            ↓ α⇒
--                              Var y ⊗₀ Var x ⊗₀ unflatten xs
--                            ↓ id ⊗₁ (id ⊗₁ permute p)
--                              Var y ⊗₀ Var x ⊗₀ unflatten ys
--                            = unflatten (y ∷ x ∷ ys)
--   trans p q : permute q ∘ permute p

-- Re-exported from `Categories.FreeSMC.Steps` (which re-exports
-- `permute` from PermuteCoherence.Faithfulness) so that APROP and
-- generic SMC code observe definitional equality on both `permute`
-- and `permute-via-vlab`.

open import Categories.FreeSMC.Steps asFreeMonoidalData public
  using (permute; permute-via-vlab)
