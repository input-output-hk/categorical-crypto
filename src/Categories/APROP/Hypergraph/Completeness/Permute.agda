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

permute : ∀ {xs ys : List X} → xs Perm.↭ ys → HomTerm (unflatten xs) (unflatten ys)
permute Perm.refl         = id
permute (Perm.prep x p)   = id ⊗₁ permute p
permute (Perm.swap x y p) =
  (id ⊗₁ (id ⊗₁ permute p)) ∘ α⇒ ∘ (σ ⊗₁ id) ∘ α⇐
permute (Perm.trans p q)  = permute q ∘ permute p

--------------------------------------------------------------------------------
-- Fin-version corollary (used by `decode`): given a permutation of two
-- `List (Fin n)` and a vertex labeling `vlab : Fin n → X`, build the
-- corresponding HomTerm between the unflattened *labelled* lists.
--
-- The image lists `map vlab xs` and `map vlab ys` are also permutations of
-- each other (by `PermProp.map⁺`); we then apply `permute` directly.

permute-via-vlab
  : ∀ {n} {xs ys : List (Fin n)} (vlab : Fin n → X)
  → xs Perm.↭ ys
  → HomTerm (unflatten (map vlab xs)) (unflatten (map vlab ys))
permute-via-vlab vlab p = permute (PermProp.map⁺ vlab p)
