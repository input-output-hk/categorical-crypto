{-# OPTIONS --safe --with-K #-}

--------------------------------------------------------------------------------
-- SMC `Steps`-level stack permutation for the two-edge swap.
--
-- Specialises the carrier-agnostic `Categories.Hypergraph.FinalStackPerm`
-- to the SMC `Steps` setting: given `IndependentSwap e₁ e₂ s`, the two
-- `process-steps` final stacks (for the two firing orders) are `_↭_`.
--
-- This is the STACK-WITNESS half of atom (1)'s `ProcessEdges↭Goal`
-- (the `stack-↭` Σ-component).  The remaining half is the term-level
-- `≈Term` chase (built on `BraidBlock.braid-natural` + permute-faithfulness).
--
-- `--safe` clean, no postulates.
--------------------------------------------------------------------------------

open import Categories.FreeMonoidal

module Categories.FreeSMC.StackPerm
  (d : FreeMonoidalData) ⦃ s≤v : Symm ≤ FreeMonoidalData.v d ⦄ where

open FreeMonoidalData d using (X)
open import Categories.FreeSMC.Steps d

open import Categories.Hypergraph.FinalStackPerm using (final-stack-↭)

open import Data.Fin using (Fin)
open import Data.List using (List; []; _∷_; _++_)
open import Data.Nat using (ℕ)
import Data.List.Relation.Binary.Permutation.Propositional as Perm
open import Data.Product using (_,_; proj₁; proj₂)

--------------------------------------------------------------------------------
-- The two-edge swap stack permutation.
--
-- `process-steps (e₁ ∷ e₂ ∷ []) s (proj₁ indep)` computes to final
-- stack `eout e₂ ++ rest-12`; the swapped order to `eout e₁ ++ rest-21`.
-- These are `_↭_` by `final-stack-↭` applied to the four firing perms
-- unpacked from `indep`.

swap-stack-↭
  : ∀ (n : ℕ) (vlab : Fin n → X)
      (e₁ e₂ : Step n vlab) (s : List (Fin n))
      (indep : IndependentSwap n vlab e₁ e₂ s)
  → proj₁ (process-steps n vlab (e₁ ∷ e₂ ∷ []) s (proj₁ indep))
    Perm.↭
    proj₁ (process-steps n vlab (e₂ ∷ e₁ ∷ []) s (proj₂ indep))
swap-stack-↭ n vlab (a₁ , b₁ , op₁) (a₂ , b₂ , op₂) s
  ((r₁ , p1 , (r₁₂ , p12 , _)) , (r₂ , p2 , (r₂₁ , p21 , _))) =
  final-stack-↭ a₁ b₁ a₂ b₂ r₁ r₁₂ r₂ r₂₁ s p1 p12 p2 p21
