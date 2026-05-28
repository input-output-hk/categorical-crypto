{-# OPTIONS --safe --with-K #-}

--------------------------------------------------------------------------------
-- Sub-discharge of `MacLaneBundle.final-stack-↭` from
-- `Discharge/Sub/SwapMacLane.agda`.
--
-- ## Goal
--
-- Discharge the combinatorial `_↭_` between the two final stacks
-- produced by firing `(e₁ ∷ e₂ ∷ [])` vs `(e₂ ∷ e₁ ∷ [])` on the same
-- starting stack `s`, given the `IndependentSwap` precondition:
--
--   eout e₂ ++ rest-12   ↭   eout e₁ ++ rest-21
--
-- where the unpacked witnesses (via `Unpack`) are:
--
--   p-1  : s ↭ ein e₁ ++ rest-1
--   p-2  : s ↭ ein e₂ ++ rest-2
--   p-12 : eout e₁ ++ rest-1 ↭ ein e₂ ++ rest-12
--   p-21 : eout e₂ ++ rest-2 ↭ ein e₁ ++ rest-21
--
-- ## Proof strategy
--
-- The multiset identity says
--
--   eout e₂ ++ rest-12   =m=   s + eout e₁ + eout e₂ - ein e₁ - ein e₂
--                         =m=  eout e₁ ++ rest-21
--
-- where `=m=` denotes multiset equality.  Constructively, we cannot
-- subtract, but we can ADD common terms on both sides and then cancel.
--
-- We show:
--
--   ein e₁ ++ ein e₂ ++ eout e₂ ++ rest-12
--     ↭ eout e₂ ++ eout e₁ ++ s         (via p-12 and p-1)
--     ↭ ein e₁ ++ ein e₂ ++ eout e₁ ++ rest-21   (symmetric, via p-21 and p-2)
--
-- Then cancel the common prefix `ein e₁ ++ ein e₂` by iterated `drop-∷`.
--
-- ## File is `--safe --with-K`-clean.  Fully constructive.  No postulates.
--------------------------------------------------------------------------------

open import Categories.APROP
open import Categories.APROP.Hypergraph.Solver.Signature using (APROPSignatureDec)

module Categories.APROP.Hypergraph.Completeness.Discharge.Sub.FinalStackPerm
  (sig-dec : APROPSignatureDec) where

open APROPSignatureDec sig-dec using (sig)
open APROP sig

open import Categories.APROP.Hypergraph.Core using (Hypergraph)
open import Categories.APROP.Hypergraph.FromAPROP sig using (FlatGen)
open import Categories.APROP.Hypergraph.Completeness.Discharge.Sub.ProcessTermAligned
  sig-dec
  using (AllFire; IndependentSwap)
open import Categories.APROP.Hypergraph.Completeness.Discharge.Sub.SwapAtomAligned
  sig-dec
  using (module Unpack)

open import Data.Fin using (Fin)
open import Data.List using (List; []; _∷_; _++_)
import Data.List.Relation.Binary.Permutation.Propositional as Perm
import Data.List.Relation.Binary.Permutation.Propositional.Properties as PermProp

--------------------------------------------------------------------------------
-- ## Section 1: list-prefix cancellation for `_↭_`.
--
-- The cancellation `pre ++ xs ↭ pre ++ ys → xs ↭ ys` is not in the
-- stdlib for arbitrary lists `pre` (only the single-element version
-- `drop-∷` exists), so we provide it here by induction on `pre`.

++-cancelˡ-↭
  : ∀ {a} {A : Set a} (pre : List A) {xs ys : List A}
  → pre ++ xs Perm.↭ pre ++ ys
  → xs Perm.↭ ys
++-cancelˡ-↭ []         p = p
++-cancelˡ-↭ (x ∷ pre)  p = ++-cancelˡ-↭ pre (PermProp.drop-∷ p)

--------------------------------------------------------------------------------
-- ## Section 2: The combinatorial final-stack `_↭_`.
--
-- The proof builds the augmented chain through `eout e₂ ++ eout e₁ ++ s`
-- and then cancels the prefix `ein e₁ ++ ein e₂` by iterated `drop-∷`.

final-stack-↭
  : ∀ (H : Hypergraph FlatGen) (e₁ e₂ : Fin (Hypergraph.nE H))
      (s : List (Fin (Hypergraph.nV H)))
      (indep : IndependentSwap H e₁ e₂ s)
      (let open Unpack H e₁ e₂ s indep)
  → Hypergraph.eout H e₂ ++ rest-12
    Perm.↭
    Hypergraph.eout H e₁ ++ rest-21
final-stack-↭ H e₁ e₂ s indep =
  ++-cancelˡ-↭ (H.ein e₂) (++-cancelˡ-↭ (H.ein e₁) augmented)
  where
    module H = Hypergraph H
    open Unpack H e₁ e₂ s indep
    open Perm.PermutationReasoning

    -- LHS-augmentation chain.
    lhs-chain
      : H.ein e₁ ++ H.ein e₂ ++ H.eout e₂ ++ rest-12
        Perm.↭ H.eout e₂ ++ H.eout e₁ ++ s
    lhs-chain = begin
        H.ein e₁ ++ H.ein e₂ ++ H.eout e₂ ++ rest-12
      ↭⟨ PermProp.++⁺ˡ (H.ein e₁)
           (PermProp.shifts (H.ein e₂) (H.eout e₂)) ⟩
        H.ein e₁ ++ H.eout e₂ ++ H.ein e₂ ++ rest-12
      ↭⟨ PermProp.++⁺ˡ (H.ein e₁)
           (PermProp.++⁺ˡ (H.eout e₂) (Perm.↭-sym p-12)) ⟩
        H.ein e₁ ++ H.eout e₂ ++ H.eout e₁ ++ rest-1
      ↭⟨ PermProp.shifts (H.ein e₁) (H.eout e₂) ⟩
        H.eout e₂ ++ H.ein e₁ ++ H.eout e₁ ++ rest-1
      ↭⟨ PermProp.++⁺ˡ (H.eout e₂)
           (PermProp.shifts (H.ein e₁) (H.eout e₁)) ⟩
        H.eout e₂ ++ H.eout e₁ ++ H.ein e₁ ++ rest-1
      ↭⟨ PermProp.++⁺ˡ (H.eout e₂)
           (PermProp.++⁺ˡ (H.eout e₁) (Perm.↭-sym p-1)) ⟩
        H.eout e₂ ++ H.eout e₁ ++ s
      ∎

    -- RHS-augmentation chain (symmetric).
    rhs-chain
      : H.ein e₁ ++ H.ein e₂ ++ H.eout e₁ ++ rest-21
        Perm.↭ H.eout e₂ ++ H.eout e₁ ++ s
    rhs-chain = begin
        H.ein e₁ ++ H.ein e₂ ++ H.eout e₁ ++ rest-21
      ↭⟨ PermProp.shifts (H.ein e₁) (H.ein e₂) ⟩
        H.ein e₂ ++ H.ein e₁ ++ H.eout e₁ ++ rest-21
      ↭⟨ PermProp.++⁺ˡ (H.ein e₂)
           (PermProp.shifts (H.ein e₁) (H.eout e₁)) ⟩
        H.ein e₂ ++ H.eout e₁ ++ H.ein e₁ ++ rest-21
      ↭⟨ PermProp.++⁺ˡ (H.ein e₂)
           (PermProp.++⁺ˡ (H.eout e₁) (Perm.↭-sym p-21)) ⟩
        H.ein e₂ ++ H.eout e₁ ++ H.eout e₂ ++ rest-2
      ↭⟨ PermProp.shifts (H.ein e₂) (H.eout e₁) ⟩
        H.eout e₁ ++ H.ein e₂ ++ H.eout e₂ ++ rest-2
      ↭⟨ PermProp.++⁺ˡ (H.eout e₁)
           (PermProp.shifts (H.ein e₂) (H.eout e₂)) ⟩
        H.eout e₁ ++ H.eout e₂ ++ H.ein e₂ ++ rest-2
      ↭⟨ PermProp.++⁺ˡ (H.eout e₁)
           (PermProp.++⁺ˡ (H.eout e₂) (Perm.↭-sym p-2)) ⟩
        H.eout e₁ ++ H.eout e₂ ++ s
      ↭⟨ PermProp.shifts (H.eout e₁) (H.eout e₂) ⟩
        H.eout e₂ ++ H.eout e₁ ++ s
      ∎

    -- Combine: LHS-aug ↭ middle ↭ RHS-aug-reversed.
    augmented
      : H.ein e₁ ++ H.ein e₂ ++ H.eout e₂ ++ rest-12
        Perm.↭
        H.ein e₁ ++ H.ein e₂ ++ H.eout e₁ ++ rest-21
    augmented = Perm.trans lhs-chain (Perm.↭-sym rhs-chain)
