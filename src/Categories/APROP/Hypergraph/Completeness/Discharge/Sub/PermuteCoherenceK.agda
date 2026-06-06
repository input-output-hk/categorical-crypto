{-# OPTIONS --safe --with-K #-}

--------------------------------------------------------------------------------
-- The permute-coherence bridge keystone, parameterised by a
-- `FaithfulnessResidual` value `K`.
--
-- Turns Kelly's `permute-resp-≅↭` obligation into a coherence statement
-- on `Unique` codomains by feeding it the rigidity witness `eval-rigid`
-- (whose result type is definitionally the `p ≅↭ q` argument K expects).
--
-- `Unique ys` (the CODOMAIN), not `Unique xs`: `eval-rigid` uses
-- injectivity of `lookup ys`.  This is the `Unique`-guarded restriction
-- of Kelly's coherence — the unrestricted X-level statement is FALSE.
--
-- The `permute-via-vlab` corollary applies `eval-rigid` at the Fin level
-- (where `Unique` holds; `vlab` need not be injective, so `map vlab ys`
-- may have duplicates), then transports through `eval-map⁺`.
--------------------------------------------------------------------------------

open import Categories.FreeMonoidal

module Categories.APROP.Hypergraph.Completeness.Discharge.Sub.PermuteCoherenceK
  (d : FreeMonoidalData) ⦃ s≤v : Symm ≤ FreeMonoidalData.v d ⦄ where

open FreeMonoidal d
open FreeMonoidalData d using (X)

open import Data.Fin using (Fin)
open import Data.List using (List; map)
open import Data.List.Properties using (length-map)
import Data.List.Relation.Binary.Permutation.Propositional as Perm
import Data.List.Relation.Binary.Permutation.Propositional.Properties as PermProp
open Perm using (_↭_)
open import Data.List.Relation.Unary.Unique.Propositional using (Unique)
open import Relation.Binary.PropositionalEquality using (sym)

open import Categories.PermuteCoherence.Faithfulness d
  using (permute; FaithfulnessResidual)
open import Categories.FreeSMC.Steps d using (permute-via-vlab)
open import Categories.PermuteCoherence.Canonical using (_≅↭_)
open import Categories.PermuteCoherence.Eval using (eval-↭)
open import Categories.PermuteCoherence.FinBij using (FinBij; _≈-fb_)
open import Categories.PermuteCoherence.Rigid using (eval-rigid)
open import Categories.PermuteCoherence.Map
  using (eval-map⁺; subst₂-FinBij-≈; ≈-fb-resp-≡)

--------------------------------------------------------------------------------
-- 1. The X-level keystone bridge: feed `eval-rigid uniq p q` (which is
-- `p ≅↭ q` by definition) straight into the residual.

permute-≈Term-coherence-K
  : (K : FaithfulnessResidual)
    {xs ys : List X}
  → Unique ys → (p q : xs Perm.↭ ys)
  → permute p ≈Term permute q
permute-≈Term-coherence-K K uniq p q =
  FaithfulnessResidual.permute-resp-≅↭ K p q (eval-rigid uniq p q)

--------------------------------------------------------------------------------
-- 2. The downstream `permute-via-vlab` corollary: apply `eval-rigid` at
-- the Fin level, then transport through `eval-map⁺` to the X-level `≅↭`.

private
  -- `map⁺ vlab p ≅↭ map⁺ vlab q` from Fin-level rigidity.
  map⁺-≅↭
    : ∀ {n} {xs ys : List (Fin n)}
        (vlab : Fin n → X)
    → Unique ys → (p q : xs Perm.↭ ys)
    → PermProp.map⁺ vlab p ≅↭ PermProp.map⁺ vlab q
  map⁺-≅↭ {xs = xs} {ys = ys} vlab uniq p q =
    ≈-fb-resp-≡
      (sym (eval-map⁺ vlab p))
      (sym (eval-map⁺ vlab q))
      (subst₂-FinBij-≈
        (sym (length-map vlab xs))
        (sym (length-map vlab ys))
        (eval-rigid uniq p q))

permute-via-vlab-≈Term-coherence-K
  : (K : FaithfulnessResidual)
    {n : _} {xs ys : List (Fin n)}
    (vlab : Fin n → X)
  → Unique ys → (p q : xs Perm.↭ ys)
  → permute-via-vlab vlab p ≈Term permute-via-vlab vlab q
permute-via-vlab-≈Term-coherence-K K vlab uniq p q =
  FaithfulnessResidual.permute-resp-≅↭ K
    (PermProp.map⁺ vlab p) (PermProp.map⁺ vlab q)
    (map⁺-≅↭ vlab uniq p q)
