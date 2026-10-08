{-# OPTIONS --safe --without-K #-}

-- eval-rigid compares permutation derivations with a Unique codomain.
-- A duplicated vertex would invalidate the uniqueness-free statement.

open import Categories.APROP.Internal.Prelude

module Categories.APROP.Hypergraph.Soundness.Stack.StackUnique
  (sig : APROPSignature) where

open APROP sig
open import Categories.APROP.Hypergraph.Model.Core using (Hypergraph)
open import Categories.APROP.Hypergraph.Model.FromAPROP sig using (FlatGen)
open import Categories.APROP.Hypergraph.Model.Translation sig using (⟪_⟫)
open import Categories.Combinatorics.ExtractPrefix.Properties
  using (extract-prefix-↭-residual)
open import Categories.Combinatorics.FinCount
open import Categories.APROP.Hypergraph.Soundness.Discharge.DecodeAttemptLinearP sig
  using (⟪⟫-LinearP)
open import Categories.APROP.Hypergraph.Soundness.Linearity.Linearity sig
  using (Linear)

open import Categories.PermuteCoherence.Rigid using (_≅↭_; eval-rigid)

open import Data.Fin using (Fin)
open import Data.List.Relation.Unary.Unique.Propositional
open import Data.Nat using (ℕ) renaming (_≤_ to _≤ⁿ_)


private variable n : ℕ

Unique-resp-↭ : {xs ys : List (Fin n)} → xs Perm.↭ ys → Unique xs → Unique ys
Unique-resp-↭ p uxs = count≤1⇒Unique (λ v → subst (_≤ⁿ 1) (↭⇒count p v) (Unique⇒count≤1 uxs v))

residual-recon
  : (ks xs rest : List (Fin n)) (perm-in : xs Perm.↭ ks ++ rest)
  → Unique (ks ++ rest)
  → let st = extract-prefix-↭-residual ks xs rest perm-in in
    Perm.trans (proj₁ (proj₂ st))
               (PermProp.++⁺ˡ ks (Perm.↭-sym (proj₂ (proj₂ (proj₂ st)))))
    ≅↭ perm-in
residual-recon ks xs rest perm-in uniq =
  eval-rigid uniq
    (Perm.trans (proj₁ (proj₂ st))
                (PermProp.++⁺ˡ ks (Perm.↭-sym (proj₂ (proj₂ (proj₂ st))))))
    perm-in
  where st = extract-prefix-↭-residual ks xs rest perm-in

Linear⇒cod-Unique : (H : Hypergraph FlatGen) → Linear H → Unique (Hypergraph.cod H)
Linear⇒cod-Unique H (bal , bnd) = count≤1⇒Unique cod-bnd
  where
    module H = Hypergraph H
    cod-bnd : ∀ v → count v H.cod ≤ⁿ 1
    cod-bnd v =
      count-++-bndˡ v H.cod (concat (tabulate H.ein)) (subst (_≤ⁿ 1) (bal v) (bnd v))

⟪⟫-cod-Unique : ∀ {A B} (f : HomTerm A B) → Unique (Hypergraph.cod ⟪ f ⟫)
⟪⟫-cod-Unique f = Linear⇒cod-Unique ⟪ f ⟫ (⟪⟫-LinearP f)
