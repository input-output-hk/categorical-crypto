{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- Stack-Uniqueness and the close of the stack-`≅↭` residual family
-- (`residual-recon`) via `Rigid.eval-rigid`.
--
-- `eval-rigid` says: two `↭`-derivations `p, q : xs ↭ ys` with a `Unique`
-- codomain `ys` evaluate to the SAME finite bijection, hence `p ≅↭ q`.  Once
-- the common Fin-index codomain is known `Unique`, `eval-rigid` closes the
-- comparison in one line.  (The uniqueness-FREE generic form is actually
-- FALSE: a duplicated vertex breaks it.)
--
-- Exports (postulate-free): `count≤1⇒Unique`, `Unique-resp-↭` (`↭` preserves
-- `Unique`, via a `count≤1` bridge), `Linear⇒cod-Unique`, and `residual-recon`.
--------------------------------------------------------------------------------

open import Categories.APROP

module Categories.APROP.Hypergraph.Soundness.Stack.StackUnique
  (sig : APROPSignature) where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin using (Fin)
open import Data.Fin.Properties using (_≟_)
open import Data.Nat using (ℕ; suc; _+_)
open import Data.Nat using (s≤s⁻¹) renaming (_≤_ to _≤ⁿ_; z≤n to z≤nⁿ)
import Data.Nat.Properties as Nat
open import Data.List using (List; []; _∷_; _++_; concat; tabulate)
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.List.Relation.Unary.AllPairs using ([]; _∷_)
open import Data.List.Relation.Unary.Unique.Propositional using (Unique)

import Data.List.Relation.Binary.Permutation.Propositional as Perm
open Perm using (_↭_)
import Data.List.Relation.Binary.Permutation.Propositional.Properties as PermProp

open import Relation.Nullary using (¬_; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)

open import Categories.APROP.Hypergraph.Model.Core using (Hypergraph)
open import Categories.APROP.Hypergraph.Model.FromAPROP sig using (FlatGen)
open import Categories.APROP.Hypergraph.Soundness.Linearity.Linearity sig
  using (count; count-++; Linear)
open import Categories.APROP.Hypergraph.Soundness.Decode.DecodeProperties sig
  using (extract-prefix-↭-residual)

open import Categories.PermuteCoherence.Canonical using (_≅↭_)
open import Categories.PermuteCoherence.Rigid using (eval-rigid)

private
  variable
    n : ℕ

--------------------------------------------------------------------------------
-- 0.  `count` cons reductions and `↭`-invariance (shared leaf).

open import Categories.APROP.Hypergraph.Soundness.Discharge.CountCombinatorics sig
  using (count-cons-yes; count-cons-no; ↭⇒count; count-mono-cons)

--------------------------------------------------------------------------------
-- 1.  `Unique` ⇔ "every element occurs at most once".
--
-- `Unique xs` (= `AllPairs _≢_ xs`) iff `∀ v → count v xs ≤ 1`.

count≤1 : List (Fin n) → Set
count≤1 xs = ∀ v → count v xs ≤ⁿ 1

-- Forward: `Unique xs → count≤1 xs`.
private
  All≢⇒count0 : ∀ {x : Fin n} {xs} → All (λ y → ¬ (x ≡ y)) xs → count x xs ≡ 0
  All≢⇒count0 {x = x} {[]}      []          = refl
  All≢⇒count0 {x = x} {y ∷ xs} (x≢y ∷ rest) =
    trans (count-cons-no x y xs x≢y) (All≢⇒count0 rest)

  -- Casing on `v ≟ x` HERE keeps the result type in terms of the
  -- un-abstracted `count v (x ∷ xs)`, so the `count-cons-*` lemmas apply.
  count-cons-le1 : (v x : Fin n) (xs : List (Fin n))
                 → count x xs ≡ 0 → count v xs ≤ⁿ 1 → count v (x ∷ xs) ≤ⁿ 1
  count-cons-le1 v x xs hx ht with v ≟ x
  ... | yes refl = Nat.≤-reflexive (cong suc hx)
  ... | no  _    = ht

Unique⇒count≤1 : ∀ {xs : List (Fin n)} → Unique xs → count≤1 xs
Unique⇒count≤1 {xs = []}      []            v = z≤nⁿ
Unique⇒count≤1 {xs = x ∷ xs} (x≢ ∷ uq)      v =
  count-cons-le1 v x xs (All≢⇒count0 x≢) (Unique⇒count≤1 uq v)

-- Backward: `count≤1 xs → Unique xs`.
private
  -- `count v (v ∷ xs) ≢ 0` (inlines the `v ≟ v` view to dodge the
  -- with-abstraction mismatch from applying `count-cons-yes` after `refl`).
  count-head-not-0 : (v : Fin n) (xs : List (Fin n)) → count v (v ∷ xs) ≡ 0 → ⊥
  count-head-not-0 v xs c0 with v ≟ v
  ... | yes _ = case-suc c0
    where case-suc : suc (count v xs) ≡ 0 → ⊥
          case-suc ()
  ... | no q  = ⊥-elim (q refl)

  count0⇒All≢ : ∀ {x : Fin n} {xs} → count x xs ≡ 0 → All (λ y → ¬ (x ≡ y)) xs
  count0⇒All≢ {x = x} {[]}     _  = []
  count0⇒All≢ {x = x} {y ∷ xs} c0 = head≢ ∷ count0⇒All≢ {x = x} {xs} tail0
    where
      head≢ : ¬ (x ≡ y)
      head≢ refl = count-head-not-0 x xs c0
      tail0 : count x xs ≡ 0
      tail0 = trans (sym (count-cons-no x y xs head≢)) c0

count≤1⇒Unique : ∀ {xs : List (Fin n)} → count≤1 xs → Unique xs
count≤1⇒Unique {xs = []}      _ = []
count≤1⇒Unique {xs = x ∷ xs}  h =
  count0⇒All≢ x∉xs ∷ count≤1⇒Unique tail-h
  where
    x∉xs : count x xs ≡ 0
    x∉xs = Nat.n≤0⇒n≡0 (s≤s⁻¹ (Nat.≤-trans (Nat.≤-reflexive (sym (count-cons-yes x xs))) (h x)))
    tail-h : count≤1 xs
    tail-h v = Nat.≤-trans (count-mono-cons v x xs) (h v)

--------------------------------------------------------------------------------
-- 2.  `Unique-resp-↭` — the actual enabler.  `↭` preserves `count` (`↭⇒count`),
--     hence preserves the `count≤1` characterisation, hence preserves `Unique`.

Unique-resp-↭ : {xs ys : List (Fin n)} → xs Perm.↭ ys → Unique xs → Unique ys
Unique-resp-↭ p uxs = count≤1⇒Unique (λ v → subst (_≤ⁿ 1) (↭⇒count p v) (Unique⇒count≤1 uxs v))

--------------------------------------------------------------------------------
-- 3.  The Fin-index `≅↭` family, closed by `eval-rigid`.

-- Closes the stack-`≅↭` residual (consumed by `Strict/Interchange/
-- StackEquiv`), modulo a `Unique (ks ++ rest)` hypothesis, via the real
-- `extract-prefix-↭-residual`.
residual-recon
  : ∀ {m} (ks xs rest : List (Fin m)) (perm-in : xs Perm.↭ ks ++ rest)
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

--------------------------------------------------------------------------------
-- 4.  `Linear H ⇒ Unique (cod H)` (sig-level).  A linear hypergraph has a
--     `count`-balanced, `count ≤ 1`-bounded codomain, hence a `Unique` one.

Linear⇒cod-Unique : (H : Hypergraph FlatGen) → Linear H → Unique (Hypergraph.cod H)
Linear⇒cod-Unique H (bal , bnd) = count≤1⇒Unique cod-bnd
  where
    module H = Hypergraph H
    cod-bnd : ∀ v → count v H.cod ≤ⁿ 1
    cod-bnd v =
      Nat.≤-trans
        (Nat.≤-trans
          (Nat.m≤m+n (count v H.cod) (count v (concat (tabulate H.ein))))
          (Nat.≤-reflexive (sym (count-++ v H.cod (concat (tabulate H.ein))))))
        (Nat.≤-trans (Nat.≤-reflexive (sym (bal v))) (bnd v))
