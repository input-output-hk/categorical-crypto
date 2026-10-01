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
-- Exports (postulate-free): `count`, the two `count≤1` bridge directions and
-- the two `count-++` bounds, all re-exported from `CountCombinatorics`;
-- `Unique-resp-↭` (`↭` preserves `Unique`, via that bridge), `residual-recon`,
-- and the two codomain-uniqueness faces `Linear⇒cod-Unique` / `⟪⟫-cod-Unique`
-- (the latter is read by `DecodeGen` and `TensorReconcile`).
--------------------------------------------------------------------------------

open import Categories.APROP

module Categories.APROP.Hypergraph.Soundness.Stack.StackUnique
  (sig : APROPSignature) where

open import Data.Fin using (Fin)
open import Data.Nat using (ℕ) renaming (_≤_ to _≤ⁿ_)
import Data.Nat.Properties as Nat
open import Data.List.Relation.Unary.Unique.Propositional using (Unique)

open Perm using (_↭_)


open APROP sig using (HomTerm)
open import Categories.APROP.Hypergraph.Model.Core using (Hypergraph)
open import Categories.APROP.Hypergraph.Model.FromAPROP sig using (FlatGen)
open import Categories.APROP.Hypergraph.Model.Translation sig using (⟪_⟫)
open import Categories.APROP.Hypergraph.Soundness.Linearity.Linearity sig
  using (Linear)
open import Categories.APROP.Hypergraph.Soundness.Decode.DecodeProperties sig
  using (extract-prefix-↭-residual)
open import Categories.APROP.Hypergraph.Soundness.Discharge.DecodeAttemptLinearP sig
  using (⟪⟫-LinearP)

open import Categories.PermuteCoherence.Rigid using (_≅↭_; eval-rigid)

private
  variable
    n : ℕ

--------------------------------------------------------------------------------
-- 0.  `↭`-invariance of `count` and the `Unique` ⇔ `count ≤ 1` bridge, both
--     from the shared leaf.  The bridge is re-exported because
--     `StackUniqueReach` reads them from here, together with `count` itself and
--     the two `count-++` bounds its `Unique`-of-`++` splits are
--     (`DecodeComposeAssembly` takes only `Linear⇒cod-Unique`).  One import,
--     opened twice — the second `open` is the `public` half.

import Categories.APROP.Hypergraph.Soundness.Discharge.CountCombinatorics as CC
open CC using (count-++; ↭⇒count)
open CC using (count; Unique⇒count≤1; count≤1⇒Unique; count-++-bndˡ; count-++-bndʳ) public

--------------------------------------------------------------------------------
-- 1.  `Unique-resp-↭` — the actual enabler.  `↭` preserves `count` (`↭⇒count`),
--     hence preserves the `count≤1` characterisation, hence preserves `Unique`.

Unique-resp-↭ : {xs ys : List (Fin n)} → xs Perm.↭ ys → Unique xs → Unique ys
Unique-resp-↭ p uxs = count≤1⇒Unique (λ v → subst (_≤ⁿ 1) (↭⇒count p v) (Unique⇒count≤1 uxs v))

--------------------------------------------------------------------------------
-- 2.  The Fin-index `≅↭` family, closed by `eval-rigid`.

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
-- 3.  `Linear H ⇒ Unique (cod H)` (sig-level).  A linear hypergraph has a
--     `count`-balanced, `count ≤ 1`-bounded codomain, hence a `Unique` one.
--     This is the tree's ONLY route to codomain uniqueness: the structural
--     `HomTerm`-induction twin that used to live in `Model.HomTermInvariant`
--     proved the same fact at the special case `H = ⟪f⟫` and is gone, since
--     every consumer already carries the `Linear` witness this route needs.

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

-- …at the ONE hypergraph the decoder ever asks about.  Four decoder shape
-- modules used to spell this composite (`Linear⇒cod-Unique ⟪ f ⟫ (⟪⟫-LinearP
-- f)`) locally; `⟪ f ⟫` is linear unconditionally, so the pairing is canonical
-- and belongs here, beside the general form the compose shapes still need.
⟪⟫-cod-Unique : ∀ {A B} (f : HomTerm A B) → Unique (Hypergraph.cod ⟪ f ⟫)
⟪⟫-cod-Unique f = Linear⇒cod-Unique ⟪ f ⟫ (⟪⟫-LinearP f)
