{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- Stack-Uniqueness, and the close of the eval-coincidence residual family
-- (`residual-recon`, `coh-in`/`coh-out`) via `Rigid.eval-rigid`.
--
-- `eval-rigid` says: two `↭`-derivations `p, q : xs ↭ ys` with a `Unique`
-- codomain `ys` evaluate to the SAME finite bijection, hence `p ≅↭ q`.  Every
-- member of the eval-coincidence family compares two `↭`s with a COMMON
-- Fin-index codomain; once that codomain is known `Unique`, `eval-rigid`
-- closes the comparison in one line.  (The uniqueness-FREE generic forms are
-- actually FALSE: a duplicated vertex breaks them.)
--
-- Exports (postulate-free): `Unique-resp-↭` (`↭` preserves `Unique`, the
-- enabler, via a `count≤1` bridge); `residual-recon-unique` /
-- `residual-recon`; `coh-fin-rigid`; and the FIRE-step uniqueness facts.
--
-- The FIRE-step verdict: the local claim `Unique s → Linear H → Unique (proj₁
-- (edge-step H s e))` is FALSE for an arbitrary `Unique s` (counterexample at
-- the bottom): `Unique (eout e ++ rest)` needs `eout e` count-disjoint from
-- `rest`, a reachability invariant of `process-edges`, NOT a consequence of
-- `Unique s` alone.  So we prove the SOUND `++-Unique-from-counts` whose
-- disjointness side-condition is supplied at the call site.
--------------------------------------------------------------------------------

open import Categories.APROP

module Categories.APROP.Hypergraph.Completeness.Discharge.Sub.StackUnique
  (sig : APROPSignature) where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin using (Fin)
open import Data.Fin.Properties using (_≟_)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Nat using (s≤s⁻¹) renaming (_≤_ to _≤ⁿ_; _<_ to _<ⁿ_; s≤s to s≤sⁿ; z≤n to z≤nⁿ)
import Data.Nat.Properties as Nat
open import Data.List using (List; []; _∷_; _++_; length; lookup)
open import Data.Product using (Σ; Σ-syntax; _,_; _×_; proj₁; proj₂)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (Any; here; there)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.List.Relation.Unary.AllPairs using ([]; _∷_)
open import Data.List.Relation.Unary.Unique.Propositional using (Unique)

import Data.List.Relation.Binary.Permutation.Propositional as Perm
open Perm using (_↭_)
import Data.List.Relation.Binary.Permutation.Propositional.Properties as PermProp

open import Relation.Nullary using (¬_; yes; no)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; subst)

open import Categories.APROP.Hypergraph.Core using (Hypergraph)
open import Categories.APROP.Hypergraph.FromAPROP sig using (FlatGen)
open import Categories.APROP.Hypergraph.Completeness.Linearity sig
  using (count; count-++)
open import Categories.APROP.Hypergraph.Completeness.Decode sig
  using (edge-step; extract-prefix)
open import Categories.APROP.Hypergraph.Completeness.DecodeProperties sig
  using (extract-prefix-↭-residual)

open import Data.Maybe using (Maybe; just; nothing)

-- PermuteCoherence machinery.
open import Categories.PermuteCoherence.Canonical using (_≅↭_)
open import Categories.PermuteCoherence.Rigid using (eval-rigid)

private
  variable
    n : ℕ

--------------------------------------------------------------------------------
-- 0.  `count` cons reductions and `↭`-invariance (shared leaf).

open import Categories.APROP.Hypergraph.Completeness.Discharge.Sub.CountCombinatorics sig
  using (count-cons-yes; count-cons-no; ↭⇒count; ∈→count-pos)

--------------------------------------------------------------------------------
-- 1.  `Unique` ⇔ "every element occurs at most once".
--
-- `Unique xs` (= `AllPairs _≢_ xs`) iff `∀ v → count v xs ≤ 1`.

-- count ≤ 1 abbreviation.
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

  count-mono-cons : (v x : Fin n) (xs : List (Fin n))
                  → count v xs ≤ⁿ count v (x ∷ xs)
  count-mono-cons v x xs with v ≟ x
  ... | yes _ = Nat.n≤1+n (count v xs)
  ... | no  _ = Nat.≤-refl

count≤1⇒Unique : ∀ {xs : List (Fin n)} → count≤1 xs → Unique xs
count≤1⇒Unique {xs = []}      _ = []
count≤1⇒Unique {xs = x ∷ xs}  h =
  count0⇒All≢ x∉xs ∷ count≤1⇒Unique tail-h
  where
    x∉xs : count x xs ≡ 0
    x∉xs = Nat.n≤0⇒n≡0
             (s≤s⁻¹ (Nat.≤-trans (Nat.≤-reflexive (sym (count-cons-yes x xs))) (h x)))
    tail-h : count≤1 xs
    tail-h v = Nat.≤-trans (count-mono-cons v x xs) (h v)

--------------------------------------------------------------------------------
-- 2.  `Unique-resp-↭` — the actual enabler.  `↭` preserves `count` (`↭⇒count`),
--     hence preserves the `count≤1` characterisation, hence preserves `Unique`.

Unique-resp-↭ : {xs ys : List (Fin n)} → xs Perm.↭ ys → Unique xs → Unique ys
Unique-resp-↭ p uxs =
  count≤1⇒Unique
    (λ v → subst (_≤ⁿ 1) (↭⇒count p v) (Unique⇒count≤1 uxs v))

--------------------------------------------------------------------------------
-- 3.  Sub-list uniqueness facts used to supply `Unique` codomain witnesses.

++-Unique-left : (xs ys : List (Fin n)) → Unique (xs ++ ys) → Unique xs
++-Unique-left xs ys u =
  count≤1⇒Unique
    (λ v → Nat.≤-trans (Nat.≤-trans (Nat.m≤m+n (count v xs) (count v ys))
                                    (Nat.≤-reflexive (sym (count-++ v xs ys))))
                       (Unique⇒count≤1 u v))

++-Unique-right : (xs ys : List (Fin n)) → Unique (xs ++ ys) → Unique ys
++-Unique-right xs ys u =
  count≤1⇒Unique
    (λ v → Nat.≤-trans (Nat.≤-trans (Nat.m≤n+m (count v ys) (count v xs))
                                    (Nat.≤-reflexive (sym (count-++ v xs ys))))
                       (Unique⇒count≤1 u v))

-- The append of two `Unique` lists is `Unique` provided the per-vertex counts
-- never both exceed zero: i.e. the two are count-disjoint.  This is the SOUND
-- form of the FIRE-step `eout e ++ rest` uniqueness (the disjointness
-- side-condition is supplied at the call site from firing stability).
++-Unique-from-counts
  : (xs ys : List (Fin n))
  → count≤1 xs → count≤1 ys
  → (∀ v → 0 <ⁿ count v xs → count v ys ≡ 0)
  → Unique (xs ++ ys)
++-Unique-from-counts xs ys cx cy disj =
  count≤1⇒Unique sum≤1
  where
    sum≤1 : ∀ v → count v (xs ++ ys) ≤ⁿ 1
    sum≤1 v with count v xs Nat.<? 1
    ... | yes <1 =
          Nat.≤-trans
            (Nat.≤-reflexive
              (trans (count-++ v xs ys)
                     (cong (_+ count v ys) (Nat.n<1⇒n≡0 <1))))
            (cy v)
    ... | no  ≮1 =
          Nat.≤-trans
            (Nat.≤-reflexive
              (trans (count-++ v xs ys)
                     (trans (cong (count v xs +_) (disj v 0<cx))
                            (Nat.+-identityʳ (count v xs)))))
            (cx v)
      where
        0<cx : 0 <ⁿ count v xs
        0<cx = Nat.≮⇒≥ ≮1

--------------------------------------------------------------------------------
-- 3.5  `edge-step` uniqueness, split as `EdgeStepRelation`'s `skipR`/`fireR`.
--   * NO-FIRE: the stack is unchanged, `Unique` preserved unconditionally.
--   * FIRE: the stack becomes `eout e ++ rest`; `Unique (eout e ++ rest)` is
--     the SOUND `++-Unique-from-counts`, its disjointness side-condition
--     supplied at the `process-edges` level (NOT derivable from `Unique s`
--     alone — see the counterexample at the bottom of the file).

module _ (H : Hypergraph FlatGen) where
  private module H = Hypergraph H

  -- NO-FIRE: `extract-prefix (ein e) s ≡ nothing` ⇒ `edge-step` returns `s`.
  edge-step-unique-skip
    : ∀ (s : List (Fin H.nV)) (e : Fin H.nE)
    → extract-prefix (H.ein e) s ≡ nothing
    → Unique s
    → Unique (proj₁ (edge-step H s e))
  edge-step-unique-skip s e eq us
    rewrite eq = us

  -- FIRE: post-fire stack is `eout e ++ rest`; stated directly on it,
  -- carrying the count-disjointness side-condition threaded by the caller.
  edge-step-unique-fire
    : ∀ (e : Fin H.nE) {s rest : List (Fin H.nV)}
        (perm : s Perm.↭ H.ein e ++ rest)
    → Unique s
    → Unique (H.eout e)
    → (∀ v → 0 <ⁿ count v (H.eout e) → count v rest ≡ 0)
    → Unique (H.eout e ++ rest)
  edge-step-unique-fire e {s} {rest} perm us ueo disj =
    ++-Unique-from-counts (H.eout e) rest
      (Unique⇒count≤1 ueo)
      (Unique⇒count≤1 u-rest)
      disj
    where
      u-ein-rest : Unique (H.ein e ++ rest)
      u-ein-rest = Unique-resp-↭ perm us
      u-rest : Unique rest
      u-rest = ++-Unique-right (H.ein e) rest u-ein-rest

--------------------------------------------------------------------------------
-- 4.  The Fin-index `≅↭` family, closed by `eval-rigid`.

-- 4a.  `coh-fin-rigid` — any two `↭`s with a common `Unique` codomain are
--      `≅↭` (= `eval-rigid`).
coh-fin-rigid
  : ∀ {m} {xs ys : List (Fin m)} (p q : xs Perm.↭ ys)
  → Unique ys
  → p ≅↭ q
coh-fin-rigid p q uniq = eval-rigid uniq p q

-- 4b.  `residual-recon-unique` — `residual-recon`'s conclusion (both sides
--      `xs ↭ ks ++ rest`), carrying a `Unique (ks ++ rest)` hypothesis,
--      closed in ONE line by `eval-rigid`.  At the `StackEquivariance` call
--      site the codomain `ein e ++ restH` is the `↭`-image of the decoder
--      stack `s'`, so the witness is `Unique-resp-↭ perm-in (Unique s')`.
residual-recon-unique
  : ∀ {m} (ks xs rest : List (Fin m)) (perm-in : xs Perm.↭ ks ++ rest)
      (st-located : xs Perm.↭ ks ++ rest)
  → Unique (ks ++ rest)
  → st-located ≅↭ perm-in
residual-recon-unique ks xs rest perm-in st-located uniq =
  eval-rigid uniq st-located perm-in

-- Packaged abstractly over an assembled `lhs : xs ↭ ks ++ rest`, so it
-- matches whatever the `extract-prefix-↭-residual` re-assembly evaluates to.
residual-recon-via-rigid
  : ∀ {m} {xs ks-rest : List (Fin m)}
      (lhs perm-in : xs Perm.↭ ks-rest)
  → Unique ks-rest
  → lhs ≅↭ perm-in
residual-recon-via-rigid lhs perm-in uniq = eval-rigid uniq lhs perm-in

-- 4c.  The drop-in for `StackEquivariance.residual-recon`, modulo a `Unique
--      (ks ++ rest)` hypothesis, using the REAL `extract-prefix-↭-residual`.
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
-- ## COUNTEREXAMPLE to the local FIRE-step claim.
--
-- `Unique s → Linear H → Unique (proj₁ (edge-step H s e))` is FALSE for an
-- arbitrary `Unique s`.  Over `Fin 1` (vertex `v = 0F`): take `H` with
-- nV=1, nE=1, dom=[], cod=[v], ein 0=[], eout 0=[v] (so `Linear H` holds),
-- and `s = [v]` (`Unique`).  Then `edge-step H [v] 0` fires with `rest = [v]`,
-- giving the new stack `eout 0 ++ rest = [v , v]` — NOT `Unique`.
--
-- The flaw: `Unique (eout e ++ rest)` needs `eout e` count-disjoint from
-- `rest`, a reachability invariant of `process-edges`, not a property of
-- `Unique s` alone.  `++-Unique-from-counts` takes that disjointness as an
-- explicit hypothesis.
--------------------------------------------------------------------------------
