{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- Phase 3.5f Step 3.5f-A — Foundation lemmas for `extract-elem`,
-- `extract-prefix`, and `extract-exact` (defined in `Decode.agda`).
--
-- These reduce the per-case `decode-attempt-h*` postulates to
-- statements about disjoint Fin injections and `Unique` lists, which
-- are already proved on the soundness side (`Invariant.agda`,
-- `Linearity.agda`).
--
-- Currently provided:
--   * `extract-elem-self`         : `extract-elem k (k ∷ xs) ≡ just (xs , Perm.refl)`.
--   * `extract-elem-skip`         : on a head ≢ `k`, the search prepends
--                                   the head and recurses.
--   * `extract-elem-skip-↑ˡ-≢-↑ʳ` : the disjoint-injection no-match case.
--   * `extract-elem-skip-↑ʳ-≢-↑ˡ` : symmetric counterpart.
--   * `extract-prefix-[]`         : `extract-prefix [] xs ≡ just (xs , Perm.refl)`.
--
-- Future: `extract-elem-find-mapped`, `extract-prefix-self`,
-- `extract-prefix-disjoint-skip`, `extract-prefix-mapped`,
-- `extract-exact-self` — still pending.
--------------------------------------------------------------------------------

open import Categories.APROP

module Categories.APROP.Hypergraph.Completeness.DecodeProperties (sig : APROPSignature) where

open APROP sig
open import Categories.APROP.Hypergraph.Completeness.Decode sig
  using (extract-elem; extract-prefix; extract-exact)
open import Categories.APROP.Hypergraph.Invariant sig
  using (inject+-inj; raise-inj; disj-L-R)

open import Data.Empty using (⊥-elim)
open import Data.Fin using (Fin; _↑ˡ_; _↑ʳ_; splitAt)
open import Data.Fin.Properties using (_≟_; splitAt-↑ˡ; splitAt-↑ʳ)
open import Data.List using (List; []; _∷_; _++_; map)
import Data.List.Relation.Binary.Permutation.Propositional as Perm
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ)
open import Data.Product using (Σ-syntax; ∃-syntax; _,_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong)
open import Relation.Nullary using (yes; no)
open import Relation.Nullary.Negation using (¬_)

--------------------------------------------------------------------------------
-- (1) `extract-elem` on a head match returns `just (xs , p)` for some
-- permutation `p`.  We don't pin `p` down to `Perm.refl` because
-- `extract-elem`'s body uses `subst (… ≡ …) p Perm.refl`, and `subst`
-- with a reflexive equation doesn't simplify under `--without-K`.

extract-elem-self
  : ∀ {n} (k : Fin n) (xs : List (Fin n))
  → Σ[ p ∈ ((k ∷ xs) Perm.↭ k ∷ xs) ]
      extract-elem k (k ∷ xs) ≡ just (xs , p)
extract-elem-self k xs with k ≟ k
... | yes a = _ , refl
... | no  q = ⊥-elim (q refl)

--------------------------------------------------------------------------------
-- (2) `extract-elem` skips a non-matching head.  Phrased as: when
-- `x ≢ k`, the result is whatever `extract-elem k xs` returns, with
-- the head prepended onto the residual (and the permutation extended
-- with a `prep + swap` step).
--
-- Stated in two halves to match the `Maybe` shape of `extract-elem`'s
-- output: a "nothing-stays-nothing" half and a "just-pre-pends" half.

extract-elem-skip-nothing
  : ∀ {n} (k x : Fin n) (xs : List (Fin n))
  → ¬ (x ≡ k)
  → extract-elem k xs ≡ nothing
  → extract-elem k (x ∷ xs) ≡ nothing
extract-elem-skip-nothing k x xs x≢k eq with x ≟ k
... | yes p = ⊥-elim (x≢k p)
... | no  _ rewrite eq = refl

extract-elem-skip-just
  : ∀ {n} (k x : Fin n) (xs : List (Fin n))
      (rest : List (Fin n)) (p : xs Perm.↭ k ∷ rest)
  → ¬ (x ≡ k)
  → extract-elem k xs ≡ just (rest , p)
  → extract-elem k (x ∷ xs)
    ≡ just ( x ∷ rest
           , Perm.trans (Perm.prep x p) (Perm.swap x k Perm.refl) )
extract-elem-skip-just k x xs rest p x≢k eq with x ≟ k
... | yes q = ⊥-elim (x≢k q)
... | no  _ rewrite eq = refl

--------------------------------------------------------------------------------
-- (3-3'): `extract-elem` on a disjoint-injection mismatch returns
-- `nothing` for any list whose elements are all on the wrong side.
-- Specialised to single-element heads first (the building block);
-- list-level lemmas come below.

private
  ↑ˡ≢↑ʳ : ∀ {nA nB} (i : Fin nA) (j : Fin nB) → ¬ (i ↑ˡ nB ≡ nA ↑ʳ j)
  ↑ˡ≢↑ʳ {nA} {nB} i j p
    with trans (sym (splitAt-↑ˡ nA i nB))
               (trans (cong (splitAt nA) p) (splitAt-↑ʳ nA nB j))
  ... | ()

  ↑ʳ≢↑ˡ : ∀ {nA nB} (i : Fin nA) (j : Fin nB) → ¬ (nA ↑ʳ j ≡ i ↑ˡ nB)
  ↑ʳ≢↑ˡ i j p = ↑ˡ≢↑ʳ i j (sym p)

extract-elem-↑ʳ-on-↑ˡ-list
  : ∀ {nA nB} (j : Fin nB) (xs : List (Fin nA))
  → extract-elem (nA ↑ʳ j) (map (_↑ˡ nB) xs) ≡ nothing
extract-elem-↑ʳ-on-↑ˡ-list j []       = refl
extract-elem-↑ʳ-on-↑ˡ-list {nA} {nB} j (x ∷ xs) =
  extract-elem-skip-nothing (nA ↑ʳ j) (x ↑ˡ nB) (map (_↑ˡ nB) xs)
    (↑ˡ≢↑ʳ x j)
    (extract-elem-↑ʳ-on-↑ˡ-list j xs)

extract-elem-↑ˡ-on-↑ʳ-list
  : ∀ {nA nB} (i : Fin nA) (xs : List (Fin nB))
  → extract-elem (i ↑ˡ nB) (map (nA ↑ʳ_) xs) ≡ nothing
extract-elem-↑ˡ-on-↑ʳ-list i []       = refl
extract-elem-↑ˡ-on-↑ʳ-list {nA} {nB} i (x ∷ xs) =
  extract-elem-skip-nothing (i ↑ˡ nB) (nA ↑ʳ x) (map (nA ↑ʳ_) xs)
    (↑ʳ≢↑ˡ i x)
    (extract-elem-↑ˡ-on-↑ʳ-list i xs)

--------------------------------------------------------------------------------
-- (extract-prefix-[]): immediate from the definition.

extract-prefix-[]
  : ∀ {n} (xs : List (Fin n))
  → extract-prefix [] xs ≡ just (xs , Perm.refl)
extract-prefix-[] xs = refl

--------------------------------------------------------------------------------
-- (5) `extract-prefix-self`: searching for `xs` in `xs` itself
-- always succeeds with empty residual.  Independent of any
-- uniqueness hypothesis — even on lists with duplicates, the
-- algorithm peels off heads one at a time and `extract-elem k (k ∷ ks)`
-- always matches at the head.

extract-prefix-self
  : ∀ {n} (xs : List (Fin n))
  → Σ[ p ∈ (xs Perm.↭ xs ++ []) ] extract-prefix xs xs ≡ just ([] , p)
extract-prefix-self []       = Perm.refl , refl
extract-prefix-self (x ∷ xs) with extract-elem-self x xs
... | p1 , eq1 with extract-prefix-self xs
...               | p2 , eq2
                  rewrite eq1 | eq2 = _ , refl

--------------------------------------------------------------------------------
-- (8) `extract-exact-self`: searching for `xs` exactly in `xs`
-- succeeds.  Follows from (5) by composition.

extract-exact-self
  : ∀ {n} (xs : List (Fin n))
  → Σ[ p ∈ (xs Perm.↭ xs) ] extract-exact xs xs ≡ just p
extract-exact-self xs with extract-prefix-self xs
... | p , eq rewrite eq = _ , refl

--------------------------------------------------------------------------------
-- (4, 6, 7) Lifting through injection — TODO.
--
-- The remaining foundation lemmas (`extract-elem-↑ˡ-mapped-success`,
-- `extract-prefix-disjoint-skip`, `extract-prefix-mapped`) require a
-- triple-`with` chain on `x ≟ k` / `(x ↑ˡ nB) ≟ (k ↑ˡ nB)` /
-- `extract-elem k xs in eq-inner`.  Agda's parser handles the
-- resulting nested-aux indentation awkwardly; phrasing them as
-- existentials and going through `inject+-inj` / `raise-inj` works in
-- principle but the Agda mechanics are fiddly.  Deferred — when
-- `decode-attempt-hSwap` / `decode-attempt-hGen` actually need them,
-- they can be inlined as case-specific helpers (the lists involved
-- there are concrete enough that the proofs are simpler than the
-- fully general statement above).
