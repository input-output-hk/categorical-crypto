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
-- Provided here:
--
--   Single-list lemmas:
--     * `extract-elem-self`             — head match returns just _.
--     * `extract-elem-skip-{nothing,just}` — head ≢ k skipping.
--     * `extract-elem-{↑ʳ-on-↑ˡ,↑ˡ-on-↑ʳ}-list` — disjoint injection no-match.
--     * `extract-elem-{↑ˡ-on-↑ˡ,↑ʳ-on-↑ʳ}-list-nothing` — same-injection no-match.
--     * `extract-prefix-[]`             — empty prefix is trivial.
--     * `extract-prefix-self`           — searching `xs` in `xs` succeeds.
--     * `extract-exact-self`            — exact-match search of `xs` in `xs`.
--
--   Membership / permutation lemmas:
--     * `extract-elem-found`            — `y ∈ xs` ⇒ search succeeds.
--     * `extract-prefix-from-↭`         — `xs ↭ ys` ⇒ exact-prefix search.
--
--   Mixed-injection lifting (for `decode-attempt-hTensor`):
--     * `extract-elem-↑ˡ-on-mixed-{nothing,just}`
--     * `extract-elem-↑ʳ-on-mixed-{nothing,just}`
--     * `extract-prefix-↑ˡ-on-mixed-just`
--     * `extract-prefix-↑ʳ-on-mixed-just`
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
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
import Data.List.Relation.Binary.Permutation.Propositional as Perm
import Data.List.Relation.Binary.Permutation.Propositional.Properties as PermProp
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
-- Lifting `extract-elem` / `extract-prefix` through disjoint
-- injections (for `decode-attempt-hTensor`).
--
-- These lemmas relate searches on a "pure side" list (e.g. `xs`)
-- to searches on a "mixed" list (`map (_↑ˡ nB) xs ++ map (nA ↑ʳ_) ys`)
-- when the key lives entirely on one side.

--------------------------------------------------------------------------------
-- `nothing` direction.  If the underlying search returns `nothing`,
-- the lifted search on the mixed list also returns `nothing` (the L
-- side has no match, the R side mismatches by disjointness).

extract-elem-↑ˡ-on-mixed-nothing
  : ∀ {nA} nB (k : Fin nA) (xs : List (Fin nA)) (ys : List (Fin nB))
  → extract-elem k xs ≡ nothing
  → extract-elem (k ↑ˡ nB) (map (_↑ˡ nB) xs ++ map (nA ↑ʳ_) ys) ≡ nothing
extract-elem-↑ˡ-on-mixed-nothing {nA} nB k []       ys _  =
  extract-elem-↑ˡ-on-↑ʳ-list k ys
extract-elem-↑ˡ-on-mixed-nothing {nA} nB k (x ∷ xs) ys eq with x ≟ k
extract-elem-↑ˡ-on-mixed-nothing {nA} nB k (x ∷ xs) ys eq | yes p with eq
... | ()
extract-elem-↑ˡ-on-mixed-nothing {nA} nB k (x ∷ xs) ys eq | no  q
    with extract-elem k xs in eq-inner
... | nothing =
      extract-elem-skip-nothing
        (k ↑ˡ nB) (x ↑ˡ nB) (map (_↑ˡ nB) xs ++ map (nA ↑ʳ_) ys)
        (λ p₁ → q (inject+-inj nB p₁))
        (extract-elem-↑ˡ-on-mixed-nothing nB k xs ys eq-inner)
... | just _ with eq
... | ()

--------------------------------------------------------------------------------
-- Helper: pure-injection-mapped list, lookup on the same side.
-- `extract-elem (k ↑ˡ nB) (map (_↑ˡ nB) xs)` returns nothing iff
-- `extract-elem k xs` returns nothing.

extract-elem-↑ˡ-on-↑ˡ-list-nothing
  : ∀ {nA} nB (k : Fin nA) (xs : List (Fin nA))
  → extract-elem k xs ≡ nothing
  → extract-elem (k ↑ˡ nB) (map (_↑ˡ nB) xs) ≡ nothing
extract-elem-↑ˡ-on-↑ˡ-list-nothing nB k []       _ = refl
extract-elem-↑ˡ-on-↑ˡ-list-nothing nB k (x ∷ xs) eq with x ≟ k
extract-elem-↑ˡ-on-↑ˡ-list-nothing nB k (x ∷ xs) eq | yes p with eq
... | ()
extract-elem-↑ˡ-on-↑ˡ-list-nothing nB k (x ∷ xs) eq | no  q
    with extract-elem k xs in eq-inner
... | nothing =
      extract-elem-skip-nothing
        (k ↑ˡ nB) (x ↑ˡ nB) (map (_↑ˡ nB) xs)
        (λ p₁ → q (inject+-inj nB p₁))
        (extract-elem-↑ˡ-on-↑ˡ-list-nothing nB k xs eq-inner)
... | just _ with eq
... | ()

extract-elem-↑ʳ-on-↑ʳ-list-nothing
  : ∀ nA {nB} (j : Fin nB) (ys : List (Fin nB))
  → extract-elem j ys ≡ nothing
  → extract-elem (nA ↑ʳ j) (map (nA ↑ʳ_) ys) ≡ nothing
extract-elem-↑ʳ-on-↑ʳ-list-nothing nA j []       _ = refl
extract-elem-↑ʳ-on-↑ʳ-list-nothing nA j (x ∷ ys) eq with x ≟ j
extract-elem-↑ʳ-on-↑ʳ-list-nothing nA j (x ∷ ys) eq | yes p with eq
... | ()
extract-elem-↑ʳ-on-↑ʳ-list-nothing nA j (x ∷ ys) eq | no  q
    with extract-elem j ys in eq-inner
... | nothing =
      extract-elem-skip-nothing
        (nA ↑ʳ j) (nA ↑ʳ x) (map (nA ↑ʳ_) ys)
        (λ p₁ → q (raise-inj nA p₁))
        (extract-elem-↑ʳ-on-↑ʳ-list-nothing nA j ys eq-inner)
... | just _ with eq
... | ()

--------------------------------------------------------------------------------
-- Symmetric R-side lifting.

extract-elem-↑ʳ-on-mixed-nothing
  : ∀ nA {nB} (j : Fin nB) (xs : List (Fin nA)) (ys : List (Fin nB))
  → extract-elem j ys ≡ nothing
  → extract-elem (nA ↑ʳ j) (map (_↑ˡ nB) xs ++ map (nA ↑ʳ_) ys) ≡ nothing
extract-elem-↑ʳ-on-mixed-nothing nA j []       ys eq =
  extract-elem-↑ʳ-on-↑ʳ-list-nothing nA j ys eq
extract-elem-↑ʳ-on-mixed-nothing nA j (x ∷ xs) ys eq =
  extract-elem-skip-nothing
    (nA ↑ʳ j) (x ↑ˡ _) (map (_↑ˡ _) xs ++ map (nA ↑ʳ_) ys)
    (↑ˡ≢↑ʳ x j)
    (extract-elem-↑ʳ-on-mixed-nothing nA j xs ys eq)

--------------------------------------------------------------------------------
-- `just` direction (L-side).  If extract-elem k xs succeeds, the
-- lifted version on (mapL xs ++ mapR ys) also succeeds, with the
-- residual being the lifted underlying residual + the preserved R
-- side.

extract-elem-↑ˡ-on-mixed-just
  : ∀ {nA} nB (k : Fin nA) (xs : List (Fin nA)) (ys : List (Fin nB))
      (rest : List (Fin nA)) (p : xs Perm.↭ k ∷ rest)
  → extract-elem k xs ≡ just (rest , p)
  → ∃[ q ] extract-elem (k ↑ˡ nB) (map (_↑ˡ nB) xs ++ map (nA ↑ʳ_) ys)
              ≡ just (map (_↑ˡ nB) rest ++ map (nA ↑ʳ_) ys , q)
extract-elem-↑ˡ-on-mixed-just nB k []       ys rest p ()
extract-elem-↑ˡ-on-mixed-just {nA} nB k (x ∷ xs) ys rest p eq
    with x ≟ k
extract-elem-↑ˡ-on-mixed-just {nA} nB k (x ∷ xs) ys rest p eq | yes p₁
    with (x ↑ˡ nB) ≟ (k ↑ˡ nB)
... | yes p₂ with eq
...             | refl = _ , refl
extract-elem-↑ˡ-on-mixed-just {nA} nB k (x ∷ xs) ys rest p eq | yes p₁ | no  q₂ =
    ⊥-elim (q₂ (cong (_↑ˡ nB) p₁))
extract-elem-↑ˡ-on-mixed-just {nA} nB k (x ∷ xs) ys rest p eq | no  q₁
    with extract-elem k xs in eq-inner
... | nothing with eq
...              | ()
extract-elem-↑ˡ-on-mixed-just {nA} nB k (x ∷ xs) ys rest p eq | no q₁ | just (rest₁ , p₁)
    with (x ↑ˡ nB) ≟ (k ↑ˡ nB)
... | yes p₂ = ⊥-elim (q₁ (inject+-inj nB p₂))
... | no  q₂ with eq
...             | refl
                with extract-elem-↑ˡ-on-mixed-just nB k xs ys rest₁ p₁ eq-inner
...               | _ , eq-↑ˡ
                  rewrite eq-↑ˡ = _ , refl

--------------------------------------------------------------------------------
-- `just` direction (R-side, symmetric).

extract-elem-↑ʳ-on-mixed-just
  : ∀ nA {nB} (j : Fin nB) (xs : List (Fin nA)) (ys : List (Fin nB))
      (rest : List (Fin nB)) (p : ys Perm.↭ j ∷ rest)
  → extract-elem j ys ≡ just (rest , p)
  → ∃[ q ] extract-elem (nA ↑ʳ j) (map (_↑ˡ _) xs ++ map (nA ↑ʳ_) ys)
              ≡ just (map (_↑ˡ _) xs ++ map (nA ↑ʳ_) rest , q)
extract-elem-↑ʳ-on-mixed-just nA j xs []       rest p ()
extract-elem-↑ʳ-on-mixed-just nA j []       (y ∷ ys) rest p eq
    with y ≟ j
extract-elem-↑ʳ-on-mixed-just nA j []       (y ∷ ys) rest p eq | yes p₁
    with (nA ↑ʳ y) ≟ (nA ↑ʳ j)
... | yes p₂ with eq
...             | refl = _ , refl
extract-elem-↑ʳ-on-mixed-just nA j []       (y ∷ ys) rest p eq | yes p₁ | no  q₂ =
    ⊥-elim (q₂ (cong (nA ↑ʳ_) p₁))
extract-elem-↑ʳ-on-mixed-just nA j []       (y ∷ ys) rest p eq | no  q₁
    with extract-elem j ys in eq-inner
... | nothing with eq
...              | ()
extract-elem-↑ʳ-on-mixed-just nA j []       (y ∷ ys) rest p eq | no q₁ | just (rest₁ , p₁)
    with (nA ↑ʳ y) ≟ (nA ↑ʳ j)
... | yes p₂ = ⊥-elim (q₁ (raise-inj nA p₂))
... | no  q₂ with eq
...             | refl
                with extract-elem-↑ʳ-on-mixed-just nA j [] ys rest₁ p₁ eq-inner
...               | _ , eq-↑ʳ
                  rewrite eq-↑ʳ = _ , refl
extract-elem-↑ʳ-on-mixed-just nA j (x ∷ xs) (y ∷ ys) rest p eq
    with extract-elem-↑ʳ-on-mixed-just nA j xs (y ∷ ys) rest p eq
... | q' , eq-rec =
      _ ,
      extract-elem-skip-just (nA ↑ʳ j) (x ↑ˡ _)
        (map (_↑ˡ _) xs ++ map (nA ↑ʳ_) (y ∷ ys))
        (map (_↑ˡ _) xs ++ map (nA ↑ʳ_) rest) q'
        (↑ˡ≢↑ʳ x j) eq-rec

--------------------------------------------------------------------------------
-- `extract-prefix` lifting: success direction.

extract-prefix-↑ˡ-on-mixed-just
  : ∀ {nA} nB (ks xs : List (Fin nA)) (ys : List (Fin nB))
      (rest : List (Fin nA)) (p : xs Perm.↭ ks ++ rest)
  → extract-prefix ks xs ≡ just (rest , p)
  → ∃[ q ] extract-prefix (map (_↑ˡ nB) ks)
                          (map (_↑ˡ nB) xs ++ map (nA ↑ʳ_) ys)
              ≡ just (map (_↑ˡ nB) rest ++ map (nA ↑ʳ_) ys , q)
extract-prefix-↑ˡ-on-mixed-just nB []       xs ys rest p eq with eq
... | refl = _ , refl
extract-prefix-↑ˡ-on-mixed-just {nA} nB (k ∷ ks) xs ys rest p eq
    with extract-elem k xs in eq-elem
... | nothing with eq
...              | ()
extract-prefix-↑ˡ-on-mixed-just {nA} nB (k ∷ ks) xs ys rest p eq
    | just (xs' , p-elem)
    with extract-prefix ks xs' in eq-prefix
... | nothing with eq
...              | ()
extract-prefix-↑ˡ-on-mixed-just {nA} nB (k ∷ ks) xs ys rest p eq
    | just (xs' , p-elem) | just (rest' , p-prefix) with eq
... | refl
    with extract-elem-↑ˡ-on-mixed-just nB k xs ys xs' p-elem eq-elem
       | extract-prefix-↑ˡ-on-mixed-just nB ks xs' ys rest' p-prefix eq-prefix
... | _ , eq-elem-↑ˡ | _ , eq-prefix-↑ˡ
    rewrite eq-elem-↑ˡ | eq-prefix-↑ˡ = _ , refl

extract-prefix-↑ʳ-on-mixed-just
  : ∀ nA {nB} (ks : List (Fin nB)) (xs : List (Fin nA)) (ys : List (Fin nB))
      (rest : List (Fin nB)) (p : ys Perm.↭ ks ++ rest)
  → extract-prefix ks ys ≡ just (rest , p)
  → ∃[ q ] extract-prefix (map (nA ↑ʳ_) ks)
                          (map (_↑ˡ nB) xs ++ map (nA ↑ʳ_) ys)
              ≡ just (map (_↑ˡ nB) xs ++ map (nA ↑ʳ_) rest , q)
extract-prefix-↑ʳ-on-mixed-just nA []       xs ys rest p eq with eq
... | refl = _ , refl
extract-prefix-↑ʳ-on-mixed-just nA (k ∷ ks) xs ys rest p eq
    with extract-elem k ys in eq-elem
... | nothing with eq
...              | ()
extract-prefix-↑ʳ-on-mixed-just nA (k ∷ ks) xs ys rest p eq
    | just (ys' , p-elem)
    with extract-prefix ks ys' in eq-prefix
... | nothing with eq
...              | ()
extract-prefix-↑ʳ-on-mixed-just nA (k ∷ ks) xs ys rest p eq
    | just (ys' , p-elem) | just (rest' , p-prefix) with eq
... | refl
    with extract-elem-↑ʳ-on-mixed-just nA k xs ys ys' p-elem eq-elem
       | extract-prefix-↑ʳ-on-mixed-just nA ks xs ys' rest' p-prefix eq-prefix
... | _ , eq-elem-↑ʳ | _ , eq-prefix-↑ʳ
    rewrite eq-elem-↑ʳ | eq-prefix-↑ʳ = _ , refl

--------------------------------------------------------------------------------
-- `extract-prefix` lifting: failure direction.  If the underlying
-- search returns `nothing`, the lifted search on the mixed list also
-- returns `nothing`.  Used by the per-edge lifting in `DecodeAttempt`
-- to handle the case where an edge cannot fire.

extract-prefix-↑ˡ-on-mixed-nothing
  : ∀ {nA} nB (ks xs : List (Fin nA)) (ys : List (Fin nB))
  → extract-prefix ks xs ≡ nothing
  → extract-prefix (map (_↑ˡ nB) ks)
                   (map (_↑ˡ nB) xs ++ map (nA ↑ʳ_) ys)
       ≡ nothing
extract-prefix-↑ˡ-on-mixed-nothing nB []       xs ys ()
extract-prefix-↑ˡ-on-mixed-nothing {nA} nB (k ∷ ks) xs ys eq
    with extract-elem k xs in eq-elem
... | nothing
    rewrite extract-elem-↑ˡ-on-mixed-nothing nB k xs ys eq-elem
    = refl
extract-prefix-↑ˡ-on-mixed-nothing {nA} nB (k ∷ ks) xs ys eq
    | just (xs' , p-elem)
    with extract-prefix ks xs' in eq-prefix
... | nothing
    with extract-elem-↑ˡ-on-mixed-just nB k xs ys xs' p-elem eq-elem
... | _ , eq-elem-↑ˡ
    rewrite eq-elem-↑ˡ
          | extract-prefix-↑ˡ-on-mixed-nothing nB ks xs' ys eq-prefix
    = refl
extract-prefix-↑ˡ-on-mixed-nothing {nA} nB (k ∷ ks) xs ys eq
    | just (xs' , p-elem) | just (rest , p-prefix)
    with eq
... | ()

extract-prefix-↑ʳ-on-mixed-nothing
  : ∀ nA {nB} (ks : List (Fin nB)) (xs : List (Fin nA)) (ys : List (Fin nB))
  → extract-prefix ks ys ≡ nothing
  → extract-prefix (map (nA ↑ʳ_) ks)
                   (map (_↑ˡ nB) xs ++ map (nA ↑ʳ_) ys)
       ≡ nothing
extract-prefix-↑ʳ-on-mixed-nothing nA []       xs ys ()
extract-prefix-↑ʳ-on-mixed-nothing nA (k ∷ ks) xs ys eq
    with extract-elem k ys in eq-elem
... | nothing
    rewrite extract-elem-↑ʳ-on-mixed-nothing nA k xs ys eq-elem
    = refl
extract-prefix-↑ʳ-on-mixed-nothing nA (k ∷ ks) xs ys eq
    | just (ys' , p-elem)
    with extract-prefix ks ys' in eq-prefix
... | nothing
    with extract-elem-↑ʳ-on-mixed-just nA k xs ys ys' p-elem eq-elem
... | _ , eq-elem-↑ʳ
    rewrite eq-elem-↑ʳ
          | extract-prefix-↑ʳ-on-mixed-nothing nA ks xs ys' eq-prefix
    = refl
extract-prefix-↑ʳ-on-mixed-nothing nA (k ∷ ks) xs ys eq
    | just (ys' , p-elem) | just (rest , p-prefix)
    with eq
... | ()

--------------------------------------------------------------------------------
-- (9) `extract-elem-found`: a membership witness `y ∈ xs` constructively
-- produces a successful `extract-elem y xs ≡ just (rest, p)`.
--
-- Pattern-match the membership; in the `there mem'` case, recurse on
-- `xs` and lift via `extract-elem-skip-just` (the latter does its own
-- `with x ≟ y`, so we keep the outer signature clean).

extract-elem-found
  : ∀ {n} (y : Fin n) (xs : List (Fin n))
  → y ∈ xs
  → ∃[ rest ] ∃[ p ] extract-elem y xs ≡ just (rest , p)
extract-elem-found y (x ∷ xs) (here refl) with y ≟ y
... | yes _ = _ , _ , refl
... | no  q = ⊥-elim (q refl)
extract-elem-found y (x ∷ xs) (there mem) with x ≟ y
... | yes _   = _ , _ , refl
... | no  q   with extract-elem-found y xs mem
...              | _ , _ , eq rewrite eq = _ , _ , refl

--------------------------------------------------------------------------------
-- (10) `extract-prefix-from-↭`: a permutation `xs ↭ ys` constructively
-- produces a successful `extract-prefix ys xs ≡ just ([], p)`.
--
-- This is THE key lemma for `decode-attempt-hSwap`: combined with
-- stdlib's `Perm.++-comm`, it discharges `extract-exact (R ++ L) (L ++ R)`.
-- Strategy: induct on `ys`, extracting the head element via `∈-resp-↭`
-- and `extract-elem-found`, then cancel via `drop-∷` for the recursive
-- call.

extract-prefix-from-↭
  : ∀ {n} (xs ys : List (Fin n))
  → xs Perm.↭ ys
  → ∃[ p ] extract-prefix ys xs ≡ just ([] , p)
extract-prefix-from-↭ xs []       p
    with PermProp.↭-empty-inv p
... | refl = Perm.refl , refl
extract-prefix-from-↭ xs (y ∷ ys') p
    with extract-elem-found y xs (PermProp.∈-resp-↭ (Perm.↭-sym p) (here refl))
... | rest , q , eq-extract
    with extract-prefix-from-↭ rest ys'
           (PermProp.drop-∷ (Perm.↭-trans (Perm.↭-sym q) p))
... | r , eq-prefix
    rewrite eq-extract | eq-prefix = _ , refl
