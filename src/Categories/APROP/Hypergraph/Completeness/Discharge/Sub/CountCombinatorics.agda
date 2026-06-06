{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- Shared `count` / `extract-prefix` combinatorics leaf (H-agnostic).
--
-- These small, generic lemmas over `List (Fin n)` were duplicated verbatim as
-- `private` blocks across many `Discharge`/`Discharge/Sub` modules (each of
-- which re-derived them because the original copies live in inaccessible
-- `private` blocks of `Completeness.Linearity` / `SwapValidity`).  This module
-- collects them in ONE `--without-K` leaf so the consumers can import them.
--
-- `count` itself (and `count-++`) is defined in `Completeness.Linearity`, which
-- this module imports.  `extract-elem` / `extract-prefix` come from
-- `Completeness.Decode`.  All lemmas are FULLY CONSTRUCTIVE and postulate-free.
--
-- NOTE: this is a `--without-K` module; it can be imported by both `--with-K`
-- and `--without-K` consumers.
--------------------------------------------------------------------------------

open import Categories.APROP

module Categories.APROP.Hypergraph.Completeness.Discharge.Sub.CountCombinatorics
  (sig : APROPSignature) where

open import Categories.APROP.Hypergraph.Completeness.Decode sig
  using (extract-prefix; extract-elem)
open import Categories.APROP.Hypergraph.Completeness.Linearity sig
  using (count; count-++)

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin using (Fin; zero; suc)
open import Data.Fin.Properties using (_≟_)
open import Data.List using (List; []; _∷_; _++_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
import Data.List.Relation.Binary.Permutation.Propositional as Perm
import Data.List.Relation.Binary.Permutation.Propositional.Properties as PermProp
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Nat using (s≤s⁻¹) renaming (_≤_ to _≤ⁿ_; _<_ to _<ⁿ_; s≤s to s≤sⁿ; z≤n to z≤nⁿ)
import Data.Nat.Properties as Nat
open import Data.Product using (Σ; Σ-syntax; _,_; _×_; proj₁; proj₂)
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; subst)

private
  variable
    n : ℕ

--------------------------------------------------------------------------------
-- `count` cons reductions.

count-cons-yes : (v : Fin n) (xs : List (Fin n))
               → count v (v ∷ xs) ≡ suc (count v xs)
count-cons-yes v xs with v ≟ v
... | yes _ = refl
... | no  q = ⊥-elim (q refl)

count-cons-no : (v x : Fin n) (xs : List (Fin n)) → ¬ (v ≡ x)
              → count v (x ∷ xs) ≡ count v xs
count-cons-no v x xs v≢x with v ≟ x
... | yes p = ⊥-elim (v≢x p)
... | no  _ = refl

--------------------------------------------------------------------------------
-- `count` ↔ membership.

∈→count-pos : ∀ {v : Fin n} {xs} → v ∈ xs → 0 <ⁿ count v xs
∈→count-pos {v = v} {x ∷ xs} (here refl)  rewrite count-cons-yes v xs = s≤sⁿ z≤nⁿ
∈→count-pos {v = v} {x ∷ xs} (there v∈xs) with v ≟ x
... | yes _ = s≤sⁿ z≤nⁿ
... | no  _ = ∈→count-pos v∈xs

count-pos→∈ : ∀ {v : Fin n} {xs} → 0 <ⁿ count v xs → v ∈ xs
count-pos→∈ {v = v} {[]}     ()
count-pos→∈ {v = v} {x ∷ xs} c with v ≟ x
... | yes refl = here refl
... | no  _    = there (count-pos→∈ c)

--------------------------------------------------------------------------------
-- Permutation preserves `count`.

↭⇒count : {xs ys : List (Fin n)} → xs Perm.↭ ys → ∀ v → count v xs ≡ count v ys
↭⇒count Perm.refl                       v = refl
↭⇒count (Perm.prep x p)                 v with v ≟ x
... | yes _ = cong suc (↭⇒count p v)
... | no  _ = ↭⇒count p v
↭⇒count (Perm.swap {xs = xs} {ys = ys} x y p) v = swap-case (v ≟ x) (v ≟ y)
  where
    swap-case : _ → _ → count v (x ∷ y ∷ xs) ≡ count v (y ∷ x ∷ ys)
    swap-case (yes refl) (yes refl) =
      trans (count-cons-yes v (v ∷ xs))
      (trans (cong suc (count-cons-yes v xs))
      (trans (cong suc (cong suc (↭⇒count p v)))
      (trans (cong suc (sym (count-cons-yes v ys)))
             (sym (count-cons-yes v (v ∷ ys))))))
    swap-case (yes refl) (no  q) =
      trans (count-cons-yes v (y ∷ xs))
      (trans (cong suc (count-cons-no v y xs q))
      (trans (cong suc (↭⇒count p v))
      (trans (sym (count-cons-yes v ys))
             (sym (count-cons-no v y (v ∷ ys) q)))))
    swap-case (no  q) (yes refl) =
      trans (count-cons-no v x (v ∷ xs) q)
      (trans (count-cons-yes v xs)
      (trans (cong suc (↭⇒count p v))
      (trans (cong suc (sym (count-cons-no v x ys q)))
             (sym (count-cons-yes v (x ∷ ys))))))
    swap-case (no  q₁) (no  q₂) =
      trans (count-cons-no v x (y ∷ xs) q₁)
      (trans (count-cons-no v y xs q₂)
      (trans (↭⇒count p v)
      (trans (sym (count-cons-no v x ys q₁))
             (sym (count-cons-no v y (x ∷ ys) q₂)))))
↭⇒count (Perm.trans p₁ p₂)              v = trans (↭⇒count p₁ v) (↭⇒count p₂ v)

--------------------------------------------------------------------------------
-- `extract-elem` / `extract-prefix` succeed under the corresponding count
-- bounds (and the residual count is the input minus the located prefix).

count-pos→extract-elem
  : (k : Fin n) (xs : List (Fin n)) → 0 <ⁿ count k xs
  → Σ[ rest ∈ List (Fin n) ] Σ[ p ∈ xs Perm.↭ k ∷ rest ]
      extract-elem k xs ≡ just (rest , p)
count-pos→extract-elem k []       ()
count-pos→extract-elem k (x ∷ xs) c with x ≟ k
... | yes refl = xs , _ , refl
... | no  x≢k  with count-pos→extract-elem k xs
                    (subst (0 <ⁿ_) (count-cons-no k x xs (λ e → x≢k (sym e))) c)
...   | rest , p , eq rewrite eq = x ∷ rest , _ , refl

count-≤→extract-prefix
  : (ks xs : List (Fin n)) → (∀ v → count v ks ≤ⁿ count v xs)
  → Σ[ rest ∈ List (Fin n) ] Σ[ p ∈ xs Perm.↭ ks ++ rest ]
      extract-prefix ks xs ≡ just (rest , p)
count-≤→extract-prefix []       xs h = xs , Perm.refl , refl
count-≤→extract-prefix (k ∷ ks) xs h
  with count-pos→extract-elem k xs
         (Nat.<-≤-trans (s≤sⁿ z≤nⁿ)
           (Nat.≤-trans (Nat.≤-reflexive (sym (count-cons-yes k ks))) (h k)))
... | xs' , p , eq-elem
    with count-≤→extract-prefix ks xs' h-rest
  where
    h-rest : ∀ v → count v ks ≤ⁿ count v xs'
    h-rest v with v ≟ k
    ... | yes refl =
          s≤s⁻¹
            (Nat.≤-trans (Nat.≤-reflexive (sym (count-cons-yes k ks)))
            (Nat.≤-trans (h k)
                         (Nat.≤-reflexive
                           (trans (↭⇒count p k) (count-cons-yes k xs')))))
    ... | no  v≢k =
          Nat.≤-trans (Nat.≤-reflexive (sym (count-cons-no v k ks v≢k)))
          (Nat.≤-trans (h v)
                       (Nat.≤-reflexive
                         (trans (↭⇒count p v) (count-cons-no v k xs' v≢k))))
...   | rest , q , eq-rest rewrite eq-elem | eq-rest =
        rest , _ , refl

--------------------------------------------------------------------------------
-- Left-cancellation of a common prefix under `_↭_` (generic; count-free).

++-cancelˡ
  : ∀ (xs : List (Fin n)) {ys zs : List (Fin n)}
  → xs ++ ys Perm.↭ xs ++ zs
  → ys Perm.↭ zs
++-cancelˡ []       p = p
++-cancelˡ (x ∷ xs) p = ++-cancelˡ xs (PermProp.drop-∷ p)
