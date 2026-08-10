{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- Shared `count` / `extract-prefix` combinatorics leaf (H-agnostic).
--
-- Generic lemmas over `List (Fin n)`, collected in one leaf.  `count` is
-- from `Soundness.Linearity`; `extract-elem`/`extract-prefix` from
-- `Soundness.Decode`.
--------------------------------------------------------------------------------

open import Categories.APROP

module Categories.APROP.Hypergraph.Soundness.Discharge.CountCombinatorics
  (sig : APROPSignature) where

open import Categories.APROP.Hypergraph.Soundness.Decode.Decode sig
  using (extract-prefix; extract-elem)
open import Categories.APROP.Hypergraph.Soundness.Linearity.Linearity sig
  using (count; count-++)

open import Data.Empty using (⊥-elim)
open import Data.Fin using (Fin; zero; suc)
open import Data.Fin.Properties using (_≟_)
open import Data.List using (List; []; _∷_; _++_; map; concat)
open import Data.List.Base using (tabulate)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
import Data.List.Relation.Binary.Permutation.Propositional as Perm
import Data.List.Relation.Binary.Permutation.Propositional.Properties as PermProp
open import Data.Maybe using (just)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Nat using (s≤s⁻¹) renaming (_≤_ to _≤ⁿ_; _<_ to _<ⁿ_; s≤s to s≤sⁿ; z≤n to z≤nⁿ)
import Data.Nat.Properties as Nat
open import Data.Product using (Σ-syntax; _,_)
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)

private
  variable
    n : ℕ

--------------------------------------------------------------------------------
-- `count` cons reductions.

count-cons-yes : (v : Fin n) (xs : List (Fin n)) → count v (v ∷ xs) ≡ suc (count v xs)
count-cons-yes v xs with v ≟ v
... | yes _ = refl
... | no  q = ⊥-elim (q refl)

count-cons-no : (v x : Fin n) (xs : List (Fin n)) → ¬ (v ≡ x) → count v (x ∷ xs) ≡ count v xs
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
...   | rest , q , eq-rest rewrite eq-elem | eq-rest = rest , _ , refl

extract-prefix-just→count-≤
  : (ks xs rest : List (Fin n)) (p : xs Perm.↭ ks ++ rest)
  → ∀ v → count v ks ≤ⁿ count v xs
extract-prefix-just→count-≤ ks xs rest p v =
  Nat.≤-trans (Nat.m≤m+n (count v ks) (count v rest))
              (Nat.≤-reflexive (trans (sym (count-++ v ks rest))
                                      (sym (↭⇒count p v))))

--------------------------------------------------------------------------------
-- `count` over a `concat (tabulate f)` family: each member's count is ≤ the
-- total, and two DISTINCT members contribute disjointly.

count-concat-tabulate-≤
  : ∀ {nE} (f : Fin nE → List (Fin n)) (e : Fin nE) (v : Fin n)
  → count v (f e) ≤ⁿ count v (concat (tabulate f))
count-concat-tabulate-≤ f zero    v =
  Nat.≤-trans (Nat.m≤m+n _ _)
              (Nat.≤-reflexive (sym (count-++ v (f zero) _)))
count-concat-tabulate-≤ f (suc e) v =
  Nat.≤-trans (count-concat-tabulate-≤ (λ i → f (suc i)) e v)
              (Nat.≤-trans (Nat.m≤n+m _ _)
                           (Nat.≤-reflexive (sym (count-++ v (f zero) _))))

count-concat-tabulate-pair-≤
  : ∀ {nE} (f : Fin nE → List (Fin n)) (e e' : Fin nE) → ¬ (e ≡ e')
  → (v : Fin n)
  → count v (f e) + count v (f e') ≤ⁿ count v (concat (tabulate f))
count-concat-tabulate-pair-≤ f zero    zero     e≢e' v = ⊥-elim (e≢e' refl)
count-concat-tabulate-pair-≤ f zero    (suc e') e≢e' v =
  Nat.≤-trans
    (Nat.+-monoʳ-≤ (count v (f zero))
                   (count-concat-tabulate-≤ (λ i → f (suc i)) e' v))
    (Nat.≤-reflexive (sym (count-++ v (f zero) _)))
count-concat-tabulate-pair-≤ f (suc e) zero     e≢e' v =
  Nat.≤-trans
    (Nat.≤-reflexive (Nat.+-comm (count v (f (suc e))) (count v (f zero))))
    (Nat.≤-trans
      (Nat.+-monoʳ-≤ (count v (f zero))
                     (count-concat-tabulate-≤ (λ i → f (suc i)) e v))
      (Nat.≤-reflexive (sym (count-++ v (f zero) _))))
count-concat-tabulate-pair-≤ f (suc e) (suc e')  e≢e' v =
  Nat.≤-trans
    (count-concat-tabulate-pair-≤ (λ i → f (suc i)) e e'
      (λ eq → e≢e' (cong suc eq)) v)
    (Nat.≤-trans (Nat.m≤n+m _ _)
                 (Nat.≤-reflexive (sym (count-++ v (f zero) _))))

--------------------------------------------------------------------------------
-- Left-cancellation of a common prefix under `_↭_` (generic; count-free).

++-cancelˡ
  : ∀ (xs : List (Fin n)) {ys zs : List (Fin n)}
  → xs ++ ys Perm.↭ xs ++ zs
  → ys Perm.↭ zs
++-cancelˡ []       p = p
++-cancelˡ (x ∷ xs) p = ++-cancelˡ xs (PermProp.drop-∷ p)

--------------------------------------------------------------------------------
-- count monotonicity / split / cancellation, and the count ⇒ ↭ bridge.

count-mono-cons : ∀ {n} (v x : Fin n) (xs : List (Fin n)) → count v xs ≤ⁿ count v (x ∷ xs)
count-mono-cons v x xs with v ≟ x
... | yes _ = Nat.n≤1+n (count v xs)
... | no  _ = Nat.≤-refl

count-zero-empty : ∀ {n} (xs : List (Fin n)) → (∀ v → count v xs ≡ 0) → xs ≡ []
count-zero-empty []       _   = refl
count-zero-empty (x ∷ xs) hyp with trans (sym (count-cons-yes x xs)) (hyp x)
... | ()

count-pos→split
  : ∀ {n} (v : Fin n) (xs : List (Fin n))
  → 0 <ⁿ count v xs
  → Σ[ xs₁ ∈ List (Fin n) ] Σ[ xs₂ ∈ List (Fin n) ] xs ≡ xs₁ ++ v ∷ xs₂
count-pos→split v []       ()
count-pos→split v (x ∷ xs) c with v ≟ x
... | yes refl = [] , xs , refl
... | no  _    with count-pos→split v xs c
...               | xs₁ , xs₂ , refl = (x ∷ xs₁) , xs₂ , refl

count-cancel-cons
  : ∀ {n} (v x : Fin n) (xs ys : List (Fin n))
  → count v (x ∷ xs) ≡ count v (x ∷ ys)
  → count v xs ≡ count v ys
count-cancel-cons v x xs ys h with v ≟ x
... | yes _ = Nat.suc-injective h
... | no  _ = h

count-≡⇒↭ : ∀ {n} (xs ys : List (Fin n)) → (∀ v → count v xs ≡ count v ys) → xs Perm.↭ ys
count-≡⇒↭ []       ys hyp rewrite count-zero-empty ys (λ k → sym (hyp k)) = Perm.refl
count-≡⇒↭ (x ∷ xs) ys hyp
  with count-pos→split x ys
         (subst (0 <ⁿ_) (trans (sym (count-cons-yes x xs)) (hyp x))
                (s≤sⁿ z≤nⁿ))
... | ys₁ , ys₂ , refl =
      Perm.trans (Perm.prep x (count-≡⇒↭ xs (ys₁ ++ ys₂) sub-hyp))
                 (Perm.↭-sym (PermProp.shift x ys₁ ys₂))
      where
        sub-hyp : ∀ v → count v xs ≡ count v (ys₁ ++ ys₂)
        sub-hyp v = count-cancel-cons v x xs (ys₁ ++ ys₂)
                      (trans (hyp v)
                             (↭⇒count (PermProp.shift x ys₁ ys₂) v))

count-map-resp
  : ∀ {n m} (f : Fin n → Fin m) (xs ys : List (Fin n))
  → (∀ k → count k xs ≡ count k ys)
  → ∀ v → count v (map f xs) ≡ count v (map f ys)
count-map-resp f xs ys hyp v = ↭⇒count (PermProp.map⁺ f (count-≡⇒↭ xs ys hyp)) v
