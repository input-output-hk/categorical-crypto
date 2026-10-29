{-# OPTIONS --safe --without-K #-}

module Categories.Combinatorics.FinCount where

open import Categories.Combinatorics.ExtractPrefix

open import Data.Empty
open import Data.Fin using (Fin; zero; suc; _↑ˡ_; _↑ʳ_)
open import Data.Fin.Properties using (_≟_; suc-injective; ↑ˡ-injective; ↑ʳ-injective)
open import Data.Fin.Properties.Ext
open import Data.List.Base
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Properties.Ext using (allFin-suc)
import Data.List.Relation.Binary.Permutation.Propositional as Perm
import Data.List.Relation.Binary.Permutation.Propositional.Properties as PermProp
import Data.List.Relation.Binary.Permutation.Setoid.Properties as SetoidPropM
import Data.List.Relation.Unary.All as All
import Data.List.Relation.Unary.AllPairs as AllPairs
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Relation.Unary.Unique.Propositional
open import Data.Maybe using (just)
open import Data.Nat using (ℕ; zero; suc; _+_; s≤s⁻¹)
  renaming (_≤_ to _≤ⁿ_; _<_ to _<ⁿ_; s≤s to s≤sⁿ; z≤n to z≤nⁿ)
import Data.Nat.Properties as Nat
open import Data.Product using (Σ-syntax; _,_)
open import Function.Base using (case_of_)
open import Relation.Binary.PropositionalEquality
open import Relation.Binary.PropositionalEquality.Properties using () renaming (setoid to ≡-setoid)
open import Relation.Nullary

private
  variable
    n m nE k nA nB : ℕ
    x v : Fin n
    xs ys : List (Fin n)

module SetoidProp {n} = SetoidPropM (≡-setoid (Fin n))

count : Fin n → List (Fin n) → ℕ
count v []       = 0
count v (x ∷ xs) = case v ≟ x of λ where
  (yes _) → suc (count v xs)
  (no _) → count v xs

count-++ : (v : Fin n) (xs ys : List (Fin n)) → count v (xs ++ ys) ≡ count v xs + count v ys
count-++ v []       ys = refl
count-++ v (x ∷ xs) ys with v ≟ x
... | yes _ = cong suc (count-++ v xs ys)
... | no  _ = count-++ v xs ys

count-cons-yes : (v : Fin n) (xs : List (Fin n)) → count v (v ∷ xs) ≡ suc (count v xs)
count-cons-yes v xs with v ≟ v
... | yes _ = refl
... | no  q = ⊥-elim (q refl)

count-cons-no : (v x : Fin n) (xs : List (Fin n)) → ¬ (v ≡ x) → count v (x ∷ xs) ≡ count v xs
count-cons-no v x xs v≢x with v ≟ x
... | yes p = ⊥-elim (v≢x p)
... | no  _ = refl

count-mono-cons : (v x : Fin n) (xs : List (Fin n)) → count v xs ≤ⁿ count v (x ∷ xs)
count-mono-cons v x xs with v ≟ x
... | yes _ = Nat.n≤1+n (count v xs)
... | no  _ = Nat.≤-refl

--------------------------------------------------------------------------------
-- Uniqueness and counts
--------------------------------------------------------------------------------
count≤1 : List (Fin n) → Set
count≤1 xs = ∀ v → count v xs ≤ⁿ 1

private
  All≢⇒count0 : All.All (λ y → ¬ (x ≡ y)) xs → count x xs ≡ 0
  All≢⇒count0 {x = x} {[]}      All.[]           = refl
  All≢⇒count0 {x = x} {y ∷ xs} (x≢y All.∷ rest) =
    trans (count-cons-no x y xs x≢y) (All≢⇒count0 rest)

  -- Casing on `v ≟ x` HERE keeps the result type in terms of the
  -- un-abstracted `count v (x ∷ xs)`, so the `count-cons-*` lemmas apply.
  count-cons-le1 : (v x : Fin n) (xs : List (Fin n))
                 → count x xs ≡ 0 → count v xs ≤ⁿ 1 → count v (x ∷ xs) ≤ⁿ 1
  count-cons-le1 v x xs hx ht with v ≟ x
  ... | yes refl = Nat.≤-reflexive (cong suc hx)
  ... | no  _    = ht

Unique⇒count≤1 : Unique xs → count≤1 xs
Unique⇒count≤1 {xs = []}      AllPairs.[]        v = z≤nⁿ
Unique⇒count≤1 {xs = x ∷ xs} (x≢ AllPairs.∷ uq) v =
  count-cons-le1 v x xs (All≢⇒count0 x≢) (Unique⇒count≤1 uq v)

private
  -- `count v (v ∷ xs) ≢ 0` (inlines the `v ≟ v` view to dodge the
  -- with-abstraction mismatch from applying `count-cons-yes` after `refl`).
  count-head-not-0 : (v : Fin n) (xs : List (Fin n)) → count v (v ∷ xs) ≡ 0 → ⊥
  count-head-not-0 v xs c0 with v ≟ v
  ... | yes _ = case-suc c0
    where case-suc : suc (count v xs) ≡ 0 → ⊥
          case-suc ()
  ... | no q  = ⊥-elim (q refl)

  count0⇒All≢ : count x xs ≡ 0 → All.All (λ y → ¬ (x ≡ y)) xs
  count0⇒All≢ {x = x} {[]}     _  = All.[]
  count0⇒All≢ {x = x} {y ∷ xs} c0 = head≢ All.∷ count0⇒All≢ {x = x} {xs} tail0
    where
      head≢ : ¬ (x ≡ y)
      head≢ refl = count-head-not-0 x xs c0
      tail0 : count x xs ≡ 0
      tail0 = trans (sym (count-cons-no x y xs head≢)) c0

count≤1⇒Unique : count≤1 xs → Unique xs
count≤1⇒Unique {xs = []}      _ = AllPairs.[]
count≤1⇒Unique {xs = x ∷ xs}  h =
  count0⇒All≢ x∉xs AllPairs.∷ count≤1⇒Unique tail-h
  where
    x∉xs : count x xs ≡ 0
    x∉xs = Nat.n≤0⇒n≡0 (s≤s⁻¹ (Nat.≤-trans (Nat.≤-reflexive (sym (count-cons-yes x xs))) (h x)))
    tail-h : count≤1 xs
    tail-h v = Nat.≤-trans (count-mono-cons v x xs) (h v)

∈→count-pos : v ∈ xs → 0 <ⁿ count v xs
∈→count-pos {v = v} {x ∷ xs} (here refl)  rewrite count-cons-yes v xs = s≤sⁿ z≤nⁿ
∈→count-pos {v = v} {x ∷ xs} (there v∈xs) with v ≟ x
... | yes _ = s≤sⁿ z≤nⁿ
... | no  _ = ∈→count-pos v∈xs

count-pos→∈ : 0 <ⁿ count v xs → v ∈ xs
count-pos→∈ {v = v} {[]}     ()
count-pos→∈ {v = v} {x ∷ xs} c with v ≟ x
... | yes refl = here refl
... | no  _    = there (count-pos→∈ c)

∉→count-zero : ¬ (v ∈ xs) → count v xs ≡ 0
∉→count-zero v∉ = Nat.n≤0⇒n≡0 (Nat.≮⇒≥ λ pos → v∉ (count-pos→∈ pos))

-- count is length ∘ filter (v ≟_); stdlib filter⁺ and ↭-length preserve both factors.

count≡filter-length : (v : Fin n) (xs : List (Fin n)) → count v xs ≡ length (filter (v ≟_) xs)
count≡filter-length v []       = refl
count≡filter-length v (x ∷ xs) with v ≟ x
... | yes _ = cong suc (count≡filter-length v xs)
... | no  _ = count≡filter-length v xs

↭⇒count : xs Perm.↭ ys → ∀ v → count v xs ≡ count v ys
↭⇒count {xs = xs} {ys} p v =
  trans (count≡filter-length v xs)
  (trans (PermProp.↭-length
           (Perm.↭ₛ⇒↭ (SetoidProp.filter⁺ (v ≟_) (λ x≡y v≡x → trans v≡x x≡y)
                        (Perm.↭⇒↭ₛ p))))
         (sym (count≡filter-length v ys)))

--------------------------------------------------------------------------------
-- Search bounds
--------------------------------------------------------------------------------

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

++-bnd→disjoint : ∀ {v : Fin n} (xs ys : List (Fin n))
                → count v (xs ++ ys) ≤ⁿ 1 → v ∈ xs → v ∈ ys → ⊥
++-bnd→disjoint {v = v} xs ys bnd v∈xs v∈ys =
  Nat.<-irrefl refl (Nat.<-≤-trans
    (subst (1 <ⁿ_) (sym (count-++ v xs ys))
           (Nat.+-mono-≤ (∈→count-pos v∈xs) (∈→count-pos v∈ys))) bnd)

count-++-bndˡ : (v : Fin n) (xs ys : List (Fin n)) → count v (xs ++ ys) ≤ⁿ k → count v xs ≤ⁿ k
count-++-bndˡ v xs ys bnd =
  Nat.≤-trans (Nat.≤-trans (Nat.m≤m+n _ _) (Nat.≤-reflexive (sym (count-++ v xs ys)))) bnd

count-++-bndʳ : (v : Fin n) (xs ys : List (Fin n)) → count v (xs ++ ys) ≤ⁿ k → count v ys ≤ⁿ k
count-++-bndʳ v xs ys bnd =
  Nat.≤-trans (Nat.≤-trans (Nat.m≤n+m _ _) (Nat.≤-reflexive (sym (count-++ v xs ys)))) bnd

count-concat-tabulate-≤
  : (f : Fin nE → List (Fin n)) (e : Fin nE) (v : Fin n)
  → count v (f e) ≤ⁿ count v (concat (tabulate f))
count-concat-tabulate-≤ f zero    v =
  Nat.≤-trans (Nat.m≤m+n _ _)
              (Nat.≤-reflexive (sym (count-++ v (f zero) _)))
count-concat-tabulate-≤ f (suc e) v =
  Nat.≤-trans (count-concat-tabulate-≤ (λ i → f (suc i)) e v)
              (Nat.≤-trans (Nat.m≤n+m _ _)
                           (Nat.≤-reflexive (sym (count-++ v (f zero) _))))

count-concat-tabulate-pair-≤
  : (f : Fin nE → List (Fin n)) (e e' : Fin nE) → ¬ (e ≡ e')
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

++-cancelˡ
  : ∀ (xs : List (Fin n)) {ys zs : List (Fin n)}
  → xs ++ ys Perm.↭ xs ++ zs
  → ys Perm.↭ zs
++-cancelˡ []       p = p
++-cancelˡ (x ∷ xs) p = ++-cancelˡ xs (PermProp.drop-∷ p)

--------------------------------------------------------------------------------
-- Count equality and permutations
--------------------------------------------------------------------------------
count-zero-empty : (xs : List (Fin n)) → (∀ v → count v xs ≡ 0) → xs ≡ []
count-zero-empty []       _   = refl
count-zero-empty (x ∷ xs) hyp with trans (sym (count-cons-yes x xs)) (hyp x)
... | ()

count-pos→split
  : (v : Fin n) (xs : List (Fin n))
  → 0 <ⁿ count v xs
  → Σ[ xs₁ ∈ List (Fin n) ] Σ[ xs₂ ∈ List (Fin n) ] xs ≡ xs₁ ++ v ∷ xs₂
count-pos→split v []       ()
count-pos→split v (x ∷ xs) c with v ≟ x
... | yes refl = [] , xs , refl
... | no  _    with count-pos→split v xs c
...               | xs₁ , xs₂ , refl = (x ∷ xs₁) , xs₂ , refl

count-cancel-cons
  : (v x : Fin n) (xs ys : List (Fin n))
  → count v (x ∷ xs) ≡ count v (x ∷ ys)
  → count v xs ≡ count v ys
count-cancel-cons v x xs ys h with v ≟ x
... | yes _ = Nat.suc-injective h
... | no  _ = h

count-≡⇒↭ : (xs ys : List (Fin n)) → (∀ v → count v xs ≡ count v ys) → xs Perm.↭ ys
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
  : (f : Fin n → Fin m) (xs ys : List (Fin n))
  → (∀ k → count k xs ≡ count k ys)
  → ∀ v → count v (map f xs) ≡ count v (map f ys)
count-map-resp f xs ys hyp v = ↭⇒count (PermProp.map⁺ f (count-≡⇒↭ xs ys hyp)) v

count-map-inj : (f : Fin n → Fin m) → (∀ {a b} → f a ≡ f b → a ≡ b)
              → (v : Fin n) (xs : List (Fin n)) → count (f v) (map f xs) ≡ count v xs
count-map-inj f f-inj v []       = refl
count-map-inj f f-inj v (x ∷ xs) with f v ≟ f x | v ≟ x
... | yes _ | yes _ = cong suc (count-map-inj f f-inj v xs)
... | yes p | no  q = ⊥-elim (q (f-inj p))
... | no  q | yes p = ⊥-elim (q (cong f p))
... | no  _ | no  _ = count-map-inj f f-inj v xs

count-map-miss : (f : Fin n → Fin m) {w : Fin m} → (∀ x → f x ≢ w)
               → (xs : List (Fin n)) → count w (map f xs) ≡ 0
count-map-miss f miss []       = refl
count-map-miss f {w} miss (x ∷ xs) with w ≟ f x
... | yes p = ⊥-elim (miss x (sym p))
... | no  _ = count-map-miss f miss xs

count-allFin : (v : Fin n) → count v (allFin n) ≡ 1
count-allFin {n = suc n} zero =
  trans (cong (count zero) (allFin-suc n))
        (trans (count-cons-yes zero (map suc (allFin n)))
               (cong suc (count-map-miss suc (λ _ ()) (allFin n))))
count-allFin {n = suc n} (suc i) =
  trans (cong (count (suc i)) (allFin-suc n))
        (trans (count-cons-no (suc i) zero (map suc (allFin n)) (λ ()))
               (trans (count-map-inj suc suc-injective i (allFin n)) (count-allFin i)))

--------------------------------------------------------------------------------
-- Injection counts
--------------------------------------------------------------------------------

count-map-↑ˡ : ∀ nB (i : Fin nA) (xs : List (Fin nA))
             → count (i ↑ˡ nB) (map (_↑ˡ nB) xs) ≡ count i xs
count-map-↑ˡ nB = count-map-inj (_↑ˡ nB) (↑ˡ-injective nB _ _)

count-map-↑ʳ : ∀ nA {nB} (j : Fin nB) (xs : List (Fin nB))
             → count (nA ↑ʳ j) (map (nA ↑ʳ_) xs) ≡ count j xs
count-map-↑ʳ nA = count-map-inj (nA ↑ʳ_) (↑ʳ-injective nA _ _)

count-map-↑ˡ-mismatch : ∀ nA {nB} (j : Fin nB) (xs : List (Fin nA))
                      → count (nA ↑ʳ j) (map (_↑ˡ nB) xs) ≡ 0
count-map-↑ˡ-mismatch nA {nB} j = count-map-miss (_↑ˡ nB) (λ x → ↑ˡ≢↑ʳ x j)

count-map-↑ʳ-mismatch : ∀ nB (i : Fin nA) (xs : List (Fin nB))
                      → count (i ↑ˡ nB) (map (nA ↑ʳ_) xs) ≡ 0
count-map-↑ʳ-mismatch {nA} nB i = count-map-miss (nA ↑ʳ_) (λ x q → ↑ˡ≢↑ʳ i x (sym q))

count-swap : (v : Fin n) (xs ys : List (Fin n)) → count v (xs ++ ys) ≡ count v (ys ++ xs)
count-swap v xs ys =
  trans (count-++ v xs ys)
        (trans (Nat.+-comm (count v xs) (count v ys))
               (sym (count-++ v ys xs)))
