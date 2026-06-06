{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- Linearity invariant on translated hypergraphs.
--
-- A hypergraph `H` is *linear* when every vertex's "production" count
-- (appearances in `dom ++ concat (tabulate eout)`) matches its
-- "consumption" count (appearances in `cod ++ concat (tabulate ein)`)
-- and both are at most 1.
--
-- This is the side condition under which the cospan-form decoder can
-- build a `HomTerm`: the free symmetric monoidal category has no
-- duplication or discarding, so each vertex must be produced and
-- consumed exactly once (or 0 times for *stranded* vertices that the
-- composite `hCompose` introduces — those do not show up in the
-- decoded term).
--
-- The translation `⟪ f ⟫` always satisfies linearity (`⟪⟫-Linear`),
-- by structural induction on `f` using `Linear-hTensor` / `Linear-hCompose`.
--------------------------------------------------------------------------------

open import Categories.APROP

module Categories.APROP.Hypergraph.Completeness.Linearity (sig : APROPSignature) where

open APROP sig
open import Categories.APROP.Hypergraph.Core
open import Categories.APROP.Hypergraph.FromAPROP sig
  using ( FlatGen; flatten; range; ⟪_⟫; ⟪⟫-domL; ⟪⟫-codL
        ; hEmpty; hVar; hId; hGen; hSwap; hTensor; hCompose
        ; module hTensor-impl; module hCompose-impl)

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin using (Fin; zero; suc; _↑ˡ_; _↑ʳ_; splitAt)
open import Data.Fin.Properties using
  ( _≟_; suc-injective; ↑ˡ-injective; ↑ʳ-injective
  ; splitAt-↑ˡ; splitAt-↑ʳ; splitAt⁻¹-↑ˡ; splitAt⁻¹-↑ʳ)
open import Data.List as List using (List; []; _∷_; _++_; length; map; tabulate; concat)
open import Data.List.Properties using
  ( ++-identityʳ; ++-assoc; map-++; length-map
  ; tabulate-cong; map-tabulate; concat-map; concat-++)
import Data.List.Relation.Binary.Permutation.Propositional as Perm
import Data.List.Relation.Binary.Permutation.Propositional.Properties as PermProp
import Function as Fun
open import Data.Nat using (ℕ; zero; suc; s≤s; z≤n; _+_)
open import Data.Nat as Nat using ()
import Data.Nat.Properties as Nat
open import Data.Product using (Σ-syntax; ∃-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; cong₂; sym; trans; subst; subst₂)
open import Relation.Nullary.Decidable using (Dec; yes; no)
open import Relation.Nullary.Negation using (¬_)

-- count v xs : number of occurrences of `v` in `xs`.

count : ∀ {n} → Fin n → List (Fin n) → ℕ
count v []       = 0
count v (x ∷ xs) with v ≟ x
... | yes _ = suc (count v xs)
... | no  _ = count v xs

-- count distributes over `_++_`.

count-++ : ∀ {n} (v : Fin n) (xs ys : List (Fin n))
         → count v (xs ++ ys) ≡ count v xs + count v ys
count-++ v []       ys = refl
count-++ v (x ∷ xs) ys with v ≟ x
... | yes _ = cong suc (count-++ v xs ys)
... | no  _ = count-++ v xs ys

-- count of `v` in `range n`: every Fin appears exactly once.

private
  count-zero-map-suc : ∀ {n} (xs : List (Fin n))
                     → count (zero {n = n}) (map suc xs) ≡ 0
  count-zero-map-suc []       = refl
  count-zero-map-suc (x ∷ xs) with zero {n = _} ≟ suc x
  ... | no  _ = count-zero-map-suc xs

  count-suc-map-suc : ∀ {n} (i : Fin n) (xs : List (Fin n))
                    → count (suc i) (map suc xs) ≡ count i xs
  count-suc-map-suc i []       = refl
  count-suc-map-suc i (x ∷ xs) with suc i ≟ suc x | i ≟ x
  ... | yes _ | yes _ = cong suc (count-suc-map-suc i xs)
  ... | yes p | no  q = ⊥-elim (q (suc-injective p))
  ... | no  q | yes p = ⊥-elim (q (cong suc p))
  ... | no  _ | no  _ = count-suc-map-suc i xs

count-range : ∀ {n} (v : Fin n) → count v (range n) ≡ 1
count-range {n = suc n} zero    with zero {n = n} ≟ zero
... | yes _ = cong suc (count-zero-map-suc {n = n} (range n))
... | no  q = ⊥-elim (q refl)
count-range {n = suc n} (suc i) with suc i ≟ zero
... | no  _ = trans (count-suc-map-suc i (range n)) (count-range i)

--------------------------------------------------------------------------------
-- Counting along the disjoint injections `_↑ˡ_` and `_↑ʳ_`.

-- The "matching" cases.
count-map-↑ˡ : ∀ {nA} nB (i : Fin nA) (xs : List (Fin nA))
             → count (i ↑ˡ nB) (map (_↑ˡ nB) xs) ≡ count i xs
count-map-↑ˡ nB i []       = refl
count-map-↑ˡ nB i (x ∷ xs) with (i ↑ˡ nB) ≟ (x ↑ˡ nB) | i ≟ x
... | yes _ | yes _ = cong suc (count-map-↑ˡ nB i xs)
... | yes p | no  q = ⊥-elim (q (↑ˡ-injective nB i x p))
... | no  q | yes p = ⊥-elim (q (cong (_↑ˡ nB) p))
... | no  _ | no  _ = count-map-↑ˡ nB i xs

count-map-↑ʳ : ∀ nA {nB} (j : Fin nB) (xs : List (Fin nB))
             → count (nA ↑ʳ j) (map (nA ↑ʳ_) xs) ≡ count j xs
count-map-↑ʳ nA j []       = refl
count-map-↑ʳ nA j (x ∷ xs) with (nA ↑ʳ j) ≟ (nA ↑ʳ x) | j ≟ x
... | yes _ | yes _ = cong suc (count-map-↑ʳ nA j xs)
... | yes p | no  q = ⊥-elim (q (↑ʳ-injective nA j x p))
... | no  q | yes p = ⊥-elim (q (cong (nA ↑ʳ_) p))
... | no  _ | no  _ = count-map-↑ʳ nA j xs

-- The "mismatch" cases: a `nA ↑ʳ j` never appears in an `_↑ˡ_` image,
-- and vice versa.

private
  ↑ˡ≢↑ʳ : ∀ {nA nB} (i : Fin nA) (j : Fin nB) → i ↑ˡ nB ≡ nA ↑ʳ j → ⊥
  ↑ˡ≢↑ʳ {nA} {nB} i j p
    with trans (sym (splitAt-↑ˡ nA i nB))
               (trans (cong (splitAt nA) p) (splitAt-↑ʳ nA nB j))
  ... | ()

count-map-↑ˡ-mismatch : ∀ nA {nB} (j : Fin nB) (xs : List (Fin nA))
                      → count (nA ↑ʳ j) (map (_↑ˡ nB) xs) ≡ 0
count-map-↑ˡ-mismatch nA j []       = refl
count-map-↑ˡ-mismatch nA {nB} j (x ∷ xs) with (nA ↑ʳ j) ≟ (x ↑ˡ nB)
... | yes p = ⊥-elim (↑ˡ≢↑ʳ x j (sym p))
... | no  _ = count-map-↑ˡ-mismatch nA j xs

count-map-↑ʳ-mismatch : ∀ {nA} nB (i : Fin nA) (xs : List (Fin nB))
                      → count (i ↑ˡ nB) (map (nA ↑ʳ_) xs) ≡ 0
count-map-↑ʳ-mismatch nB i []       = refl
count-map-↑ʳ-mismatch {nA} nB i (x ∷ xs) with (i ↑ˡ nB) ≟ (nA ↑ʳ x)
... | yes p = ⊥-elim (↑ˡ≢↑ʳ i x p)
... | no  _ = count-map-↑ʳ-mismatch nB i xs

-- count is invariant under swapping the two sides of a `_++_`.

count-swap : ∀ {n} (v : Fin n) (xs ys : List (Fin n))
           → count v (xs ++ ys) ≡ count v (ys ++ xs)
count-swap v xs ys =
  trans (count-++ v xs ys)
        (trans (Nat.+-comm (count v xs) (count v ys))
               (sym (count-++ v ys xs)))

-- `tabulate` over `Fin (m + n)` splits along the `↑ˡ`/`↑ʳ` boundary.

private
  tabulate-+ : ∀ {m n} {A : Set} (f : Fin (m + n) → A)
             → tabulate f
             ≡ tabulate (λ i → f (i ↑ˡ n)) ++ tabulate (λ j → f (m ↑ʳ j))
  tabulate-+ {m = zero}              f = refl
  tabulate-+ {m = suc m} {n = n}     f = cong (f zero ∷_) (tabulate-+ {m = m} {n = n} (f Fun.∘ suc))

-- The combined `LL ++ RR` list contains every Fin (nA + nB) exactly once.

private
  count-LL-RR-eq-1
    : ∀ (nA nB : ℕ) (v : Fin (nA + nB))
    → count v (map (_↑ˡ nB) (range nA) ++ map (nA ↑ʳ_) (range nB)) ≡ 1
  count-LL-RR-eq-1 nA nB v with splitAt nA v in eq
  ... | inj₁ i with splitAt⁻¹-↑ˡ {n = nB} eq
  ...           | refl =
                  trans (count-++ (i ↑ˡ nB)
                                  (map (_↑ˡ nB) (range nA))
                                  (map (nA ↑ʳ_) (range nB)))
                        (cong₂ Nat._+_
                          (trans (count-map-↑ˡ nB i (range nA)) (count-range i))
                          (count-map-↑ʳ-mismatch nB i (range nB)))
  count-LL-RR-eq-1 nA nB v | inj₂ j with splitAt⁻¹-↑ʳ {m = nA} eq
  ...                                  | refl =
                                          trans (count-++ (nA ↑ʳ j)
                                                          (map (_↑ˡ nB) (range nA))
                                                          (map (nA ↑ʳ_) (range nB)))
                                                (cong₂ Nat._+_
                                                  (count-map-↑ˡ-mismatch nA j (range nA))
                                                  (trans (count-map-↑ʳ nA j (range nB)) (count-range j)))

-- Production / consumption lists of a hypergraph.

producedList : (H : Hypergraph FlatGen) → List (Fin (Hypergraph.nV H))
producedList H =
  Hypergraph.dom H ++ concat (tabulate (Hypergraph.eout H))

consumedList : (H : Hypergraph FlatGen) → List (Fin (Hypergraph.nV H))
consumedList H =
  Hypergraph.cod H ++ concat (tabulate (Hypergraph.ein H))

-- Linearity: matching production / consumption counts, each ≤ 1.

Linear : Hypergraph FlatGen → Set
Linear H = (∀ v → count v (producedList H) ≡ count v (consumedList H))
         × (∀ v → count v (producedList H) Nat.≤ 1)

--------------------------------------------------------------------------------
-- Tensor preserves linearity.
--
-- For `v = injL i`, `count v ≡ count i` on G's lists; for `v = injR j`,
-- `count v ≡ count j` on K's lists.  Both sides match by `Linear G`/
-- `Linear K`, and the bound transfers.

Linear-hTensor
  : (G K : Hypergraph FlatGen)
  → Linear G → Linear K
  → Linear (hTensor G K)
Linear-hTensor G K (G-bal , G-bnd) (K-bal , K-bnd) = balance , bound
  where
    module G = Hypergraph G
    module K = Hypergraph K
    open hTensor-impl G K

    -- Decompose `concat (tabulate {ein,eout}-c)` into the L/R-side blocks.

    eout-tensor-eq
      : concat (tabulate eout-c)
      ≡ map injL (concat (tabulate G.eout))
        ++ map injR (concat (tabulate K.eout))
    eout-tensor-eq =
      trans (cong concat (tabulate-+ {m = G.nE} {n = K.nE} eout-c))
      (trans (cong concat
                (cong₂ _++_
                   (trans (tabulate-cong eout-c-inj₁-red)
                          (sym (map-tabulate G.eout (map injL))))
                   (trans (tabulate-cong eout-c-inj₂-red)
                          (sym (map-tabulate K.eout (map injR))))))
      (trans (sym (concat-++ (map (map injL) (tabulate G.eout))
                              (map (map injR) (tabulate K.eout))))
             (cong₂ _++_ (concat-map (tabulate G.eout))
                         (concat-map (tabulate K.eout)))))

    ein-tensor-eq
      : concat (tabulate ein-c)
      ≡ map injL (concat (tabulate G.ein))
        ++ map injR (concat (tabulate K.ein))
    ein-tensor-eq =
      trans (cong concat (tabulate-+ {m = G.nE} {n = K.nE} ein-c))
      (trans (cong concat
                (cong₂ _++_
                   (trans (tabulate-cong ein-c-inj₁-red)
                          (sym (map-tabulate G.ein (map injL))))
                   (trans (tabulate-cong ein-c-inj₂-red)
                          (sym (map-tabulate K.ein (map injR))))))
      (trans (sym (concat-++ (map (map injL) (tabulate G.ein))
                              (map (map injR) (tabulate K.ein))))
             (cong₂ _++_ (concat-map (tabulate G.ein))
                         (concat-map (tabulate K.ein)))))

    count-injL-mixed
      : ∀ (i : Fin G.nV) (xs : List (Fin G.nV)) (ys : List (Fin K.nV))
      → count (injL i) (map injL xs ++ map injR ys) ≡ count i xs
    count-injL-mixed i xs ys =
      trans (count-++ (injL i) (map injL xs) (map injR ys))
      (trans (cong₂ Nat._+_
                (count-map-↑ˡ K.nV i xs)
                (count-map-↑ʳ-mismatch K.nV i ys))
             (Nat.+-identityʳ (count i xs)))

    count-injR-mixed
      : ∀ (j : Fin K.nV) (xs : List (Fin G.nV)) (ys : List (Fin K.nV))
      → count (injR j) (map injL xs ++ map injR ys) ≡ count j ys
    count-injR-mixed j xs ys =
      trans (count-++ (injR j) (map injL xs) (map injR ys))
            (cong₂ Nat._+_
              (count-map-↑ˡ-mismatch G.nV j xs)
              (count-map-↑ʳ G.nV j ys))

    -- `count (injL i)` of the composite's lists equals `count i` of G's;
    -- `count (injR j)` equals `count j` of K's.

    count-injL-prod
      : ∀ (i : Fin G.nV)
      → count (injL i) (producedList (hTensor G K)) ≡ count i (producedList G)
    count-injL-prod i =
      trans (count-++ (injL i)
                       (map injL G.dom ++ map injR K.dom)
                       (concat (tabulate eout-c)))
      (trans (cong₂ Nat._+_
                (count-injL-mixed i G.dom K.dom)
                (trans (cong (count (injL i)) eout-tensor-eq)
                       (count-injL-mixed i (concat (tabulate G.eout))
                                            (concat (tabulate K.eout)))))
             (sym (count-++ i G.dom (concat (tabulate G.eout)))))

    count-injL-cons
      : ∀ (i : Fin G.nV)
      → count (injL i) (consumedList (hTensor G K)) ≡ count i (consumedList G)
    count-injL-cons i =
      trans (count-++ (injL i)
                       (map injL G.cod ++ map injR K.cod)
                       (concat (tabulate ein-c)))
      (trans (cong₂ Nat._+_
                (count-injL-mixed i G.cod K.cod)
                (trans (cong (count (injL i)) ein-tensor-eq)
                       (count-injL-mixed i (concat (tabulate G.ein))
                                            (concat (tabulate K.ein)))))
             (sym (count-++ i G.cod (concat (tabulate G.ein)))))

    count-injR-prod
      : ∀ (j : Fin K.nV)
      → count (injR j) (producedList (hTensor G K)) ≡ count j (producedList K)
    count-injR-prod j =
      trans (count-++ (injR j)
                       (map injL G.dom ++ map injR K.dom)
                       (concat (tabulate eout-c)))
      (trans (cong₂ Nat._+_
                (count-injR-mixed j G.dom K.dom)
                (trans (cong (count (injR j)) eout-tensor-eq)
                       (count-injR-mixed j (concat (tabulate G.eout))
                                            (concat (tabulate K.eout)))))
             (sym (count-++ j K.dom (concat (tabulate K.eout)))))

    count-injR-cons
      : ∀ (j : Fin K.nV)
      → count (injR j) (consumedList (hTensor G K)) ≡ count j (consumedList K)
    count-injR-cons j =
      trans (count-++ (injR j)
                       (map injL G.cod ++ map injR K.cod)
                       (concat (tabulate ein-c)))
      (trans (cong₂ Nat._+_
                (count-injR-mixed j G.cod K.cod)
                (trans (cong (count (injR j)) ein-tensor-eq)
                       (count-injR-mixed j (concat (tabulate G.ein))
                                            (concat (tabulate K.ein)))))
             (sym (count-++ j K.cod (concat (tabulate K.ein)))))

    balance : ∀ v → count v (producedList (hTensor G K))
                  ≡ count v (consumedList (hTensor G K))
    balance v with splitAt G.nV v in eq
    ... | inj₁ i with splitAt⁻¹-↑ˡ {n = K.nV} eq
    ...           | refl =
                    trans (count-injL-prod i)
                          (trans (G-bal i) (sym (count-injL-cons i)))
    balance v | inj₂ j with splitAt⁻¹-↑ʳ {m = G.nV} eq
    ...                  | refl =
                           trans (count-injR-prod j)
                                 (trans (K-bal j) (sym (count-injR-cons j)))

    bound : ∀ v → count v (producedList (hTensor G K)) Nat.≤ 1
    bound v with splitAt G.nV v in eq
    ... | inj₁ i with splitAt⁻¹-↑ˡ {n = K.nV} eq
    ...           | refl rewrite count-injL-prod i = G-bnd i
    bound v | inj₂ j with splitAt⁻¹-↑ʳ {m = G.nV} eq
    ...                | refl rewrite count-injR-prod j = K-bnd j

--------------------------------------------------------------------------------
-- Helpers for `Linear-hCompose`: count manipulation and the
-- count ↔ permutation correspondence.

private
  count-cons-yes : ∀ {n} (v : Fin n) (xs : List (Fin n))
                 → count v (v ∷ xs) ≡ suc (count v xs)
  count-cons-yes v xs with v ≟ v
  ... | yes _ = refl
  ... | no  q = ⊥-elim (q refl)

  count-cons-no : ∀ {n} (v x : Fin n) (xs : List (Fin n))
                → ¬ (v ≡ x)
                → count v (x ∷ xs) ≡ count v xs
  count-cons-no v x xs v≢x with v ≟ x
  ... | yes p = ⊥-elim (v≢x p)
  ... | no  _ = refl

  -- count is monotone under prepending a head.
  count-mono-cons : ∀ {n} (v x : Fin n) (xs : List (Fin n))
                  → count v xs Nat.≤ count v (x ∷ xs)
  count-mono-cons v x xs with v ≟ x
  ... | yes _ = Nat.n≤1+n (count v xs)
  ... | no  _ = Nat.≤-refl

  -- all counts zero iff `xs ≡ []`.
  count-zero-empty : ∀ {n} (xs : List (Fin n))
                   → (∀ v → count v xs ≡ 0)
                   → xs ≡ []
  count-zero-empty []       _   = refl
  count-zero-empty (x ∷ xs) hyp
    with trans (sym (count-cons-yes x xs)) (hyp x)
  ... | ()

  -- Decompose a list with positive count: `xs ≡ xs₁ ++ v ∷ xs₂`.
  count-pos→split
    : ∀ {n} (v : Fin n) (xs : List (Fin n))
    → 0 Nat.< count v xs
    → Σ[ xs₁ ∈ List (Fin n) ] Σ[ xs₂ ∈ List (Fin n) ] xs ≡ xs₁ ++ v ∷ xs₂
  count-pos→split v []       ()
  count-pos→split v (x ∷ xs) c with v ≟ x
  ... | yes refl = [] , xs , refl
  ... | no  _    with count-pos→split v xs c
  ...               | xs₁ , xs₂ , refl = (x ∷ xs₁) , xs₂ , refl

  -- Permutation preserves count.
  ↭⇒count-≡
    : ∀ {n} {xs ys : List (Fin n)}
    → xs Perm.↭ ys → ∀ v → count v xs ≡ count v ys
  ↭⇒count-≡ Perm.refl              v = refl
  ↭⇒count-≡ (Perm.prep x p)        v with v ≟ x
  ... | yes _ = cong suc (↭⇒count-≡ p v)
  ... | no  _ = ↭⇒count-≡ p v
  ↭⇒count-≡ (Perm.swap {xs = xs'} {ys = ys'} x y p) v =
    swap-case (v ≟ x) (v ≟ y)
    where
      swap-case : Dec (v ≡ x) → Dec (v ≡ y)
                → count v (x ∷ y ∷ xs') ≡ count v (y ∷ x ∷ ys')
      swap-case (yes refl) (yes refl) =
        trans (count-cons-yes v (v ∷ xs'))
        (trans (cong suc (count-cons-yes v xs'))
        (trans (cong suc (cong suc (↭⇒count-≡ p v)))
        (trans (cong suc (sym (count-cons-yes v ys')))
               (sym (count-cons-yes v (v ∷ ys'))))))
      swap-case (yes refl) (no  q) =
        trans (count-cons-yes v (y ∷ xs'))
        (trans (cong suc (count-cons-no v y xs' q))
        (trans (cong suc (↭⇒count-≡ p v))
        (trans (sym (count-cons-yes v ys'))
               (sym (count-cons-no v y (v ∷ ys') q)))))
      swap-case (no  q) (yes refl) =
        trans (count-cons-no v x (v ∷ xs') q)
        (trans (count-cons-yes v xs')
        (trans (cong suc (↭⇒count-≡ p v))
        (trans (cong suc (sym (count-cons-no v x ys' q)))
               (sym (count-cons-yes v (x ∷ ys'))))))
      swap-case (no  q₁) (no  q₂) =
        trans (count-cons-no v x (y ∷ xs') q₁)
        (trans (count-cons-no v y xs' q₂)
        (trans (↭⇒count-≡ p v)
        (trans (sym (count-cons-no v x ys' q₁))
               (sym (count-cons-no v y (x ∷ ys') q₂)))))
  ↭⇒count-≡ (Perm.trans p₁ p₂)     v = trans (↭⇒count-≡ p₁ v) (↭⇒count-≡ p₂ v)

  -- Cancel a shared cons in a count equality.
  count-cancel-cons
    : ∀ {n} (v x : Fin n) (xs ys : List (Fin n))
    → count v (x ∷ xs) ≡ count v (x ∷ ys)
    → count v xs ≡ count v ys
  count-cancel-cons v x xs ys h with v ≟ x
  ... | yes _ = Nat.suc-injective h
  ... | no  _ = h

  -- Count equality lifts to a permutation.
  count-≡⇒↭
    : ∀ {n} (xs ys : List (Fin n))
    → (∀ v → count v xs ≡ count v ys)
    → xs Perm.↭ ys
  count-≡⇒↭ []       ys hyp
    rewrite count-zero-empty ys (λ k → sym (hyp k)) = Perm.refl
  count-≡⇒↭ (x ∷ xs) ys hyp
    with count-pos→split x ys
           (subst (0 Nat.<_) (trans (sym (count-cons-yes x xs)) (hyp x))
                  (s≤s z≤n))
  ... | ys₁ , ys₂ , refl =
        Perm.trans (Perm.prep x (count-≡⇒↭ xs (ys₁ ++ ys₂) sub-hyp))
                   (Perm.↭-sym (PermProp.shift x ys₁ ys₂))
        where
          -- After splitting `ys = ys₁ ++ x ∷ ys₂`, count-equality on
          -- `x ∷ xs ≡ ys₁ ++ x ∷ ys₂` rearranges to count-equality on
          -- `xs ≡ ys₁ ++ ys₂` by going through the shift permutation.
          sub-hyp : ∀ v → count v xs ≡ count v (ys₁ ++ ys₂)
          sub-hyp v = count-cancel-cons v x xs (ys₁ ++ ys₂)
                        (trans (hyp v)
                               (↭⇒count-≡ (PermProp.shift x ys₁ ys₂) v))

  count-map-resp
    : ∀ {n m} (f : Fin n → Fin m) (xs ys : List (Fin n))
    → (∀ k → count k xs ≡ count k ys)
    → ∀ v → count v (map f xs) ≡ count v (map f ys)
  count-map-resp f xs ys hyp v =
    ↭⇒count-≡ (PermProp.map⁺ f (count-≡⇒↭ xs ys hyp)) v

--------------------------------------------------------------------------------
-- `Linear-hCompose`.  The vertices of `hCompose G K` are
-- `Fin (G.nV + K.nV)`; the boundary identification lives in `remap`,
-- which sends each `K.dom`-vertex to the corresponding `G.cod`-vertex on
-- the L-side, and leaves "non-domain" K-vertices untouched on the R-side.
--
-- K-balance (a count-equality) lifts via `map⁺` on `_↭_` to a
-- count-equality of the `map remap`-images.  Combined with G-balance and
-- `map remap K.dom ≡ map injL G.cod`, this yields the balance equation;
-- the bound reduces to G-bound (L-side) and K-bound (R-side).

--------------------------------------------------------------------------------
-- Combinatorial core of the K-side `remap` routing, shared by both
-- `Linear-hCompose`'s where-block and `hCompose-Linear-utils`.  Depends
-- only on `G`, `K`, the boundary equation, and the generic `count`
-- lemmas — NOT on `Linear G` / `Linear K`.  The duplicate-freeness bound
-- `count k K.dom ≤ 1` is Linearity-dependent and so is passed in as a
-- parameter (see `map-remap-K-dom-from-bnd`).

private
  module remap-core
    (G K : Hypergraph FlatGen) (bdy-eq : codL G ≡ domL K)
    where
    private
      module G = Hypergraph G
      module K = Hypergraph K
    open hCompose-impl G K bdy-eq

    -- For `k ∉ K.dom`, `remap k ≡ injR k` (the recursion exhausts `K.dom`).
    private-remap-noDom
      : ∀ (ks : List (Fin K.nV)) (gs : List (Fin G.nV)) (k : Fin K.nV)
      → count k ks ≡ 0
      → remap' ks gs k ≡ injR k
    private-remap-noDom []        _         k _ = refl
    private-remap-noDom (_ ∷ _)   []        k _ = refl
    private-remap-noDom (k' ∷ ks) (g ∷ gs)  k c with k ≟ k'
    ... | no q = private-remap-noDom ks gs k c
    ... | yes refl with c
    ...               | ()

    remap-noDom : ∀ k → count k K.dom ≡ 0 → remap k ≡ injR k
    remap-noDom = private-remap-noDom K.dom G.cod

    length-K-dom : length K.dom ≡ length G.cod
    length-K-dom =
      trans (sym (length-map K.vlab K.dom))
      (trans (cong length (sym bdy-eq))
             (length-map G.vlab G.cod))

    -- For dup-free `ks` (length-matched to `gs`),
    -- `map (remap' ks gs) ks ≡ map injL gs`.
    private-map-remap-on-self
      : ∀ (ks : List (Fin K.nV)) (gs : List (Fin G.nV))
      → length ks ≡ length gs
      → (∀ k → count k ks Nat.≤ 1)
      → map (remap' ks gs) ks ≡ map injL gs
    private-map-remap-on-self []        []         _   _     = refl
    private-map-remap-on-self []        (_ ∷ _)    () _
    private-map-remap-on-self (_ ∷ _)   []         () _
    private-map-remap-on-self (k ∷ ks)  (g ∷ gs)   len bnd =
      cong₂ _∷_ head-eq (trans shift-tail rest-eq)
      where
        head-eq : remap' (k ∷ ks) (g ∷ gs) k ≡ injL g
        head-eq with k ≟ k
        ... | yes _ = refl
        ... | no  q = ⊥-elim (q refl)

        k-not-in-ks : count k ks ≡ 0
        k-not-in-ks =
          Nat.≤-antisym
            (Nat.s≤s⁻¹
              (Nat.≤-trans (Nat.≤-reflexive (sym (count-cons-yes k ks)))
                           (bnd k)))
            z≤n

        shift-step
          : ∀ (xs : List (Fin K.nV))
          → count k xs ≡ 0
          → map (remap' (k ∷ ks) (g ∷ gs)) xs ≡ map (remap' ks gs) xs
        shift-step []        _ = refl
        shift-step (x ∷ xs)  c with k ≟ x
        ... | no q = cong₂ _∷_ shift-head (shift-step xs c)
          where
            shift-head : remap' (k ∷ ks) (g ∷ gs) x ≡ remap' ks gs x
            shift-head with x ≟ k
            ... | yes p = ⊥-elim (q (sym p))
            ... | no  _ = refl
        ... | yes refl with c
        ...               | ()

        shift-tail : map (remap' (k ∷ ks) (g ∷ gs)) ks ≡ map (remap' ks gs) ks
        shift-tail = shift-step ks k-not-in-ks

        bnd-ks : ∀ k' → count k' ks Nat.≤ 1
        bnd-ks k' = Nat.≤-trans (count-mono-cons k' k ks) (bnd k')

        rest-eq : map (remap' ks gs) ks ≡ map injL gs
        rest-eq = private-map-remap-on-self ks gs (Nat.suc-injective len) bnd-ks

    map-remap-K-dom-from-bnd
      : (∀ k → count k K.dom Nat.≤ 1) → map remap K.dom ≡ map injL G.cod
    map-remap-K-dom-from-bnd bnd =
      private-map-remap-on-self K.dom G.cod length-K-dom bnd

Linear-hCompose
  : (G K : Hypergraph FlatGen) (bdy-eq : codL G ≡ domL K)
  → Linear G → Linear K
  → Linear (hCompose G K bdy-eq)
Linear-hCompose G K bdy-eq (G-bal , G-bnd) (K-bal , K-bnd) =
  balance , bound
  where
    module G = Hypergraph G
    module K = Hypergraph K
    open hCompose-impl G K bdy-eq

    G-eb    = concat (tabulate G.eout)
    G-ein-b = concat (tabulate G.ein)
    K-eb    = concat (tabulate K.eout)
    K-ein-b = concat (tabulate K.ein)

    -- Decompositions as in `Linear-hTensor`, but the K-side uses
    -- `remap` instead of `injR`.

    eout-comp-eq
      : concat (tabulate eout-c)
      ≡ map injL G-eb ++ map remap K-eb
    eout-comp-eq =
      trans (cong concat (tabulate-+ {m = G.nE} {n = K.nE} eout-c))
      (trans (cong concat
                (cong₂ _++_
                   (trans (tabulate-cong eout-c-inj₁-red)
                          (sym (map-tabulate G.eout (map injL))))
                   (trans (tabulate-cong eout-c-inj₂-red)
                          (sym (map-tabulate K.eout (map remap))))))
      (trans (sym (concat-++ (map (map injL) (tabulate G.eout))
                              (map (map remap) (tabulate K.eout))))
             (cong₂ _++_ (concat-map (tabulate G.eout))
                         (concat-map (tabulate K.eout)))))

    ein-comp-eq
      : concat (tabulate ein-c)
      ≡ map injL G-ein-b ++ map remap K-ein-b
    ein-comp-eq =
      trans (cong concat (tabulate-+ {m = G.nE} {n = K.nE} ein-c))
      (trans (cong concat
                (cong₂ _++_
                   (trans (tabulate-cong ein-c-inj₁-red)
                          (sym (map-tabulate G.ein (map injL))))
                   (trans (tabulate-cong ein-c-inj₂-red)
                          (sym (map-tabulate K.ein (map remap))))))
      (trans (sym (concat-++ (map (map injL) (tabulate G.ein))
                              (map (map remap) (tabulate K.ein))))
             (cong₂ _++_ (concat-map (tabulate G.ein))
                         (concat-map (tabulate K.ein)))))

    -- K's domain is duplicate-free, a corollary of the K-bound since
    -- count k K.dom ≤ count k (K.dom ++ K-eb) = count k K.producedList.

    K-dom-bnd : ∀ k → count k K.dom Nat.≤ 1
    K-dom-bnd k =
      Nat.≤-trans
        (Nat.≤-trans (Nat.m≤m+n (count k K.dom) _)
                     (Nat.≤-reflexive (sym (count-++ k K.dom K-eb))))
        (K-bnd k)

    open remap-core G K bdy-eq

    map-remap-K-dom : map remap K.dom ≡ map injL G.cod
    map-remap-K-dom = map-remap-K-dom-from-bnd K-dom-bnd

    -- count v (map remap S) for the special K-side lists.

    count-map-remap-K-dom-injL
      : ∀ (i : Fin G.nV) → count (injL i) (map remap K.dom) ≡ count i G.cod
    count-map-remap-K-dom-injL i =
      trans (cong (count (injL i)) map-remap-K-dom)
            (count-map-↑ˡ K.nV i G.cod)

    count-map-remap-K-dom-injR
      : ∀ (j : Fin K.nV) → count (injR j) (map remap K.dom) ≡ 0
    count-map-remap-K-dom-injR j =
      trans (cong (count (injR j)) map-remap-K-dom)
            (count-map-↑ˡ-mismatch G.nV j G.cod)

    -- For `k ∈ K-eb`, `count k K.dom ≡ 0` by K-bnd; hence each element
    -- of K-eb is mapped by `remap` to `injR`.

    K-eb-noDom : ∀ k → 0 Nat.< count k K-eb → count k K.dom ≡ 0
    K-eb-noDom k pos = Nat.≤-antisym le-0 z≤n
      where
        prod-bnd : count k K.dom + count k K-eb Nat.≤ 1
        prod-bnd = subst (Nat._≤ 1) (count-++ k K.dom K-eb) (K-bnd k)

        step : count k K.dom + 1 Nat.≤ 1
        step =
          Nat.≤-trans
            (Nat.+-monoʳ-≤ (count k K.dom) pos)
            prod-bnd

        le-0 : count k K.dom Nat.≤ 0
        le-0 = Nat.+-cancelʳ-≤ 1 (count k K.dom) 0 step

    map-remap-eb : map remap K-eb ≡ map injR K-eb
    map-remap-eb = go K-eb (λ _ p → p)
      where
        go : ∀ (xs : List (Fin K.nV))
           → (∀ k → 0 Nat.< count k xs → 0 Nat.< count k K-eb)
           → map remap xs ≡ map injR xs
        go []       _   = refl
        go (x ∷ xs) sub =
          cong₂ _∷_
            (remap-noDom x (K-eb-noDom x (sub x x∈x∷xs)))
            (go xs (λ k p → sub k (Nat.≤-trans p (count-mono-cons k x xs))))
          where
            x∈x∷xs : 0 Nat.< count x (x ∷ xs)
            x∈x∷xs = subst (0 Nat.<_) (sym (count-cons-yes x xs)) (s≤s z≤n)

    -- count of `injL i` / `injR j` in `map injL xs ++ map remap S`.

    count-injL-mixed-remap
      : ∀ (i : Fin G.nV) (xs : List (Fin G.nV)) (ys : List (Fin K.nV))
      → count (injL i) (map injL xs ++ map remap ys)
      ≡ count i xs + count (injL i) (map remap ys)
    count-injL-mixed-remap i xs ys =
      trans (count-++ (injL i) (map injL xs) (map remap ys))
            (cong (Nat._+ count (injL i) (map remap ys))
                  (count-map-↑ˡ K.nV i xs))

    count-injR-mixed-remap
      : ∀ (j : Fin K.nV) (xs : List (Fin G.nV)) (ys : List (Fin K.nV))
      → count (injR j) (map injL xs ++ map remap ys)
      ≡ count (injR j) (map remap ys)
    count-injR-mixed-remap j xs ys =
      trans (count-++ (injR j) (map injL xs) (map remap ys))
            (cong (Nat._+ count (injR j) (map remap ys))
                  (count-map-↑ˡ-mismatch G.nV j xs))

    -- K-bal lifted via `remap`: the K-side count-equality survives
    -- applying `remap` pointwise.

    K-bal-via-remap
      : ∀ v
      → count v (map remap (K.dom ++ K-eb))
      ≡ count v (map remap (K.cod ++ K-ein-b))
    K-bal-via-remap v =
      count-map-resp remap (K.dom ++ K-eb) (K.cod ++ K-ein-b) K-bal v

    -- producedList/consumedList counts decomposed into G-side and
    -- K-side contributions (labelled by `injL` resp. `remap`).

    count-prod
      : ∀ v
      → count v (producedList (hCompose G K bdy-eq))
      ≡ count v (map injL G.dom)
      + count v (map injL G-eb)
      + count v (map remap K-eb)
    count-prod v =
      trans (count-++ v (map injL G.dom) (concat (tabulate eout-c)))
      (trans (cong (count v (map injL G.dom) Nat.+_)
                   (trans (cong (count v) eout-comp-eq)
                          (trans (count-++ v (map injL G-eb) (map remap K-eb))
                                 refl)))
             (sym (Nat.+-assoc (count v (map injL G.dom)) _ _)))

    count-cons
      : ∀ v
      → count v (consumedList (hCompose G K bdy-eq))
      ≡ count v (map remap K.cod)
      + count v (map injL G-ein-b)
      + count v (map remap K-ein-b)
    count-cons v =
      trans (count-++ v (map remap K.cod) (concat (tabulate ein-c)))
      (trans (cong (count v (map remap K.cod) Nat.+_)
                   (trans (cong (count v) ein-comp-eq)
                          (trans (count-++ v (map injL G-ein-b) (map remap K-ein-b))
                                 refl)))
             (sym (Nat.+-assoc (count v (map remap K.cod)) _ _)))

    -- The balance identity combining G-bal with the
    -- `map-remap-K-dom = map injL G.cod` characterisation of the cospan.
    -- For v = injL i: count v (map injL G.dom) + count v (map injL G-eb)
    --                ≡ count v (map injL G-ein-b) + count v (map remap K.dom).
    -- For v = injR j: both sides are 0.
    αβ≡εη
      : ∀ v
      → count v (map injL G.dom) + count v (map injL G-eb)
      ≡ count v (map injL G-ein-b) + count v (map remap K.dom)
    αβ≡εη v with splitAt G.nV v in eq
    ... | inj₁ i with splitAt⁻¹-↑ˡ {n = K.nV} eq
    ...           | refl =
                    trans (cong₂ Nat._+_
                            (count-map-↑ˡ K.nV i G.dom)
                            (count-map-↑ˡ K.nV i G-eb))
                    (trans (sym (count-++ i G.dom G-eb))
                    (trans (G-bal i)
                    (trans (count-swap i G.cod G-ein-b)
                    (trans (count-++ i G-ein-b G.cod)
                           (cong₂ Nat._+_
                             (sym (count-map-↑ˡ K.nV i G-ein-b))
                             (sym (count-map-remap-K-dom-injL i)))))))
    αβ≡εη v | inj₂ j with splitAt⁻¹-↑ʳ {m = G.nV} eq
    ...                | refl =
                         trans (cong₂ Nat._+_
                                 (count-map-↑ˡ-mismatch G.nV j G.dom)
                                 (count-map-↑ˡ-mismatch G.nV j G-eb))
                         (sym (cong₂ Nat._+_
                                 (count-map-↑ˡ-mismatch G.nV j G-ein-b)
                                 (count-map-remap-K-dom-injR j)))

    balance : ∀ v → count v (producedList (hCompose G K bdy-eq))
                  ≡ count v (consumedList (hCompose G K bdy-eq))
    balance v =
      trans (count-prod v)
      (trans (cong (Nat._+ γ) (αβ≡εη v))
      (trans (Nat.+-assoc ε η γ)
      (trans (cong (ε Nat.+_)
                   (trans (sym (count-++ v (map remap K.dom) (map remap K-eb)))
                   (trans (sym (cong (count v) (map-++ remap K.dom K-eb)))
                   (trans (K-bal-via-remap v)
                   (trans (cong (count v) (map-++ remap K.cod K-ein-b))
                          (count-++ v (map remap K.cod) (map remap K-ein-b)))))))
      (trans (sym (Nat.+-assoc ε δ ζ))
      (trans (cong (Nat._+ ζ) (Nat.+-comm ε δ))
             (sym (count-cons v)))))))
      where
        α = count v (map injL G.dom)
        β = count v (map injL G-eb)
        γ = count v (map remap K-eb)
        δ = count v (map remap K.cod)
        ε = count v (map injL G-ein-b)
        ζ = count v (map remap K-ein-b)
        η = count v (map remap K.dom)

    -- Bound: case-split on `v` and use G-bnd / K-bnd.

    -- `count (injL i) (map remap K-eb) ≡ 0`: each element of K-eb is
    -- injR'd by `remap`, and injR i ≠ injL anything.
    count-injL-remap-K-eb-zero
      : ∀ (i : Fin G.nV) → count (injL i) (map remap K-eb) ≡ 0
    count-injL-remap-K-eb-zero i =
      trans (cong (count (injL i)) map-remap-eb)
            (count-map-↑ʳ-mismatch K.nV i K-eb)

    count-injR-remap-K-eb
      : ∀ (j : Fin K.nV) → count (injR j) (map remap K-eb) ≡ count j K-eb
    count-injR-remap-K-eb j =
      trans (cong (count (injR j)) map-remap-eb)
            (count-map-↑ʳ G.nV j K-eb)

    bound : ∀ v → count v (producedList (hCompose G K bdy-eq)) Nat.≤ 1
    bound v with splitAt G.nV v in eq
    ... | inj₁ i with splitAt⁻¹-↑ˡ {n = K.nV} eq
    ...           | refl =
                    subst (Nat._≤ 1)
                      (sym (trans (count-prod (i ↑ˡ K.nV))
                            (trans (cong (Nat._+ count (injL i) (map remap K-eb))
                                         (cong₂ Nat._+_
                                           (count-map-↑ˡ K.nV i G.dom)
                                           (count-map-↑ˡ K.nV i G-eb)))
                                   (trans (cong (count i G.dom + count i G-eb Nat.+_)
                                                (count-injL-remap-K-eb-zero i))
                                          (trans (Nat.+-identityʳ _)
                                                 (sym (count-++ i G.dom G-eb)))))))
                      (G-bnd i)
    bound v | inj₂ j with splitAt⁻¹-↑ʳ {m = G.nV} eq
    ...                | refl =
                         subst (Nat._≤ 1)
                           (sym (trans (count-prod (G.nV ↑ʳ j))
                                 (trans (cong (Nat._+ count (injR j) (map remap K-eb))
                                              (cong₂ Nat._+_
                                                (count-map-↑ˡ-mismatch G.nV j G.dom)
                                                (count-map-↑ˡ-mismatch G.nV j G-eb)))
                                        (count-injR-remap-K-eb j))))
                           K-eb-bnd-j
      where
        K-eb-bnd-j : count j K-eb Nat.≤ 1
        K-eb-bnd-j =
          Nat.≤-trans
            (Nat.≤-trans (Nat.m≤n+m (count j K-eb) (count j K.dom))
                         (Nat.≤-reflexive (sym (count-++ j K.dom K-eb))))
            (K-bnd j)

--------------------------------------------------------------------------------
-- Base cases.

Linear-hEmpty : Linear hEmpty
Linear-hEmpty = (λ ()) , (λ ())

Linear-hVar : ∀ x → Linear (hVar x)
Linear-hVar x =
    (λ { zero → refl })
  , (λ { zero → s≤s z≤n })

-- Symmetry: `dom = LL ++ RR`, `cod = RR ++ LL`, no edges.  Both sides
-- count `LL`/`RR` once each, just permuted; bound by `count-LL-RR-eq-1`.
Linear-hSwap : ∀ A B → Linear (hSwap A B)
Linear-hSwap A B = balance , bound
  where
    nA = length (flatten A)
    nB = length (flatten B)

    LL : List (Fin (nA + nB))
    LL = map (_↑ˡ nB) (range nA)

    RR : List (Fin (nA + nB))
    RR = map (nA ↑ʳ_) (range nB)

    balance : ∀ v → count v ((LL ++ RR) ++ []) ≡ count v ((RR ++ LL) ++ [])
    balance v rewrite ++-identityʳ (LL ++ RR) | ++-identityʳ (RR ++ LL) =
      count-swap v LL RR

    bound : ∀ v → count v ((LL ++ RR) ++ []) Nat.≤ 1
    bound v rewrite ++-identityʳ (LL ++ RR) | count-LL-RR-eq-1 nA nB v =
      s≤s z≤n

-- Generator edge: `dom = LL`, `cod = RR`; the single edge has
-- `ein _ = LL`, `eout _ = RR`.  Reduces to the same `LL ⊕ RR` story as hSwap.
Linear-hGen : ∀ {A B} (g : mor A B) → Linear (hGen g)
Linear-hGen {A} {B} _ = balance , bound
  where
    nA = length (flatten A)
    nB = length (flatten B)

    LL : List (Fin (nA + nB))
    LL = map (_↑ˡ nB) (range nA)

    RR : List (Fin (nA + nB))
    RR = map (nA ↑ʳ_) (range nB)

    balance : ∀ v → count v (LL ++ (RR ++ [])) ≡ count v (RR ++ (LL ++ []))
    balance v rewrite ++-identityʳ RR | ++-identityʳ LL =
      count-swap v LL RR

    bound : ∀ v → count v (LL ++ (RR ++ [])) Nat.≤ 1
    bound v rewrite ++-identityʳ RR | count-LL-RR-eq-1 nA nB v =
      s≤s z≤n

Linear-hId : ∀ A → Linear (hId A)
Linear-hId unit       = Linear-hEmpty
Linear-hId (Var x)    = Linear-hVar x
Linear-hId (A ⊗₀ B)   = Linear-hTensor (hId A) (hId B)
                          (Linear-hId A) (Linear-hId B)

--------------------------------------------------------------------------------
-- The translation `⟪ f ⟫` is Linear.
--
-- ρ/α/λ cases unfold directly to `Linear-hId` (no `subst₂` boundary
-- transport): the boundary equations live in `⟪⟫-domL`/`⟪⟫-codL`
-- separately rather than being woven into the type.

⟪⟫-Linear : ∀ {A B} (f : HomTerm A B) → Linear ⟪ f ⟫
⟪⟫-Linear (Agen g)        = Linear-hGen g
⟪⟫-Linear (id {A})        = Linear-hId A
⟪⟫-Linear (g ∘ f)         =
  Linear-hCompose ⟪ f ⟫ ⟪ g ⟫
    (trans (⟪⟫-codL f) (sym (⟪⟫-domL g)))
    (⟪⟫-Linear f) (⟪⟫-Linear g)
⟪⟫-Linear (f ⊗₁ g)        =
  Linear-hTensor ⟪ f ⟫ ⟪ g ⟫ (⟪⟫-Linear f) (⟪⟫-Linear g)
⟪⟫-Linear (λ⇒ {A})        = Linear-hId A
⟪⟫-Linear (λ⇐ {A})        = Linear-hId A
⟪⟫-Linear (ρ⇒ {A})        = Linear-hId (A ⊗₀ unit)
⟪⟫-Linear (ρ⇐ {A})        = Linear-hId (A ⊗₀ unit)
⟪⟫-Linear (α⇒ {A}{B}{C})  = Linear-hId ((A ⊗₀ B) ⊗₀ C)
⟪⟫-Linear (α⇐ {A}{B}{C})  = Linear-hId ((A ⊗₀ B) ⊗₀ C)
⟪⟫-Linear (σ {A}{B})      = Linear-hSwap A B

--------------------------------------------------------------------------------
-- Helpers for `decode-attempt-hCompose`'s K-side machinery.
--
-- Given Linear G + Linear K, expose `K-dom-bnd`, `G-cod-bnd`,
-- `length-K-dom`, `remap-noDom`, `map-remap-K-dom`, and `remap-injective`
-- (globally injective).  `remap-injective`'s both-in-K.dom subcase uses
-- a count-based contradiction (count ≥ 2 from K.dom ↭ x ∷ y ∷ rest,
-- count ≤ 1 from map-remap-K-dom + G-cod-bnd).

module hCompose-Linear-utils
  (G K : Hypergraph FlatGen) (bdy-eq : codL G ≡ domL K)
  (lin-G : Linear G) (lin-K : Linear K)
  where

  open hCompose-impl G K bdy-eq public
  -- The Linearity-free combinatorial core is shared via `remap-core` and
  -- re-exported here; only the duplicate-freeness bounds (`K-dom-bnd` /
  -- `G-cod-bnd`) are Linearity-dependent and stay local.
  open remap-core G K bdy-eq public
  private
    module G = Hypergraph G
    module K = Hypergraph K

    G-bal = proj₁ lin-G
    G-bnd = proj₂ lin-G
    K-bnd = proj₂ lin-K
    K-eb = concat (tabulate K.eout)
    G-eb = concat (tabulate G.eout)
    G-ein-b = concat (tabulate G.ein)

  -- K.dom is dup-free.
  K-dom-bnd : ∀ k → count k K.dom Nat.≤ 1
  K-dom-bnd k =
    Nat.≤-trans
      (Nat.≤-trans (Nat.m≤m+n (count k K.dom) _)
                   (Nat.≤-reflexive (sym (count-++ k K.dom K-eb))))
      (K-bnd k)

  -- G.cod is dup-free, from balance + bound on G.
  G-cod-bnd : ∀ v → count v G.cod Nat.≤ 1
  G-cod-bnd v =
    Nat.≤-trans
      (Nat.≤-trans (Nat.m≤m+n (count v G.cod) _)
                   (Nat.≤-reflexive (sym (count-++ v G.cod G-ein-b))))
      (Nat.≤-trans (Nat.≤-reflexive (sym (G-bal v))) (G-bnd v))

  map-remap-K-dom : map remap K.dom ≡ map injL G.cod
  map-remap-K-dom = map-remap-K-dom-from-bnd K-dom-bnd

  -- Auxiliary count lemmas for the remap-injective proof.

  -- count v (map f xs) ≥ count k xs whenever f k = v.
  private
    count-map-≥-fiber
      : ∀ {n m} (f : Fin n → Fin m) (k : Fin n) {v : Fin m}
      → f k ≡ v
      → ∀ (xs : List (Fin n)) → count k xs Nat.≤ count v (map f xs)
    count-map-≥-fiber f k {v} eq []       = z≤n
    count-map-≥-fiber f k {v} eq (x ∷ xs) with k ≟ x
    count-map-≥-fiber f k {v} eq (x ∷ xs) | yes refl with v ≟ f x
    ...                                                  | yes _ = s≤s (count-map-≥-fiber f k eq xs)
    ...                                                  | no  q = ⊥-elim (q (sym eq))
    count-map-≥-fiber f k {v} eq (x ∷ xs) | no  _    with v ≟ f x
    ...                                                  | yes _ = Nat.≤-trans
                                                                    (count-map-≥-fiber f k eq xs)
                                                                    (Nat.n≤1+n _)
    ...                                                  | no  _ = count-map-≥-fiber f k eq xs

  private
    count-map-remap-K-dom-≤-1 : ∀ v → count v (map remap K.dom) Nat.≤ 1
    count-map-remap-K-dom-≤-1 v
      rewrite map-remap-K-dom = aux v
      where
        aux : ∀ v → count v (map (_↑ˡ K.nV) G.cod) Nat.≤ 1
        aux v with splitAt G.nV v in eq-split
        ... | inj₁ g with splitAt⁻¹-↑ˡ {n = K.nV} eq-split
        ...             | refl =
                          Nat.≤-trans
                            (Nat.≤-reflexive (count-map-↑ˡ K.nV g G.cod))
                            (G-cod-bnd g)
        aux v | inj₂ k with splitAt⁻¹-↑ʳ {m = G.nV} eq-split
        ...               | refl =
                            Nat.≤-trans
                              (Nat.≤-reflexive
                                (count-map-↑ˡ-mismatch G.nV k G.cod))
                              z≤n

  -- K.dom permutes to `x ∷ y ∷ rest` when `x ≠ y` are both in K.dom.
  private
    K-dom-↭-x∷y∷
      : ∀ (x y : Fin K.nV) → ¬ (x ≡ y)
      → 0 Nat.< count x K.dom → 0 Nat.< count y K.dom
      → ∃[ rest ] (K.dom Perm.↭ x ∷ y ∷ rest)
    K-dom-↭-x∷y∷ x y x≢y cx cy
        with count-pos→split x K.dom cx
    ... | pre1 , post1 , K-dom-eq-x
        with count-pos→split y (pre1 ++ post1) y-pos-pp
      where
        y≢x : ¬ (y ≡ x)
        y≢x p = x≢y (sym p)
        y-pos-pp : 0 Nat.< count y (pre1 ++ post1)
        y-pos-pp =
          Nat.≤-trans cy
            (Nat.≤-reflexive
              (trans (cong (count y) K-dom-eq-x)
              (trans (count-++ y pre1 (x ∷ post1))
              (trans (cong (count y pre1 +_) (count-cons-no y x post1 y≢x))
                     (sym (count-++ y pre1 post1))))))
    ...    | pre2 , post2 , prepost-eq =
            pre2 ++ post2 , the-perm
      where
        open Perm.PermutationReasoning
        the-perm : K.dom Perm.↭ x ∷ y ∷ (pre2 ++ post2)
        the-perm = begin
          K.dom
            ≡⟨ K-dom-eq-x ⟩
          pre1 ++ x ∷ post1
            ↭⟨ PermProp.shift x pre1 post1 ⟩
          x ∷ pre1 ++ post1
            ≡⟨ cong (x ∷_) prepost-eq ⟩
          x ∷ pre2 ++ y ∷ post2
            ↭⟨ Perm.prep x (PermProp.shift y pre2 post2) ⟩
          x ∷ y ∷ (pre2 ++ post2)
            ∎

  private
    count-cons-eq
      : ∀ {n} (v u : Fin n) (xs : List (Fin n))
      → v ≡ u
      → count v (u ∷ xs) ≡ suc (count v xs)
    count-cons-eq v u xs refl = count-cons-yes v xs

  remap-injective : ∀ {x y} → remap x ≡ remap y → x ≡ y
  remap-injective {x} {y} eq with count x K.dom in cx | count y K.dom in cy
  ... | zero  | zero  =
        ↑ʳ-injective G.nV x y
          (trans (sym (remap-noDom x cx)) (trans eq (remap-noDom y cy)))
  ... | zero  | suc m = ⊥-elim contra
    where
      rx≡injR-x : remap x ≡ injR x
      rx≡injR-x = remap-noDom x cx

      injR-x≡remap-y : injR x ≡ remap y
      injR-x≡remap-y = trans (sym rx≡injR-x) eq

      bnd-y-by-count : count y K.dom Nat.≤ count (injR x) (map remap K.dom)
      bnd-y-by-count = count-map-≥-fiber remap y (sym injR-x≡remap-y) K.dom

      count-injR-x-zero : count (injR x) (map remap K.dom) ≡ 0
      count-injR-x-zero = trans (cong (count (injR x)) map-remap-K-dom)
                                (count-map-↑ˡ-mismatch G.nV x G.cod)

      count-y-zero : count y K.dom ≡ 0
      count-y-zero = Nat.≤-antisym
                       (Nat.≤-trans bnd-y-by-count
                                    (Nat.≤-reflexive count-injR-x-zero))
                       z≤n

      contra : ⊥
      contra with trans (sym count-y-zero) cy
      ... | ()

  ... | suc n | zero  = ⊥-elim contra
    where
      ry≡injR-y : remap y ≡ injR y
      ry≡injR-y = remap-noDom y cy

      injR-y≡remap-x : injR y ≡ remap x
      injR-y≡remap-x = trans (sym ry≡injR-y) (sym eq)

      bnd-x-by-count : count x K.dom Nat.≤ count (injR y) (map remap K.dom)
      bnd-x-by-count = count-map-≥-fiber remap x (sym injR-y≡remap-x) K.dom

      count-injR-y-zero : count (injR y) (map remap K.dom) ≡ 0
      count-injR-y-zero = trans (cong (count (injR y)) map-remap-K-dom)
                                (count-map-↑ˡ-mismatch G.nV y G.cod)

      count-x-zero : count x K.dom ≡ 0
      count-x-zero = Nat.≤-antisym
                       (Nat.≤-trans bnd-x-by-count
                                    (Nat.≤-reflexive count-injR-y-zero))
                       z≤n

      contra : ⊥
      contra with trans (sym count-x-zero) cx
      ... | ()

  ... | suc n | suc m with x ≟ y
  ...                    | yes p = p
  ...                    | no  q = ⊥-elim contra
    where
      cx-pos : 0 Nat.< count x K.dom
      cx-pos = subst (0 Nat.<_) (sym cx) (s≤s z≤n)
      cy-pos : 0 Nat.< count y K.dom
      cy-pos = subst (0 Nat.<_) (sym cy) (s≤s z≤n)

      contra : ⊥
      contra with K-dom-↭-x∷y∷ x y q cx-pos cy-pos
      ... | rest , K-perm =
          Nat.1+n≰n
            (Nat.≤-trans count-≥-2
              (Nat.≤-trans
                (Nat.≤-reflexive
                  (sym (↭⇒count-≡
                         (PermProp.map⁺ remap K-perm)
                         (remap x))))
                (count-map-remap-K-dom-≤-1 (remap x))))
        where
          head-count
            : count (remap x) (remap x ∷ remap y ∷ map remap rest)
            ≡ suc (suc (count (remap x) (map remap rest)))
          head-count =
            trans (count-cons-yes (remap x) (remap y ∷ map remap rest))
                  (cong suc (count-cons-eq (remap x) (remap y) (map remap rest) eq))

          count-≥-2 : 2 Nat.≤ count (remap x) (map remap (x ∷ y ∷ rest))
          count-≥-2 = Nat.≤-trans (s≤s (s≤s z≤n))
                                  (Nat.≤-reflexive (sym head-count))
