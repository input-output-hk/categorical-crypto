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

module Categories.APROP.Hypergraph.Soundness.Linearity (sig : APROPSignature) where

open APROP sig
open import Categories.APROP.Hypergraph.Core
open import Categories.APROP.Hypergraph.FromAPROP sig
  using ( FlatGen; flatten; range
        ; hEmpty; hVar; hId; hGen; hSwap; hTensor
        ; module hTensor-impl)

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

