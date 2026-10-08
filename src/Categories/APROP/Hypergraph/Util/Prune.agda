{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- Pruning helpers for the pruned cospan composition `hComposeP`.
--
-- Given `xs : List (Fin n)` (typically `K.dom` of the right operand of a
-- cospan composition), identify the Fin values NOT in `xs`.  After
-- composition the positions named in `xs` have been "glued" to the left
-- operand's `cod`, so they become unreferenced and can be pruned.
--------------------------------------------------------------------------------

module Categories.APROP.Hypergraph.Util.Prune where

open import Data.Empty
open import Data.Fin using (Fin; _↑ˡ_; _↑ʳ_; splitAt)
open import Data.Fin.Properties using (_≟_; splitAt-↑ˡ; splitAt-↑ʳ; ↑ˡ-injective; ↑ʳ-injective)
open import Data.List using (List; length; filter; allFin; lookup; map)
open import Data.List.Membership.Propositional
open import Data.List.Membership.Propositional.Properties
open import Data.List.Properties.Ext
open import Data.List.Relation.Unary.Any using (index)
open import Data.List.Relation.Unary.Any.Properties
open import Data.List.Relation.Unary.Unique.Propositional
open import Data.Nat using (ℕ; _+_)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_]′)
open import Function
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary.Decidable using (Dec; ¬?; yes; no)

--------------------------------------------------------------------------------
-- Membership classification
--------------------------------------------------------------------------------

module _ {n : ℕ} where
  open import Data.List.Membership.DecPropositional (_≟_ {n = n}) using (_∈?_)

  nonMem? : (xs : List (Fin n)) → (v : Fin n) → Dec (v ∉ xs)
  nonMem? xs v = ¬? (v ∈? xs)

  nonMem : List (Fin n) → List (Fin n)
  nonMem xs = filter (nonMem? xs) (allFin n)

  count-non : List (Fin n) → ℕ
  count-non xs = length (nonMem xs)

  classify : (xs : List (Fin n)) (v : Fin n) → Fin (length xs) ⊎ Fin (count-non xs)
  classify xs v with v ∈? xs
  ... | yes v∈xs = inj₁ (index v∈xs)
  ... | no  v∉xs = inj₂ (index (∈-filter⁺ (nonMem? xs) (∈-allFin v) v∉xs))

  data ClassifyV (xs : List (Fin n)) (v : Fin n)
       : Fin (length xs) ⊎ Fin (count-non xs) → Set where
    is-mem : (p : v ∈ xs)        → ClassifyV xs v (inj₁ (index p))
    is-non : (p : v ∈ nonMem xs) → ClassifyV xs v (inj₂ (index p))

  classify-view : (xs : List (Fin n)) (v : Fin n) → ClassifyV xs v (classify xs v)
  classify-view xs v with v ∈? xs
  ... | yes p = is-mem p
  ... | no  q = is-non (∈-filter⁺ (nonMem? xs) (∈-allFin v) q)

  classify-lookup-Unique
    : (xs : List (Fin n)) → Unique xs
    → (j : Fin (length xs))
    → classify xs (lookup xs j) ≡ inj₁ j
  classify-lookup-Unique xs unique j with lookup xs j ∈? xs
  ... | yes v∈ = cong inj₁
    (lookup-injective-unique unique (index v∈) j (sym (lookup-index v∈)))
  ... | no  v∉ = ⊥-elim (v∉ (∈-lookup j))

--------------------------------------------------------------------------------
-- Disjoint vertex embeddings
--------------------------------------------------------------------------------

↑ˡ-inj : ∀ {n} (k : ℕ) {i j : Fin n} → i ↑ˡ k ≡ j ↑ˡ k → i ≡ j
↑ˡ-inj k {i} {j} eq = ↑ˡ-injective k i j eq

↑ʳ-inj : ∀ (k : ℕ) {n} {i j : Fin n} → k ↑ʳ i ≡ k ↑ʳ j → i ≡ j
↑ʳ-inj k {n} {i} {j} eq = ↑ʳ-injective k i j eq

↑ˡ-↑ʳ-disjoint : ∀ {m k} (i : Fin m) (j : Fin k) → i ↑ˡ k ≡ m ↑ʳ j → ⊥
↑ˡ-↑ʳ-disjoint {m} {k} i j eq
  with trans (sym (splitAt-↑ˡ m i k)) (trans (cong (splitAt m) eq) (splitAt-↑ʳ m k j))
... | ()

--------------------------------------------------------------------------------
-- Pruned remapping
--------------------------------------------------------------------------------

module _ {n m : ℕ} where
  open import Data.List.Membership.DecPropositional (_≟_ {n = n}) using (_∈?_)
  remap : (xs : List (Fin n)) → (Fin (length xs) → Fin m) → Fin n → Fin (m + count-non xs)
  remap xs f v = [ (λ i → f i ↑ˡ count-non xs) , (λ j → m ↑ʳ j) ]′ (classify xs v)

  remap-inj₁ : (xs : List (Fin n)) (f : Fin (length xs) → Fin m)
               (v : Fin n) (i : Fin (length xs))
             → classify xs v ≡ inj₁ i
             → remap xs f v ≡ f i ↑ˡ count-non xs
  remap-inj₁ xs f v i eq with classify xs v
  remap-inj₁ xs f v i refl | inj₁ .i = refl

  remap-lookup-compatible
    : (xs : List (Fin n)) (f : Fin (length xs) → Fin m)
    → (∀ i j → lookup xs i ≡ lookup xs j → f i ≡ f j)
    → ∀ i → remap xs f (lookup xs i) ≡ f i ↑ˡ count-non xs
  remap-lookup-compatible xs f compatible i with lookup xs i ∈? xs
  ... | yes p = cong (_↑ˡ count-non xs) (compatible (index p) i (sym (lookup-index p)))
  ... | no q = ⊥-elim (q (∈-lookup i))

  remap-↑ˡ→∈ : (xs : List (Fin n)) (f : Fin (length xs) → Fin m)
               (v : Fin n) (i : Fin m)
             → remap xs f v ≡ i ↑ˡ count-non xs → v ∈ xs
  remap-↑ˡ→∈ xs f v i eq with classify xs v | classify-view xs v
  ... | _ | is-mem v∈ = v∈
  ... | _ | is-non _  = ⊥-elim (↑ˡ-↑ʳ-disjoint i _ (sym eq))

  remap-injective
    : (xs : List (Fin n)) (f : Fin (length xs) → Fin m)
    → Unique xs
    → (∀ {i j : Fin (length xs)} → f i ≡ f j → i ≡ j)
    → ∀ {v v' : Fin n} → remap xs f v ≡ remap xs f v' → v ≡ v'
  remap-injective xs f xs-uniq f-inj {v} {v'} eq
    with classify xs v | classify-view xs v | classify xs v' | classify-view xs v'
  ... | _ | is-mem v∈  | _ | is-mem v'∈ =
    trans (lookup-index v∈)
      (trans (cong (lookup xs) (f-inj (↑ˡ-inj (count-non xs) eq)))
             (sym (lookup-index v'∈)))
  ... | _ | is-mem _   | _ | is-non _   = ⊥-elim (↑ˡ-↑ʳ-disjoint _ _ eq)
  ... | _ | is-non _   | _ | is-mem _   = ⊥-elim (↑ˡ-↑ʳ-disjoint _ _ (sym eq))
  ... | _ | is-non v∈ⁿ | _ | is-non v'∈ⁿ =
    trans (lookup-index v∈ⁿ)
      (trans (cong (lookup (nonMem xs)) (↑ʳ-inj m eq))
             (sym (lookup-index v'∈ⁿ)))

module _ {a} {X : Set a} {n m : ℕ} where
  remap-vlab : (xs : List (Fin n)) (f : Fin (length xs) → Fin m)
               (λK : Fin n → X) (λG : Fin m → X)
               (bdy : ∀ i → λK (lookup xs i) ≡ λG (f i))
               (v : Fin n)
             → [ λG , (λ j → λK (lookup (nonMem xs) j)) ]′
                  (splitAt m (remap xs f v))
             ≡ λK v
  remap-vlab xs f λK λG bdy v with classify xs v | classify-view xs v
  ... | _ | is-mem v∈xs =
    trans
      (cong [ λG , (λ k → λK (lookup (nonMem xs) k)) ]′
        (splitAt-↑ˡ m (f (index v∈xs)) (count-non xs)))
      (trans (sym (bdy (index v∈xs)))
             (cong λK (sym (lookup-index v∈xs))))
  ... | _ | is-non v∈ⁿ =
    trans
      (cong [ λG , (λ k → λK (lookup (nonMem xs) k)) ]′
        (splitAt-↑ʳ m (count-non xs) (index v∈ⁿ)))
      (cong λK (sym (lookup-index v∈ⁿ)))

  map-via-remap : (xs : List (Fin n)) (f : Fin (length xs) → Fin m)
                  (λK : Fin n → X) (λG : Fin m → X)
                  (bdy : ∀ i → λK (lookup xs i) ≡ λG (f i))
                  (ys : List (Fin n))
                → map λK ys
                ≡ map ([ λG , (λ j → λK (lookup (nonMem xs) j)) ]′ ∘ splitAt m)
                      (map (remap xs f) ys)
  map-via-remap xs f λK λG bdy ys =
    sym (map-∘-cong (remap-vlab xs f λK λG bdy) ys)
