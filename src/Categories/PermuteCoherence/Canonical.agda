{-# OPTIONS --safe --without-K #-}

------------------------------------------------------------------------
-- A canonical-form analysis for `_↭_` derivations.
--
-- This module derives a *canonical decomposition* of any
-- `Data.Fin.Permutation`-style finite bijection as a sequence of
-- "adjacent transposition" generators, and reifies that decomposition
-- back into a `_↭_` derivation. Two `_↭_` derivations agreeing on their
-- underlying bijection are then declared *canonically equivalent* via
-- the `_≅↭_` relation, which the downstream `Faithfulness` module is
-- expected to refine into an equality in a quotient setoid.
--
-- The construction proceeds by structural recursion on the length of
-- the list: a bijection of `Fin (suc n)` is decomposed into the choice
-- of where `0F` maps to, then a residual bijection of `Fin n`. The
-- "head choice" is realised by a sequence of adjacent swaps that
-- bubble the chosen element to position 0.
------------------------------------------------------------------------

module Categories.PermuteCoherence.Canonical where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Fin.Base using (Fin; zero; suc)
open import Data.Fin.Patterns using (0F; 1F)
import Data.Fin.Permutation as P
open P using (Permutation; _∘ₚ_; transpose; lift₀; remove)
open import Data.List.Base using (List; []; _∷_; length)
import Data.List.Relation.Binary.Permutation.Propositional as Perm
open Perm using (_↭_)

open import Data.Product.Base using (Σ; _×_; _,_; ∃; ∃-syntax; proj₁; proj₂)

open import Relation.Binary.PropositionalEquality.Core
  using (_≡_; refl; cong; sym; trans)

open import Level using (Level)

open import Categories.PermuteCoherence.FinBij
open import Categories.PermuteCoherence.Eval

private
  variable
    a : Level
    A : Set a

------------------------------------------------------------------------
-- "Bubble-the-head" canonical motion: given a list of length (suc n) and
-- a target `k : Fin (suc n)`, swap the element at position k to the head
-- via k adjacent transpositions.

lookup : (xs : List A) → Fin (length xs) → A
lookup (x ∷ _)  zero    = x
lookup (_ ∷ xs) (suc i) = lookup xs i

-- `bubble-to-front xs k = (ys , p)` with `p : xs ↭ (lookup xs k ∷ ys)`,
-- the predecessor length `n` made explicit as a parameter.

bubble-to-front : ∀ {n} (xs : List A) (xs-len : length xs ≡ suc n)
                  (k : Fin (length xs)) →
                  Σ (List A) λ ys → length ys ≡ n × xs ↭ (lookup xs k ∷ ys)
bubble-to-front {n = n}     []           ()     k
bubble-to-front {n = n}     (x ∷ xs)     xs-len zero =
  xs , suc-injective xs-len , Perm.refl
  where
  suc-injective : ∀ {a b} → suc a ≡ suc b → a ≡ b
  suc-injective refl = refl
bubble-to-front {n = zero}  (x ∷ [])     refl   (suc ())
bubble-to-front {n = suc n} (x ∷ y ∷ xs) xs-len (suc k)
  with bubble-to-front {n = n} (y ∷ xs) (suc-injective xs-len) k
  where
  suc-injective : ∀ {a b} → suc a ≡ suc b → a ≡ b
  suc-injective refl = refl
... | (zs , zs-len , p) =
  x ∷ zs , cong suc zs-len ,
  Perm.trans (Perm.prep x p)
             (Perm.swap x (lookup (y ∷ xs) k) Perm.refl)

------------------------------------------------------------------------
-- Removing the head bijectively: `head-target` is where the head goes in
-- the target, `residual` the bijection on the tail.

head-target : ∀ {n} → FinBij (suc n) (suc n) → Fin (suc n)
head-target b = b P.⟨$⟩ʳ 0F

residual : ∀ {n} → (b : FinBij (suc n) (suc n)) → FinBij n n
residual b = remove 0F b

------------------------------------------------------------------------
-- The canonical decoder.  Given `xs` and a self-bijection `b`, produce a
-- target list `ys` and a derivation `xs ↭ ys`.  At length (suc n): bubble
-- position `head-target b` to the front, recurse on the tail with the
-- residual bijection.

private
  cast-fin-back : ∀ {p q} → p ≡ q → Fin q → Fin p
  cast-fin-back refl i = i

-- Recurses on a nat bound on the list length.
canonical-go : ∀ (n : ℕ) (xs : List A) → length xs ≡ n →
               (b : FinBij n n) →
               ∃[ ys ] (xs Perm.↭ ys)
canonical-go zero    []       _      b = [] , Perm.refl
canonical-go zero    (_ ∷ _)  ()     b
canonical-go (suc n) []       ()     b
canonical-go (suc n) (x ∷ xs) xs-len b
  with cast-fin-back xs-len (head-target b)
... | k with bubble-to-front {n = n} (x ∷ xs) xs-len k
... | (ws , ws-len , bubble) with canonical-go n ws ws-len (residual b)
... | (ys , rec) =
  lookup (x ∷ xs) k ∷ ys ,
  Perm.trans bubble (Perm.prep _ rec)

canonical : (xs : List A) (b : FinBij (length xs) (length xs)) →
            ∃[ ys ] (xs Perm.↭ ys)
canonical xs b = canonical-go (length xs) xs refl b

------------------------------------------------------------------------
-- Propositional unfolding equations for `canonical-go`, exposing its
-- `with`-blocks so downstream consumers can reason on abstract bijections.

canonical-go-zero
  : proj₁ (canonical-go zero ([] {A = A}) refl id-fb) ≡ []
canonical-go-zero = refl

canonical-go-suc-unfold
  : ∀ (x : A) (xs : List A) (b : FinBij (suc (length xs)) (suc (length xs)))
  → proj₁ (canonical-go (suc (length xs)) (x ∷ xs) refl b)
    ≡ lookup (x ∷ xs) (head-target b)
      ∷ proj₁ (canonical-go (length xs)
                            (proj₁ (bubble-to-front (x ∷ xs) refl (head-target b)))
                            (proj₁ (proj₂ (bubble-to-front (x ∷ xs) refl (head-target b))))
                            (residual b))
canonical-go-suc-unfold x xs b = refl

-- The derivation-projection unfolding.
canonical-go-suc-unfold-↭
  : ∀ (x : A) (xs : List A) (b : FinBij (suc (length xs)) (suc (length xs)))
  → proj₂ (canonical-go (suc (length xs)) (x ∷ xs) refl b)
    ≡ Perm.trans
        (proj₂ (proj₂ (bubble-to-front (x ∷ xs) refl (head-target b))))
        (Perm.prep _ (proj₂ (canonical-go (length xs)
                              (proj₁ (bubble-to-front (x ∷ xs) refl (head-target b)))
                              (proj₁ (proj₂ (bubble-to-front (x ∷ xs) refl (head-target b))))
                              (residual b))))
canonical-go-suc-unfold-↭ x xs b = refl

canonical-target : (xs : List A) → FinBij (length xs) (length xs) → List A
canonical-target xs b = proj₁ (canonical xs b)

canonical-↭ : (xs : List A) (b : FinBij (length xs) (length xs)) →
              xs Perm.↭ canonical-target xs b
canonical-↭ xs b = proj₂ (canonical xs b)

------------------------------------------------------------------------
-- Canonical equivalence: two derivations are canonically equivalent when
-- they agree on the underlying finite bijection.  This is what coherence
-- consumers (e.g. `Faithfulness`) use to quotient `_↭_` by `eval-↭`.

infix 4 _≅↭_
_≅↭_ : {xs ys : List A} → xs ↭ ys → xs ↭ ys → Set
p ≅↭ q = eval-↭ p ≈-fb eval-↭ q

≅↭-refl : {xs ys : List A} {p : xs ↭ ys} → p ≅↭ p
≅↭-refl _ = refl

≅↭-sym : {xs ys : List A} {p q : xs ↭ ys} → p ≅↭ q → q ≅↭ p
≅↭-sym eq i = sym (eq i)

≅↭-trans : {xs ys : List A} {p q r : xs ↭ ys} → p ≅↭ q → q ≅↭ r → p ≅↭ r
≅↭-trans p≡q q≡r i = trans (p≡q i) (q≡r i)

------------------------------------------------------------------------
-- A self-loop `r : xs ↭ xs` evaluating to the identity bijection is
-- `≅↭`-equivalent to `refl`.  (The constructive upgrade to ↭-equivalence
-- is `Faithfulness`'s job.)

self-loop-canonical
  : {xs : List A} (r : xs Perm.↭ xs)
  → eval-↭ r ≈-fb id-fb
  → r ≅↭ Perm.refl
self-loop-canonical _ eq i = eq i

------------------------------------------------------------------------
-- Congruence of `_≅↭_` under the four `_↭_` constructors.

private
  ∘-fb-cong : ∀ {n m k} {g g′ : FinBij m k} {f f′ : FinBij n m} →
              g ≈-fb g′ → f ≈-fb f′ → (g ∘-fb f) ≈-fb (g′ ∘-fb f′)
  ∘-fb-cong {g = g} {g′} {f} {f′} g≈ f≈ i
    rewrite f≈ i = g≈ (f′ P.⟨$⟩ʳ i)

  cons-fb-cong : ∀ {n m} {f f′ : FinBij n m} →
                 f ≈-fb f′ → cons-fb f ≈-fb cons-fb f′
  cons-fb-cong eq 0F      = refl
  cons-fb-cong eq (suc i) = cong suc (eq i)

≅↭-prep : ∀ {xs ys : List A} {p q : xs ↭ ys} (x : A) →
          p ≅↭ q → Perm.prep x p ≅↭ Perm.prep x q
≅↭-prep x p≅q = cons-fb-cong p≅q

≅↭-swap : ∀ {xs ys : List A} {p q : xs ↭ ys} (x y : A) →
          p ≅↭ q → Perm.swap x y p ≅↭ Perm.swap x y q
≅↭-swap {xs = xs} {ys} {p = p} {q} x y p≅q =
  ∘-fb-cong {g = swap-fb (length ys)} {g′ = swap-fb (length ys)}
            {f = cons-fb (cons-fb (eval-↭ p))}
            {f′ = cons-fb (cons-fb (eval-↭ q))}
            (λ _ → refl)
            (cons-fb-cong (cons-fb-cong p≅q))

≅↭-trans-cong
  : ∀ {xs ys zs : List A} {p p′ : xs ↭ ys} {q q′ : ys ↭ zs}
  → p ≅↭ p′ → q ≅↭ q′
  → Perm.trans p q ≅↭ Perm.trans p′ q′
≅↭-trans-cong {p = p} {p′} {q} {q′} p≅p′ q≅q′ =
  ∘-fb-cong {g = eval-↭ q} {g′ = eval-↭ q′}
            {f = eval-↭ p} {f′ = eval-↭ p′}
            q≅q′ p≅p′
