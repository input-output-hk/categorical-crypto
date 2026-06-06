{-# OPTIONS --safe --without-K #-}

------------------------------------------------------------------------
-- Soundness of `eval-↭` and structural identities at the FinBij level.
--
-- These are the bijection-level coherence lemmas required by the
-- canonical-form / faithfulness work for list permutations.
------------------------------------------------------------------------

module Categories.PermuteCoherence.Soundness where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Fin.Base using (Fin; zero; suc)
open import Data.Fin.Patterns using (0F; 1F)
open import Data.List.Base using (List; []; _∷_; length)
import Data.List.Relation.Binary.Permutation.Propositional as Perm
open Perm using (_↭_)

import Data.Fin.Permutation as P

open import Relation.Binary.PropositionalEquality.Core
  using (_≡_; refl; sym; cong)

open import Categories.PermuteCoherence.FinBij
open import Categories.PermuteCoherence.Eval

open import Level using (Level)

private
  variable
    a : Level
    A : Set a
    n m k : ℕ

------------------------------------------------------------------------
-- Equivalence lemmas for `_≈-fb_`.

≈-fb-sym : {π ρ : FinBij n m} → π ≈-fb ρ → ρ ≈-fb π
≈-fb-sym eq i = sym (eq i)

≈-fb-trans : {π ρ σ : FinBij n m} → π ≈-fb ρ → ρ ≈-fb σ → π ≈-fb σ
≈-fb-trans p q i rewrite p i = q i

------------------------------------------------------------------------
-- 4.  cons-fb-functor-id

cons-fb-functor-id : cons-fb (id-fb {n = n}) ≈-fb id-fb {n = suc n}
cons-fb-functor-id = P.lift₀-id

------------------------------------------------------------------------
-- 5.  cons-fb-functor-comp

cons-fb-functor-comp : ∀ {n m k} (g : FinBij m k) (f : FinBij n m) →
                       cons-fb (g ∘-fb f) ≈-fb cons-fb g ∘-fb cons-fb f
cons-fb-functor-comp g f i = sym (P.lift₀-comp f g i)

------------------------------------------------------------------------
-- 3.  swap-fb-involutive
--
-- Use a small auxiliary saying that `PC.transpose i j` is symmetric in
-- `i, j`.


swap-fb-involutive : swap-fb n ∘-fb swap-fb n ≈-fb id-fb
swap-fb-involutive 0F            = refl
swap-fb-involutive (suc 0F)      = refl
swap-fb-involutive (suc (suc i)) = refl

------------------------------------------------------------------------
-- 6.  swap-fb-natural
--
-- swap-fb m ∘-fb cons-fb (cons-fb f) ≈ cons-fb (cons-fb f) ∘-fb swap-fb n

swap-fb-natural : ∀ {n m} (f : FinBij n m) →
                  swap-fb m ∘-fb cons-fb (cons-fb f)
                  ≈-fb
                  cons-fb (cons-fb f) ∘-fb swap-fb n
swap-fb-natural f 0F             = refl
swap-fb-natural f (suc 0F)       = refl
swap-fb-natural f (suc (suc i))  = refl

------------------------------------------------------------------------
-- 7.  Yang-Baxter (braid) identity at the bijection level
--
--   swap-fb (1+n) ∘-fb cons-fb (swap-fb n) ∘-fb swap-fb (1+n)
-- ≈ cons-fb (swap-fb n) ∘-fb swap-fb (1+n) ∘-fb cons-fb (swap-fb n)

yang-baxter : ∀ {n} →
  swap-fb (suc n) ∘-fb cons-fb (swap-fb n) ∘-fb swap-fb (suc n)
  ≈-fb
  cons-fb (swap-fb n) ∘-fb swap-fb (suc n) ∘-fb cons-fb (swap-fb n)
yang-baxter 0F                   = refl
yang-baxter (suc 0F)             = refl
yang-baxter (suc (suc 0F))       = refl
yang-baxter (suc (suc (suc i)))  = refl

------------------------------------------------------------------------
-- 1, 2.  eval-↭ on trans / sym
--
-- These are mostly definitional but stated for downstream use.

eval-↭-comp : ∀ {xs ys zs : List A} (p : xs ↭ ys) (q : ys ↭ zs) →
              eval-↭ (Perm.trans p q) ≈-fb eval-↭ q ∘-fb eval-↭ p
eval-↭-comp _ _ _ = refl

-- `inv-fb` distributes over composition (definitionally, at the level
-- of `_≈-fb_`).

inv-fb-comp : ∀ {n m k} (g : FinBij m k) (f : FinBij n m) →
              inv-fb (g ∘-fb f) ≈-fb inv-fb f ∘-fb inv-fb g
inv-fb-comp _ _ _ = refl

-- `inv-fb (cons-fb π) ≈ cons-fb (inv-fb π)`.

inv-fb-cons : ∀ {n m} (π : FinBij n m) →
              inv-fb (cons-fb π) ≈-fb cons-fb (inv-fb π)
inv-fb-cons π 0F      = refl
inv-fb-cons π (suc i) = refl

-- `swap-fb` is self-inverse: `inv-fb (swap-fb n) ≈ swap-fb n`.

inv-fb-swap : ∀ {n} → inv-fb (swap-fb n) ≈-fb swap-fb n
inv-fb-swap 0F            = refl
inv-fb-swap (suc 0F)      = refl
inv-fb-swap (suc (suc i)) = refl

-- `inv-fb id-fb ≈ id-fb` (definitional).

inv-fb-id : inv-fb (id-fb {n = n}) ≈-fb id-fb
inv-fb-id _ = refl

-- Soundness of `eval-↭` with respect to `↭-sym`.

eval-↭-sym : ∀ {xs ys : List A} (p : xs ↭ ys) →
             eval-↭ (Perm.↭-sym p) ≈-fb inv-fb (eval-↭ p)
eval-↭-sym Perm.refl _       = refl
eval-↭-sym (Perm.prep x p)   = aux
  where
    aux : ∀ j → eval-↭ (Perm.↭-sym (Perm.prep x p)) P.⟨$⟩ʳ j
              ≡ inv-fb (eval-↭ (Perm.prep x p))        P.⟨$⟩ʳ j
    aux 0F      = refl
    aux (suc j) = cong suc (eval-↭-sym p j)
eval-↭-sym (Perm.swap x y p) 0F            = refl
eval-↭-sym (Perm.swap x y p) (suc 0F)      = refl
eval-↭-sym (Perm.swap x y p) (suc (suc i)) =
  cong (λ z → suc (suc z)) (eval-↭-sym p i)
eval-↭-sym (Perm.trans p q) i =
  step-trans
    (cong (eval-↭ (Perm.↭-sym p) P.⟨$⟩ʳ_) (eval-↭-sym q i))
    (eval-↭-sym p (inv-fb (eval-↭ q) P.⟨$⟩ʳ i))
  where
  step-trans : ∀ {a b c : Fin _} → a ≡ b → b ≡ c → a ≡ c
  step-trans refl q = q

------------------------------------------------------------------------
-- 8.  trans-refl normalisations.
--
-- Note: stdlib's `_↭_` constructor for `trans` does *not* identify
-- `trans refl p` with `p` definitionally; only the smart `↭-trans`
-- does.  We therefore phrase these lemmas on `Perm.trans` directly.

eval-↭-trans-refl-l : ∀ {xs ys : List A} (p : xs ↭ ys) →
                      eval-↭ (Perm.trans Perm.refl p) ≈-fb eval-↭ p
eval-↭-trans-refl-l _ _ = refl

eval-↭-trans-refl-r : ∀ {xs ys : List A} (p : xs ↭ ys) →
                      eval-↭ (Perm.trans p Perm.refl) ≈-fb eval-↭ p
eval-↭-trans-refl-r _ _ = refl
