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
-- 1, 2.  eval-↭ on trans / sym (mostly definitional, stated for reuse).

eval-↭-comp : ∀ {xs ys zs : List A} (p : xs ↭ ys) (q : ys ↭ zs) →
              eval-↭ (Perm.trans p q) ≈-fb eval-↭ q ∘-fb eval-↭ p
eval-↭-comp _ _ _ = refl

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
-- 8.  trans-refl normalisations (phrased on `Perm.trans` directly, since
-- the `trans` constructor does NOT identify `trans refl p` with `p`).

eval-↭-trans-refl-l : ∀ {xs ys : List A} (p : xs ↭ ys) →
                      eval-↭ (Perm.trans Perm.refl p) ≈-fb eval-↭ p
eval-↭-trans-refl-l _ _ = refl

eval-↭-trans-refl-r : ∀ {xs ys : List A} (p : xs ↭ ys) →
                      eval-↭ (Perm.trans p Perm.refl) ≈-fb eval-↭ p
eval-↭-trans-refl-r _ _ = refl
