{-# OPTIONS --safe --without-K #-}

------------------------------------------------------------------------
-- Canonical equivalence of `_↭_` derivations.
--
-- `residual b` is the tail bijection obtained by removing the head of a
-- self-bijection.  `_≅↭_` relates two `_↭_` derivations that agree on
-- their evaluated finite bijection (via `eval-↭`), together with its
-- congruence laws under the four `_↭_` constructors.
------------------------------------------------------------------------

module Categories.PermuteCoherence.Canonical where

open import Data.Nat.Base
open import Data.Fin.Base
open import Data.Fin.Patterns
import Data.Fin.Permutation as P
open P
open import Data.List.Base using (List; []; _∷_; length)
import Data.List.Relation.Binary.Permutation.Propositional as Perm
open Perm using (_↭_)

open import Relation.Binary.PropositionalEquality.Core


open import Level using (Level)

open import Categories.PermuteCoherence.FinBij
open import Categories.PermuteCoherence.Eval

private
  variable
    a : Level
    A : Set a

------------------------------------------------------------------------
-- Removing the head bijectively: `residual` is the bijection on the tail.

residual : ∀ {n} → (b : FinBij (suc n) (suc n)) → FinBij n n
residual b = remove 0F b

------------------------------------------------------------------------
-- Canonical equivalence: two derivations are canonically equivalent when
-- they agree on the underlying finite bijection.

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
-- `≅↭`-equivalent to `refl`.

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
