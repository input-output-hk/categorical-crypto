{-# OPTIONS --safe --without-K #-}

-- `Data.Bool.ListAction` is definitions only: the stdlib proves none of this.

-- `Data.List`'s `any`/`or` are the deprecated aliases of the
-- `Data.Bool.ListAction` ones.
open import categorical-crypto.Prelude hiding (any; or)

open import Data.Bool.ListAction
open import Data.Bool.Properties
open import Data.List.Properties

open import Algebra.Bundles
open import Algebra.Properties.CommutativeSemigroup
  (CommutativeMonoid.commutativeSemigroup ∨-commutativeMonoid)

module Data.Bool.ListAction.Ext where

private variable
  ℓ : Level
  A B : Type ℓ

any-cong : {P Q : A → Bool} → P ≗ Q → any P ≗ any Q
any-cong P≗Q xs = cong or (map-cong P≗Q xs)

any-const-false : (xs : List A) → any (λ _ → false) xs ≡ false
any-const-false []       = refl
any-const-false (x ∷ xs) = any-const-false xs

any-++ : (P : A → Bool) (xs ys : List A) → any P (xs ++ ys) ≡ any P xs ∨ any P ys
any-++ P []       ys = refl
any-++ P (x ∷ xs) ys = trans (cong (P x ∨_) (any-++ P xs ys))
                             (sym (∨-assoc (P x) (any P xs) (any P ys)))

any-concatMap : (P : B → Bool) (f : A → List B) (xs : List A)
              → any P (concatMap f xs) ≡ any (λ a → any P (f a)) xs
any-concatMap P f []       = refl
any-concatMap P f (x ∷ xs) = trans (any-++ P (f x) (concatMap f xs))
                                   (cong (any P (f x) ∨_) (any-concatMap P f xs))

any-∨ : (P Q : A → Bool) (xs : List A) → any (λ a → P a ∨ Q a) xs ≡ any P xs ∨ any Q xs
any-∨ P Q []       = refl
any-∨ P Q (x ∷ xs) = trans (cong ((P x ∨ Q x) ∨_) (any-∨ P Q xs))
                           (interchange (P x) (Q x) (any P xs) (any Q xs))

-- Fubini for `any`.
any-pair : (Q : A × B → Bool) (xs : List A) (ys : List B)
         → any (λ a → any (λ b → Q (a , b)) ys) xs
         ≡ any (λ b → any (λ a → Q (a , b)) xs) ys
any-pair Q []       ys = sym (any-const-false ys)
any-pair Q (x ∷ xs) ys =
  trans (cong (any (λ b → Q (x , b)) ys ∨_) (any-pair Q xs ys))
        (sym (any-∨ (λ b → Q (x , b)) (λ b → any (λ a → Q (a , b)) xs) ys))
