{-# OPTIONS --safe --cubical-compatible #-}

------------------------------------------------------------------------
-- Finite bijections, with categorical (right-to-left) composition.
-- `FinBij n m` is empty when `n ≢ m`; see `Data.Fin.Permutation.↔⇒≡`.
------------------------------------------------------------------------

module Categories.PermuteCoherence.FinBij where

open import Data.Fin.Base
open import Data.Fin.Patterns
import Data.Fin.Permutation as P
open P
open import Data.Nat.Base
open import Relation.Binary.PropositionalEquality.Core

private
  variable
    n m k : ℕ

FinBij : ℕ → ℕ → Set
FinBij n m = Permutation n m

------------------------------------------------------------------------
-- Bijection operations
------------------------------------------------------------------------
id-fb : FinBij n n
id-fb = P.id

infixr 9 _∘-fb_
_∘-fb_ : FinBij m k → FinBij n m → FinBij n k
g ∘-fb f = f ∘ₚ g

inv-fb : FinBij n m → FinBij m n
inv-fb = P.flip

------------------------------------------------------------------------
-- Adjacent-transposition generators
------------------------------------------------------------------------
cons-fb : FinBij n m → FinBij (suc n) (suc m)
cons-fb = lift₀

swap-fb : ∀ n → FinBij (suc (suc n)) (suc (suc n))
swap-fb _ = transpose 0F 1F

infix 4 _≈-fb_
_≈-fb_ : FinBij n m → FinBij n m → Set
π ≈-fb ρ = P._≈_ π ρ

≈-fb-trans : {b b′ b″ : FinBij n m} → b ≈-fb b′ → b′ ≈-fb b″ → b ≈-fb b″
≈-fb-trans h₁ h₂ x = trans (h₁ x) (h₂ x)
