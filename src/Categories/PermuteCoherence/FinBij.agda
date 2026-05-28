{-# OPTIONS --safe --cubical-compatible #-}

------------------------------------------------------------------------
-- A minimal finite-bijection model.
--
-- `FinBij n m` is the type of bijections between `Fin n` and `Fin m`.
-- This type is empty whenever `n ≢ m` (see `Data.Fin.Permutation.↔⇒≡`).
--
-- The module is a thin wrapper around stdlib's `Data.Fin.Permutation`
-- providing the small API expected by `Categories.PermuteCoherence.Eval`.
------------------------------------------------------------------------

module Categories.PermuteCoherence.FinBij where

open import Data.Nat.Base using (ℕ; zero; suc; _+_)
open import Data.Fin.Base using (Fin; zero; suc)
open import Data.Fin.Patterns using (0F; 1F)
import Data.Fin.Permutation as P
open P using (Permutation; _∘ₚ_; transpose; lift₀)
open import Relation.Binary.PropositionalEquality.Core
  using (_≡_; refl)

private
  variable
    n m k : ℕ

------------------------------------------------------------------------
-- The type

FinBij : ℕ → ℕ → Set
FinBij n m = Permutation n m

------------------------------------------------------------------------
-- Identity, composition, inverse

id-fb : FinBij n n
id-fb = P.id

-- Categorical (right-to-left) composition.
infixr 9 _∘-fb_
_∘-fb_ : FinBij m k → FinBij n m → FinBij n k
g ∘-fb f = f ∘ₚ g

inv-fb : FinBij n m → FinBij m n
inv-fb = P.flip

------------------------------------------------------------------------
-- Generators used by `eval-↭`

-- Prepend identity at position 0:  cons-fb π : FinBij (suc n) (suc m).
cons-fb : FinBij n m → FinBij (suc n) (suc m)
cons-fb = lift₀

-- Swap the first two positions, leaving the rest fixed.
swap-fb : ∀ n → FinBij (suc (suc n)) (suc (suc n))
swap-fb _ = transpose 0F 1F

------------------------------------------------------------------------
-- Equality on bijections (pointwise on the forward map).

infix 4 _≈-fb_
_≈-fb_ : FinBij n m → FinBij n m → Set
π ≈-fb ρ = P._≈_ π ρ

≈-fb-refl : {π : FinBij n m} → π ≈-fb π
≈-fb-refl _ = refl
