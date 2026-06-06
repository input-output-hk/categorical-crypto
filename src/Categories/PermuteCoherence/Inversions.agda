{-# OPTIONS --safe --without-K #-}

------------------------------------------------------------------------
-- The inversion count `inv` (Coxeter length) on `FinBij`, and the fact
-- that the bubble-sort word `canonW` is REDUCED (its length is `inv`).
--
-- `inv` is defined by the Lehmer-code recursion mirroring `canonW`, so
-- `length (canonW b) ≡ inv b` is a clean induction (L2 below).  The descent
-- dichotomy `inv (genFB i ∘-fb b) = inv b ± 1` (L1) is proved separately.
------------------------------------------------------------------------

module Categories.PermuteCoherence.Inversions where

open import Data.Nat.Base using (ℕ; zero; suc; _+_)
open import Data.Fin.Base using (Fin; toℕ) renaming (suc to fsuc)
open import Data.Fin.Patterns using (0F)
open import Data.List.Base using ([]; _∷_; _++_; length)
open import Data.List.Properties using (length-++)
import Data.Fin.Permutation as P
open P using (remove)
open import Relation.Binary.PropositionalEquality.Core
  using (_≡_; refl; trans; sym; cong; cong₂)

open import Categories.PermuteCoherence.FinBij using (FinBij; _∘-fb_; inv-fb)
open import Categories.PermuteCoherence.Word
  using (Word; liftW; rotateW; rotate-fb; canonW)

private
  variable
    n : ℕ

------------------------------------------------------------------------
-- 1. The inversion count, by the Lehmer-code recursion.
--
-- `b ⟨$⟩ˡ 0F` is the position of the smallest value; since it is the
-- smallest, every earlier position holds a larger value, contributing
-- exactly `toℕ (b ⟨$⟩ˡ 0F)` inversions.  The remaining inversions are
-- those of the residual (the same `rest` as in `canonW`).

opaque
  inv : {n : ℕ} → FinBij (suc n) (suc n) → ℕ
  inv {zero}  b = 0
  inv {suc n} b =
    inv (remove 0F (b ∘-fb inv-fb (rotate-fb (b P.⟨$⟩ˡ 0F)))) + toℕ (b P.⟨$⟩ˡ 0F)

------------------------------------------------------------------------
-- 2. Word-length bookkeeping.

length-liftW : (w : Word n) → length (liftW w) ≡ length w
length-liftW []      = refl
length-liftW (i ∷ w) = cong suc (length-liftW w)

length-rotateW : (m : Fin (suc n)) → length (rotateW m) ≡ toℕ m
length-rotateW         0F       = refl
length-rotateW {suc n} (fsuc m) =
  cong suc (trans (length-liftW (rotateW m)) (length-rotateW m))

------------------------------------------------------------------------
-- 3. L2:  `canonW` is reduced — its length is exactly `inv`.

opaque
  unfolding inv
  canonW-length : (b : FinBij (suc n) (suc n)) → length (canonW b) ≡ inv b
  canonW-length {zero}  b = refl
  canonW-length {suc n} b =
    trans (length-++ (liftW (canonW rest)) {rotateW m})
          (cong₂ _+_ (trans (length-liftW (canonW rest)) (canonW-length rest))
                     (length-rotateW m))
    where
    m : Fin (suc (suc n))
    m    = b P.⟨$⟩ˡ 0F
    rest : FinBij (suc n) (suc n)
    rest = remove 0F (b ∘-fb inv-fb (rotate-fb m))
