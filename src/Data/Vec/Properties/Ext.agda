{-# OPTIONS --safe --without-K #-}

------------------------------------------------------------------------
-- Extensions to `Data.Vec.Properties`.
------------------------------------------------------------------------

module Data.Vec.Properties.Ext where

open import Data.Nat.Base using (ℕ; _+_)
open import Data.Vec.Base using (Vec; _++_; take; drop)
open import Data.Vec.Properties using (take++drop≡id)
open import Level using (Level)
open import Relation.Binary.PropositionalEquality using (_≡_; sym; trans; cong₂)

private variable
  a : Level
  A : Set a
  n : ℕ

-- A vector is determined by its take/drop split at any position.
take-drop-inj : ∀ (m : ℕ) (u v : Vec A (m + n))
              → take m u ≡ take m v → drop m u ≡ drop m v → u ≡ v
take-drop-inj m u v et ed =
  trans (sym (take++drop≡id m u)) (trans (cong₂ _++_ et ed) (take++drop≡id m v))
