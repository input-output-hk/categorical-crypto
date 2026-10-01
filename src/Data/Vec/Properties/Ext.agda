{-# OPTIONS --safe --without-K #-}

module Data.Vec.Properties.Ext where

open import Data.Nat.Base
open import Data.Vec.Base
open import Data.Vec.Properties
open import Level
open import Relation.Binary.PropositionalEquality

private variable
  a : Level
  A : Set a
  n : ℕ

take-drop-inj : ∀ (m : ℕ) (u v : Vec A (m + n))
              → take m u ≡ take m v → drop m u ≡ drop m v → u ≡ v
take-drop-inj m u v et ed =
  trans (sym (take++drop≡id m u)) (trans (cong₂ _++_ et ed) (take++drop≡id m v))
