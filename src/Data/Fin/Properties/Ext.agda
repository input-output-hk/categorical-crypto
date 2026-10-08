{-# OPTIONS --safe --without-K #-}

module Data.Fin.Properties.Ext where

open import Data.Empty using (⊥)
open import Data.Fin.Base using (Fin; _↑ˡ_; _↑ʳ_; splitAt)
open import Data.Fin.Properties using (splitAt-↑ˡ; splitAt-↑ʳ)
open import Relation.Binary.PropositionalEquality using (_≡_; trans; sym; cong)

↑ˡ≢↑ʳ : ∀ {m n} (i : Fin m) (j : Fin n) → i ↑ˡ n ≡ m ↑ʳ j → ⊥
↑ˡ≢↑ʳ {m} {n} i j eq
  with trans (sym (splitAt-↑ˡ m i n)) (trans (cong (splitAt m) eq) (splitAt-↑ʳ m n j))
... | ()
