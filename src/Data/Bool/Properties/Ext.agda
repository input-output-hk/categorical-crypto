{-# OPTIONS --safe --without-K #-}

-- `Data.Bool.Properties` has no `_≤_`-monotonicity lemmas, nor `∨-idemˡ`.

open import Data.Bool.Base
open import Data.Bool.Properties
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

module Data.Bool.Properties.Ext where

private variable a b c d : Bool

∨-mono-≤ : a ≤ b → c ≤ d → a ∨ c ≤ b ∨ d
∨-mono-≤ f≤t          _  = ≤-maximum _
∨-mono-≤ (b≤b {true})  _ = b≤b
∨-mono-≤ (b≤b {false}) cd = cd

a≤b⇒a≤b∨c : a ≤ b → a ≤ b ∨ c
a≤b⇒a≤b∨c f≤t           = ≤-maximum _
a≤b⇒a≤b∨c (b≤b {true})  = b≤b
a≤b⇒a≤b∨c (b≤b {false}) = ≤-minimum _

∨-idemˡ : (a b : Bool) → a ∨ (a ∨ b) ≡ a ∨ b
∨-idemˡ false _ = refl
∨-idemˡ true  _ = refl
