{-# OPTIONS --safe --without-K #-}

-- Monotonicity of `_∨_` in the Boolean order, which `Data.Bool.Properties`
-- states for every other operation but not this one.

open import Data.Bool.Base using (Bool; true; false; _∨_; _≤_; f≤t; b≤b)
open import Data.Bool.Properties using (≤-maximum; ≤-minimum)

module Data.Bool.Properties.Ext where

private variable a b c d : Bool

∨-mono : a ≤ b → c ≤ d → a ∨ c ≤ b ∨ d
∨-mono f≤t          _  = ≤-maximum _
∨-mono (b≤b {true})  _ = b≤b
∨-mono (b≤b {false}) cd = cd

∨-monoʳ : a ≤ b → a ≤ b ∨ c
∨-monoʳ f≤t           = ≤-maximum _
∨-monoʳ (b≤b {true})  = b≤b
∨-monoʳ (b≤b {false}) = ≤-minimum _
