{-# OPTIONS --safe --without-K #-}

module Data.Sum.Ext where

open import Data.Empty
open import Data.Sum
open import Level

private variable a : Level
                 A : Set a

-- `Data.Sum.Algebra.⊎-identityˡ`/`-identityʳ` bury these inside `↔` bundles, at
-- `Data.Empty.Polymorphic.⊥`.

unitˡ⇒ : ⊥ ⊎ A → A
unitˡ⇒ (inj₂ a) = a

unitʳ⇒ : A ⊎ ⊥ → A
unitʳ⇒ (inj₁ a) = a
