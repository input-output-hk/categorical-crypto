{-# OPTIONS --safe --without-K #-}

-- The two unit maps of `_⊎_`: `⊥` contributes no case.  `Data.Sum.Algebra`
-- has them only inside an `↔` bundle.

module Data.Sum.Ext where

open import Data.Empty using (⊥)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Level using (Level)

private variable a : Level
                 A : Set a

unitˡ⇒ : ⊥ ⊎ A → A
unitˡ⇒ (inj₂ a) = a

unitʳ⇒ : A ⊎ ⊥ → A
unitʳ⇒ (inj₁ a) = a
