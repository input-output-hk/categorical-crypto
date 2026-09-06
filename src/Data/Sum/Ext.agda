{-# OPTIONS --safe --without-K #-}

-- The unit and associativity maps of `_⊎_`: `⊥` contributes no case.
-- `Data.Sum.Algebra` has them only inside an `↔` bundle.

module Data.Sum.Ext where

open import Data.Empty using (⊥)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Level using (Level)

private variable a : Level
                 A P Q R : Set a

unitˡ⇒ : ⊥ ⊎ A → A
unitˡ⇒ (inj₂ a) = a

unitʳ⇒ : A ⊎ ⊥ → A
unitʳ⇒ (inj₁ a) = a

⊎assocˡ : P ⊎ (Q ⊎ R) → (P ⊎ Q) ⊎ R
⊎assocˡ (inj₁ p)        = inj₁ (inj₁ p)
⊎assocˡ (inj₂ (inj₁ q)) = inj₁ (inj₂ q)
⊎assocˡ (inj₂ (inj₂ r)) = inj₂ r

⊎assocʳ : (P ⊎ Q) ⊎ R → P ⊎ (Q ⊎ R)
⊎assocʳ (inj₁ (inj₁ p)) = inj₁ p
⊎assocʳ (inj₁ (inj₂ q)) = inj₂ (inj₁ q)
⊎assocʳ (inj₂ r)        = inj₂ (inj₂ r)
