{-# OPTIONS --safe --without-K #-}

open import Function.Base
open import Function.Bundles
open import Level
open import Relation.Binary.Bundles
open import Relation.Binary.PropositionalEquality
open import Relation.Binary.PropositionalEquality.Properties using () renaming (setoid to ≡-setoid)

module Function.Bundles.Ext where

private variable a b ℓ : Level

-- A map out of a discrete setoid is a setoid map for free.
discreteFunc : {A : Set a} {S : Setoid b ℓ} → (A → Setoid.Carrier S) → Func (≡-setoid A) S
discreteFunc {S = S} f = record { to = f ; cong = Setoid.reflexive S ∘ cong f }
