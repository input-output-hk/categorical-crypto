{-# OPTIONS --safe #-}

module LibExt where

open import categorical-crypto.Prelude
open import Relation.Binary

-- Equivalence and Setoid structure for the extentional equality

IsEquivalence-≗ : ∀ {a b} {A : Set a} {B : Set b}
  → IsEquivalence (_≗_ {A = A} {B = B})
IsEquivalence-≗ = record
   { refl = λ _ → refl
   ; sym = λ x≗y → sym ∘ x≗y
   ; trans = λ i≗j j≗k l → trans (i≗j l) (j≗k l)
   }

≗-setoid : ∀ {a b} {A : Set a} {B : Set b} → Setoid _ _
≗-setoid {A = A} {B} = record
  { Carrier = A → B
  ; _≈_ = _
  ; isEquivalence = IsEquivalence-≗ }
