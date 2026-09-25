{-# OPTIONS --safe --without-K #-}

-- Positive naturals, ordered by ≤ with multiplication and unit 1.

module Data.Nat.Positive where

import Algebra.Properties.CommutativeSemigroup as CommSemigroupProperties
open import Algebra.Ordered.Bundles
open import Algebra.Structures
open import Data.Nat
open import Data.Nat.Properties
open import Data.Product
open import Function
open import Level using (0ℓ)
open import Relation.Binary
import Relation.Binary.Construct.On as On
open import Relation.Binary.PropositionalEquality

ℕ⁺ : Set
ℕ⁺ = Σ[ n ∈ ℕ ] 1 ≤ n

value : ℕ⁺ → ℕ
value = proj₁

1⁺ : ℕ⁺
1⁺ = 1 , ≤-refl

infixl 7 _·_

-- `value (r · s) ≡ value r * value s` holds definitionally
_·_ : ℕ⁺ → ℕ⁺ → ℕ⁺
r · s = value r * value s , *-mono-≤ (proj₂ r) (proj₂ s)

≤⁺-poset : Poset 0ℓ 0ℓ 0ℓ
≤⁺-poset = On.poset ≤-poset value

·-1-isCommutativeMonoid : IsCommutativeMonoid (_≡_ on value) _·_ 1⁺
·-1-isCommutativeMonoid = record
  { isMonoid = record
    { isSemigroup = record
      { isMagma = record { isEquivalence = On.isEquivalence value isEquivalence ; ∙-cong = cong₂ _*_ }
      ; assoc   = λ r s t → *-assoc (value r) (value s) (value t)
      }
    ; identity = *-identityˡ ∘ value , *-identityʳ ∘ value
    }
  ; comm = λ r s → *-comm (value r) (value s)
  }

·-1-OrderedCommutativeMonoid : OrderedCommutativeMonoid 0ℓ 0ℓ 0ℓ
·-1-OrderedCommutativeMonoid = record
  { poset = ≤⁺-poset ; _∙_ = _·_ ; ε = 1⁺ ; isCommutativeMonoid = ·-1-isCommutativeMonoid ; ∙-mono = *-mono-≤ }

positive : ℕ → ℕ⁺
positive c = c ⊔ 1 , m≤n⊔m c 1

-- `positive` is not multiplicative at 0; this is what does hold
positive-· : ∀ c d → value (positive c · positive d) ≡ (c ⊔ 1) * (d ⊔ 1)
positive-· c d = refl

scale : ℕ → ℕ⁺ → ℕ
scale q r = q * value r

scale-zero : ∀ r → scale 0 r ≡ 0
scale-zero r = refl

scale-unit : ∀ q → scale q 1⁺ ≡ q
scale-unit = *-identityʳ
