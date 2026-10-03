{-# OPTIONS --safe --without-K #-}

-- Errors, closeness at an error, and the all-positive collapse of closeness.
--
-- `OrderedErrorAlgebra` is what finite-error reasoning spends and no more: a
-- preorder, a monotone sum, and `ε₀` a unit up to `⊑` in the one direction —
-- two zero-error identifications compose back to zero error, and a fixed bound
-- survives a zero-error change of either endpoint (`≈[]-resp₀`).  It is NOT an
-- ordered monoid: no consumer spends associativity, commutativity or the
-- converse unit bounds, the lax direction keeps an upper-bound model
-- admissible (`Approx.Controlled`'s resource-sensitive maps), and schedule
-- errors (`Approx.Schedule.pointwise`) are antisymmetric only up to pointwise
-- equality.
--
-- `_∼ᵃ_`, closeness at EVERY positive error, is the qualitative equivalence
-- closeness collapses to, and positivity is spent there alone, so it is a
-- separate `Refinement` of the errors; the ε/2 argument for its transitivity
-- is proved once, here.  The existential collapse at a class of small errors
-- needs no refinement at all (`Approx.Small`).

open import Data.Nat.Base as ℕ using (ℕ)
open import Data.Product.Base
open import Data.Rational as ℚ using (ℚ; 0ℚ; ½; ∣_∣)
open import Data.Rational.Properties.Ext
open import Level
open import Relation.Binary.Bundles
open import Relation.Binary.Definitions
open import Relation.Binary.PropositionalEquality
open import Relation.Binary.Structures

import Data.Nat.Properties as ℕₚ
import Data.Rational.Properties as ℚₚ

module CategoricalCrypto.Approx.Error where

private variable os es ℓe ℓa : Level

------------------------------------------------------------------------
-- Errors and closeness

record OrderedErrorAlgebra (es ℓe : Level) : Set (suc (es ⊔ ℓe)) where
  infixl 6 _⊕_
  infix 4 _⊑_

  field
    Error        : Set es
    ε₀           : Error
    _⊕_          : Error → Error → Error
    _⊑_          : Error → Error → Set ℓe
    ⊑-isPreorder : IsPreorder _≡_ _⊑_
    ⊕-mono       : Monotonic₂ _⊑_ _⊑_ _⊑_ _⊕_
    ⊕-identityˡ  : {ε : Error} → ε₀ ⊕ ε ⊑ ε
    ⊕-identityʳ  : {ε : Error} → ε ⊕ ε₀ ⊑ ε

  open IsPreorder ⊑-isPreorder public using () renaming (refl to ⊑-refl; trans to ⊑-trans)

  ⊑-preorder : Preorder es es ℓe
  ⊑-preorder = record { isPreorder = ⊑-isPreorder }

record Approximation (Obs : Set os) (E : OrderedErrorAlgebra es ℓe) (ℓa : Level)
                   : Set (os ⊔ es ⊔ ℓe ⊔ suc ℓa) where
  open OrderedErrorAlgebra E public

  infix 4 _≈[_]_

  field
    _≈[_]_    : Obs → Error → Obs → Set ℓa
    ≈[]-refl  : {x : Obs} → x ≈[ ε₀ ] x
    ≈[]-sym   : {x y : Obs} {ε : Error} → x ≈[ ε ] y → y ≈[ ε ] x
    ≈[]-trans : {x y z : Obs} {ε δ : Error} → x ≈[ ε ] y → y ≈[ δ ] z → x ≈[ ε ⊕ δ ] z
    ≈[]-mono  : {x y : Obs} {ε δ : Error} → ε ⊑ δ → x ≈[ ε ] y → x ≈[ δ ] y

module _ (E : OrderedErrorAlgebra es ℓe) {Obs : Set os} (A : Approximation Obs E ℓa) where
  open Approximation A

  ≈[]-resp₀ : {x x′ y y′ : Obs} {ε : Error}
            → x′ ≈[ ε₀ ] x → y ≈[ ε₀ ] y′ → x ≈[ ε ] y → x′ ≈[ ε ] y′
  ≈[]-resp₀ l r h = ≈[]-mono (⊑-trans (⊕-mono ⊕-identityˡ ⊑-refl) ⊕-identityʳ)
                             (≈[]-trans (≈[]-trans l h) r)

-- Closeness at every index past a threshold of `κ`.  `κ` should be cofinal: a
-- bounded `κ` makes every eventual statement true.
module _ {E : OrderedErrorAlgebra es ℓe} {Obs : Set os} (A : Approximation Obs E ℓa) where
  open Approximation A

  Eventually : (Ix : Set) → (Ix → ℕ) → Approximation (Ix → Obs) E ℓa
  Eventually Ix κ = record
    { _≈[_]_    = λ μ ε ν → Σ[ N ∈ ℕ ] ((i : Ix) → N ℕ.≤ κ i → μ i ≈[ ε ] ν i)
    ; ≈[]-refl  = 0 , λ _ _ → ≈[]-refl
    ; ≈[]-sym   = λ (N , h) → N , λ i le → ≈[]-sym (h i le)
    ; ≈[]-trans = λ (N₁ , h₁) (N₂ , h₂) → N₁ ℕ.⊔ N₂ , λ i le →
        ≈[]-trans (h₁ i (ℕₚ.≤-trans (ℕₚ.m≤m⊔n N₁ N₂) le)) (h₂ i (ℕₚ.≤-trans (ℕₚ.m≤n⊔m N₁ N₂) le))
    ; ≈[]-mono  = λ le (N , h) → N , λ i le′ → ≈[]-mono le (h i le′)
    }

------------------------------------------------------------------------
-- The all-positive collapse

-- Tolerances small enough to collapse at: each positive one lies above zero and
-- splits into two positive ones whose sum is below it.  That split is the
-- whole ε/2 argument.
record Refinement (E : OrderedErrorAlgebra es ℓe) : Set (es ⊔ suc ℓe) where
  open OrderedErrorAlgebra E

  field
    Positive : Error → Set ℓe
    ε₀-least : {ε : Error} → Positive ε → ε₀ ⊑ ε
    refine   : {ε : Error} → Positive ε
             → Σ[ δ ∈ Error ] Σ[ δ′ ∈ Error ] Positive δ × Positive δ′ × δ ⊕ δ′ ⊑ ε

-- No positive error separates the two.  This is the relation a qualitative
-- observation exposes; at the asymptotic instance it is vanishing advantage.
module AllPositive {E : OrderedErrorAlgebra es ℓe} (R : Refinement E)
                   {Obs : Set os} (A : Approximation Obs E ℓa) where
  open Refinement R
  open Approximation A

  infix 4 _∼ᵃ_

  _∼ᵃ_ : Obs → Obs → Set (es ⊔ ℓe ⊔ ℓa)
  x ∼ᵃ y = (ε : Error) → Positive ε → x ≈[ ε ] y

  ∼ᵃ-isEquivalence : IsEquivalence _∼ᵃ_
  ∼ᵃ-isEquivalence = record
    { refl  = λ _ pos → ≈[]-mono (ε₀-least pos) ≈[]-refl
    ; sym   = λ h ε pos → ≈[]-sym (h ε pos)
    ; trans = λ h k ε pos →
        let δ , δ′ , pδ , pδ′ , le = refine pos in ≈[]-mono le (≈[]-trans (h δ pδ) (k δ′ pδ′))
    }

  zero⇒positive : {x y : Obs} → x ≈[ ε₀ ] y → x ∼ᵃ y
  zero⇒positive h _ pos = ≈[]-mono (ε₀-least pos) h

------------------------------------------------------------------------
-- Instances

ℚ-ordered : OrderedErrorAlgebra 0ℓ 0ℓ
ℚ-ordered = record
  { Error        = ℚ
  ; ε₀           = 0ℚ
  ; _⊕_          = ℚ._+_
  ; _⊑_          = ℚ._≤_
  ; ⊑-isPreorder = ℚₚ.≤-isPreorder
  ; ⊕-mono       = ℚₚ.+-mono-≤
  ; ⊕-identityˡ  = λ {ε} → ℚₚ.≤-reflexive (ℚₚ.+-identityˡ ε)
  ; ⊕-identityʳ  = λ {ε} → ℚₚ.≤-reflexive (ℚₚ.+-identityʳ ε)
  }

-- ℚ at its own metric.  An `Approximation` alone never bounds a gap from
-- below (the relation identifying everything satisfies the laws); this
-- instance does (`≈ᵐ-gap`), which is what a NEGATIVE closeness statement needs.
infix 4 _≈ᵐ[_]_

_≈ᵐ[_]_ : ℚ → ℚ → ℚ → Set
x ≈ᵐ[ ε ] y = ∣ x ℚ.- y ∣ ℚ.≤ ε

ℚ-metric : Approximation ℚ ℚ-ordered 0ℓ
ℚ-metric = record
  { _≈[_]_    = _≈ᵐ[_]_
  ; ≈[]-refl  = λ {x} → ℚₚ.≤-reflexive (∣x-x∣≡0 x)
  ; ≈[]-sym   = λ {x} {y} → subst (ℚ._≤ _) (∣-∣-comm x y)
  ; ≈[]-trans = λ {x} {y} {z} h k → ℚₚ.≤-trans (∣-∣-triangle x y z) (ℚₚ.+-mono-≤ h k)
  ; ≈[]-mono  = λ le h → ℚₚ.≤-trans h le
  }

≈ᵐ-0 : {x : ℚ} → 0ℚ ℚ.≤ x → x ≈ᵐ[ x ] 0ℚ
≈ᵐ-0 {x} 0≤x = ℚₚ.≤-reflexive (trans (cong ∣_∣ (ℚₚ.+-identityʳ x)) (ℚₚ.0≤p⇒∣p∣≡p 0≤x))

≈ᵐ-gap : {x ε : ℚ} → x ≈ᵐ[ ε ] 0ℚ → x ℚ.≤ ε
≈ᵐ-gap {x} h = ℚₚ.≤-trans (ℚₚ.≤-trans (p≤∣p∣ x) (ℚₚ.≤-reflexive (cong ∣_∣ (sym (ℚₚ.+-identityʳ x))))) h

ℚ-refinement : Refinement ℚ-ordered
ℚ-refinement = record
  { Positive = 0ℚ ℚ.<_
  ; ε₀-least = ℚₚ.<⇒≤
  ; refine   = λ {ε} pos → ½ ℚ.* ε , ½ ℚ.* ε , 0<½* pos , 0<½* pos , ℚₚ.≤-reflexive (½*+½* ε)
  }

-- Counts: the finite-error layer at an instance with nothing to halve.  A
-- positive count below `1` does not split (`Approx.FilteredTests.ℕ-unrefinable`).
ℕ-ordered : OrderedErrorAlgebra 0ℓ 0ℓ
ℕ-ordered = record
  { Error        = ℕ
  ; ε₀           = 0
  ; _⊕_          = ℕ._+_
  ; _⊑_          = ℕ._≤_
  ; ⊑-isPreorder = ℕₚ.≤-isPreorder
  ; ⊕-mono       = ℕₚ.+-mono-≤
  ; ⊕-identityˡ  = ℕₚ.≤-refl
  ; ⊕-identityʳ  = λ {n} → ℕₚ.≤-reflexive (ℕₚ.+-identityʳ n)
  }
