{-# OPTIONS --safe --without-K #-}

-- Errors, closeness at an error, and the all-positive collapse of closeness.
--
-- `OrderedErrorAlgebra` is what finite-error reasoning spends and no more: a
-- preorder, a monotone sum, and `ε₀` a unit up to `⊑` in the one direction —
-- two zero-error identifications compose back to zero error, and a fixed bound
-- survives a zero-error change of either endpoint (`≈[]-resp₀`).  It is NOT an
-- ordered monoid: no consumer spends associativity, commutativity or the
-- converse unit bounds, the lax direction keeps an upper-bound model
-- admissible (the resource extension of `docs/quantitative-uc-setup-plan.typ`
-- §7), and schedule errors (`Approx.Schedule.pointwise`) are antisymmetric only
-- up to pointwise equality.
--
-- `_∼ᵃ_`, closeness at EVERY positive error, is the qualitative equivalence
-- closeness collapses to, and positivity is spent there alone, so it is a
-- separate `Refinement` of the errors; the ε/2 argument for its transitivity
-- is proved once, here.  The existential collapse at a class of small errors
-- needs no refinement at all (`Approx.Small`).

open import Data.Nat.Base as ℕ using (ℕ)
open import Data.Product.Base using (Σ-syntax; _×_; _,_)
open import Data.Rational as ℚ using (ℚ; 0ℚ; ½)
open import Data.Rational.Properties.Ext using (0<½*; ½*+½*)
open import Level using (Level; 0ℓ; suc; _⊔_)
open import Relation.Binary.Bundles using (Preorder; Setoid)
open import Relation.Binary.Definitions using (Monotonic₂)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Relation.Binary.Structures using (IsEquivalence; IsPreorder)
open import Relation.Nullary using (¬_)

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

------------------------------------------------------------------------
-- The all-positive collapse

-- Tolerances small enough to collapse at: each positive one lies above zero and
-- splits into two positive ones whose sum is below it.  That split is the
-- whole ε/2 argument; `halving` is the usual way to supply it.
record Refinement (E : OrderedErrorAlgebra es ℓe) : Set (es ⊔ suc ℓe) where
  open OrderedErrorAlgebra E

  field
    Positive : Error → Set ℓe
    ε₀-least : {ε : Error} → Positive ε → ε₀ ⊑ ε
    refine   : {ε : Error} → Positive ε
             → Σ[ δ ∈ Error ] Σ[ δ′ ∈ Error ] Positive δ × Positive δ′ × δ ⊕ δ′ ⊑ ε

module _ {E : OrderedErrorAlgebra es ℓe} where
  open OrderedErrorAlgebra E

  halving : (Positive : Error → Set ℓe) → ({ε : Error} → Positive ε → ε₀ ⊑ ε)
          → (half : Error → Error) → ({ε : Error} → Positive ε → Positive (half ε))
          → ((ε : Error) → half ε ⊕ half ε ⊑ ε) → Refinement E
  halving Positive ε₀-least half half-pos half-sum = record
    { Positive = Positive
    ; ε₀-least = ε₀-least
    ; refine   = λ {ε} pos → half ε , half ε , half-pos pos , half-pos pos , half-sum ε
    }

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

  positiveSetoid : Setoid os (es ⊔ ℓe ⊔ ℓa)
  positiveSetoid = record { Carrier = Obs ; _≈_ = _∼ᵃ_ ; isEquivalence = ∼ᵃ-isEquivalence }

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

ℚ-refinement : Refinement ℚ-ordered
ℚ-refinement = halving (0ℚ ℚ.<_) ℚₚ.<⇒≤ (½ ℚ.*_) 0<½* (λ ε → ℚₚ.≤-reflexive (½*+½* ε))

-- Counts: the finite-error layer at an instance with nothing to halve.  A
-- positive count below `1` does not split (`ℕ-unrefinable`).
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

ℕ-unrefinable : (R : Refinement ℕ-ordered)
              → ({n : ℕ} → Refinement.Positive R n → 0 ℕ.< n) → ¬ Refinement.Positive R 1
ℕ-unrefinable R pos⇒ p1 = let _ , _ , pδ , pδ′ , le = Refinement.refine R p1
  in ℕₚ.1+n≰n (ℕₚ.≤-trans (ℕₚ.+-mono-≤ (pos⇒ pδ) (pos⇒ pδ′)) le)
