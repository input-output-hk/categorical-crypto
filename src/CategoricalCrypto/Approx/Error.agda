{-# OPTIONS --safe --without-K #-}

-- What a CATEGORY of approximate spaces costs of its errors.  No positivity:
-- the all-positive collapse takes its `Refinement` separately (`Approx.Forget`).
--
-- Composition needs the errors to be ordered and unital: two zero-error
-- identifications must compose back to zero error, a fixed bound must survive a
-- zero-error change of either endpoint, and a bound built from two others must
-- be weakenable in both arguments.
--
-- None of that is needed as an EQUATION: `⊑` in the one direction suffices
-- throughout, which is what keeps a lax or upper-bound model admissible (the
-- resource extension of `docs/quantitative-uc-setup-plan.typ` §7 needs that).

open import Data.Nat.Base as ℕ using (ℕ)
open import Data.Product.Base using (_,_)
open import Data.Rational.Properties
  using (+-identityʳ; +-identityˡ; +-mono-≤; ≤-refl; ≤-reflexive; ≤-trans)
open import Level using (Level; 0ℓ; suc; _⊔_)
open import Relation.Nullary using (¬_)

open import CategoricalCrypto.UC.Approximate
  using (Approximation; ErrorAlgebra; Refinement; ℚ-errors)

import Data.Nat.Properties as ℕₚ

module CategoricalCrypto.Approx.Error where

record OrderedErrorAlgebra (es ℓe : Level) : Set (suc (es ⊔ ℓe)) where
  field errors : ErrorAlgebra es ℓe

  open ErrorAlgebra errors public

  field
    ⊑-refl      : {ε : Error} → ε ⊑ ε
    ⊑-trans     : {ε δ γ : Error} → ε ⊑ δ → δ ⊑ γ → ε ⊑ γ
    ⊕-identityˡ : {ε : Error} → ε₀ ⊕ ε ⊑ ε
    ⊕-identityʳ : {ε : Error} → ε ⊕ ε₀ ⊑ ε
    ⊕-mono      : {ε ε′ δ δ′ : Error} → ε ⊑ ε′ → δ ⊑ δ′ → ε ⊕ δ ⊑ ε′ ⊕ δ′

ℚ-ordered : OrderedErrorAlgebra 0ℓ 0ℓ
ℚ-ordered = record
  { errors      = ℚ-errors
  ; ⊑-refl      = ≤-refl
  ; ⊑-trans     = ≤-trans
  ; ⊕-identityˡ = λ {ε} → ≤-reflexive (+-identityˡ ε)
  ; ⊕-identityʳ = λ {ε} → ≤-reflexive (+-identityʳ ε)
  ; ⊕-mono      = +-mono-≤
  }

-- Counts: the finite-error layer at an instance with nothing to halve.  A
-- positive count below `1` does not split (`ℕ-unrefinable`).
ℕ-ordered : OrderedErrorAlgebra 0ℓ 0ℓ
ℕ-ordered = record
  { errors      = record { Error = ℕ ; ε₀ = 0 ; _⊕_ = ℕ._+_ ; _⊑_ = ℕ._≤_ }
  ; ⊑-refl      = ℕₚ.≤-refl
  ; ⊑-trans     = ℕₚ.≤-trans
  ; ⊕-identityˡ = ℕₚ.≤-refl
  ; ⊕-identityʳ = λ {n} → ℕₚ.≤-reflexive (ℕₚ.+-identityʳ n)
  ; ⊕-mono      = ℕₚ.+-mono-≤
  }

ℕ-unrefinable : (R : Refinement (OrderedErrorAlgebra.errors ℕ-ordered))
              → ({n : ℕ} → Refinement.Positive R n → 0 ℕ.< n) → ¬ Refinement.Positive R 1
ℕ-unrefinable R pos⇒ p1 = let _ , _ , pδ , pδ′ , le = Refinement.refine R p1
  in ℕₚ.1+n≰n (ℕₚ.≤-trans (ℕₚ.+-mono-≤ (pos⇒ pδ) (pos⇒ pδ′)) le)

-- The second law of the header, as its users spend it: a bound survives a
-- zero-error change of either endpoint.
module _ {es ℓe os ℓa : Level} (E : OrderedErrorAlgebra es ℓe) {Obs : Set os}
         (A : Approximation Obs (OrderedErrorAlgebra.errors E) ℓa) where
  open OrderedErrorAlgebra E using (⊑-refl; ⊑-trans; ⊕-identityˡ; ⊕-identityʳ; ⊕-mono)
  open Approximation A using (Error; ε₀; _≈[_]_; ≈[]-mono; ≈[]-trans)

  ≈[]-resp₀ : {x x′ y y′ : Obs} {ε : Error}
            → x′ ≈[ ε₀ ] x → y ≈[ ε₀ ] y′ → x ≈[ ε ] y → x′ ≈[ ε ] y′
  ≈[]-resp₀ l r h = ≈[]-mono (⊑-trans (⊕-mono ⊕-identityˡ ⊑-refl) ⊕-identityʳ)
                             (≈[]-trans (≈[]-trans l h) r)
