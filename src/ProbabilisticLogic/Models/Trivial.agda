{-# OPTIONS --safe --without-K #-}

-- The trivial 1-element model of `Abstract`.
--
-- All probabilities are `tt`, so 0 = 1 and the ring is degenerate.
-- This is a sanity check that the axioms are consistent.

open import categorical-crypto.Prelude

open import Class.HasOrder
open import Algebra
open import Algebra.Structures

open import ProbabilisticLogic.Abstract

module ProbabilisticLogic.Models.Trivial where

private
  Carrierᵀ : Type
  Carrierᵀ = ⊤

  ⊤-IsCommutativeSemiring : IsCommutativeSemiring
    {A = Carrierᵀ} _≡_ (λ _ _ → tt) (λ _ _ → tt) tt tt
  ⊤-IsCommutativeSemiring = record
    { isSemiring = record
      { isSemiringWithoutAnnihilatingZero = record
        { +-isCommutativeMonoid = record
          { isMonoid = record
            { isSemigroup = record
              { isMagma = record
                { isEquivalence = isEquivalence
                ; ∙-cong = λ _ _ → refl
                }
              ; assoc = λ _ _ _ → refl
              }
            ; identity = (λ _ → refl) , (λ _ → refl)
            }
          ; comm = λ _ _ → refl
          }
        ; *-cong = λ _ _ → refl
        ; *-assoc = λ _ _ _ → refl
        ; *-identity = (λ _ → refl) , (λ _ → refl)
        ; distrib = (λ _ _ _ → refl) , (λ _ _ _ → refl)
        }
      ; zero = (λ _ → refl) , (λ _ → refl)
      }
    ; *-comm = λ _ _ → refl
    }

  ⊤-CommutativeSemiring : CommutativeSemiring 0ℓ 0ℓ
  ⊤-CommutativeSemiring = record { isCommutativeSemiring = ⊤-IsCommutativeSemiring }

  -- The trivial preorder/partial order on ⊤ via _≡_.
  ⊤-HasPreorder : HasPreorder {A = Carrierᵀ} {_≈_ = _≡_}
  ⊤-HasPreorder = record
    { _≤_           = _≡_
    ; _<_           = λ _ _ → ⊥
    ; ≤-isPreorder  = isPreorder
    ; <-irrefl      = λ _ ()
    ; ≤⇔<∨≈         = mk⇔ inj₂ (λ { (inj₁ ()) ; (inj₂ x) → x })
    }
    where open import Relation.Binary.PropositionalEquality
            using (isPreorder)
          open import Function.Bundles using (mk⇔)

  ⊤-HasPartialOrder : HasPartialOrder {A = Carrierᵀ} {_≈_ = _≡_}
  ⊤-HasPartialOrder = record
    { hasPreorder = ⊤-HasPreorder
    ; ≤-antisym = λ p _ → p
    }

Triv-AbstractProbability : AbstractProbability 0ℓ 0ℓ
Triv-AbstractProbability = record
  { Probabilityᴿ                  = ⊤-CommutativeSemiring
  ; _⁻¹                           = λ _ _ → tt
  ; d                             = λ _ _ → tt
  ; HasPartialOrder-Probability   = ⊤-HasPartialOrder
  ; ≤-cong                        = λ _ _ → refl
  ; +-mono-≤                      = λ _ _ → refl
  ; +-cancelʳ-≤                   = λ _ → refl
  ; fromℚ                         = λ _ → tt
  ; fromℚ-isSemiringHomomorphism  = record
      { isNearSemiringHomomorphism = record
          { +-isMonoidHomomorphism = record
              { isMagmaHomomorphism = record
                  { isRelHomomorphism = record { cong = λ _ → refl }
                  ; homo = λ _ _ → refl
                  }
              ; ε-homo = refl
              }
          ; *-homo = λ _ _ → refl
          }
      ; 1#-homo = refl
      }
  }

Triv : Abstract 0ℓ 0ℓ
Triv = record
  { abstractProbability = Triv-AbstractProbability
  ; ProbDistr           = λ _ → ⊤
  ; _∙_                 = λ _ _ → tt
  ; _∣_                 = λ _ _ → tt
  ; P∅≈0                = refl
  ; PU≈1                = refl
  ; P-distrib-disjoint  = λ _ → refl
  ; cond-probability    = refl
  ; prob-monotonous     = λ _ → refl
  ; ∣-cong              = λ _ → refl
  ; empirical           = λ _ → tt
  ; empirical-eq        = refl
  ; cond-empirical      = λ _ → refl
  ; _⊗_                 = λ _ _ → tt
  ; ⊗-rect              = refl
  }
