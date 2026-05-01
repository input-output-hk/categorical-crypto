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

  ⊤-IsCommutativeRing : IsCommutativeRing
    {A = Carrierᵀ} _≡_ (λ _ _ → tt) (λ _ _ → tt) (λ _ → tt) tt tt
  ⊤-IsCommutativeRing = record
    { isRing = record
      { +-isAbelianGroup = record
        { isGroup = record
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
          ; inverse = (λ _ → refl) , (λ _ → refl)
          ; ⁻¹-cong = λ _ → refl
          }
        ; comm = λ _ _ → refl
        }
      ; *-cong = λ _ _ → refl
      ; *-assoc = λ _ _ _ → refl
      ; *-identity = (λ _ → refl) , (λ _ → refl)
      ; distrib = (λ _ _ _ → refl) , (λ _ _ _ → refl)
      }
    ; *-comm = λ _ _ → refl
    }

  ⊤-CommutativeRing : CommutativeRing 0ℓ 0ℓ
  ⊤-CommutativeRing = record { isCommutativeRing = ⊤-IsCommutativeRing }

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

Triv-AbstractProbability : AbstractProbability
Triv-AbstractProbability = record
  { Probabilityᴿ                  = ⊤-CommutativeRing
  ; _⁻¹                           = λ _ → tt
  ; d                             = λ _ _ → tt
  ; HasPartialOrder-Probability   = ⊤-HasPartialOrder
  ; ≤-cong                        = λ _ _ → refl
  ; +-mono-≤                      = λ _ _ → refl
  ; +-cancelʳ-≤                   = λ _ → refl
  ; fromℚ                         = λ _ → tt
  ; fromℚ-homomorphism            = refl
  }

Triv : Abstract
Triv = record
  { abstractProbability = Triv-AbstractProbability
  ; ProbDistr           = λ _ → ⊤
  ; _∙_                 = λ _ _ → tt
  ; _∣_                 = λ _ _ → tt
  ; extend              = λ _ → tt
  ; P∅≈0                = refl
  ; PU≤1                = refl
  ; P-distrib-disjoint  = λ _ → refl
  ; cond-probability    = refl
  ; prob-monotonous     = λ _ → refl
  ; extend-∣            = refl
  ; extend-∣-cong       = λ _ → refl
  ; uniformFromList     = λ _ → tt
  ; uniform-eq          = refl
  ; cond-uniform        = λ _ → refl
  ; ∩-bound             = refl
  }
