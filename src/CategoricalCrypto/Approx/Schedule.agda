{-# OPTIONS --safe --without-K #-}

-- Schedule-valued errors, and allowance reindexing as a control.
--
-- `Approx` is already generic in its error structure, so schedule-valued
-- errors are an INSTANCE rather than a second category: the instances in use are `pointwise ℕ ℚ-ordered` over
-- the security parameter and `pointwise ℕ⁺ ℚ-ordered` over closure rates
-- (`UC.Quantitative.Query.Sched`).
--
-- Substituting an allowance is the control `ε ∘ ρ`, and it is EXACT — both its
-- zero and its additivity law hold by reflexivity — so the schedule
-- substitutions the existing composition theorems perform
-- (`UC.Quantitative.Family`'s
-- `λ n q → ε n (scale q (schedOf s n))`) are instances of composing controlled
-- maps, not a UC-specific axiom.

open import Data.Product.Base
open import Level
open import Relation.Binary.PropositionalEquality

open import CategoricalCrypto.Approx.Error

module CategoricalCrypto.Approx.Schedule where

pointwise : {i es ℓe : Level} (I : Set i) → OrderedErrorAlgebra es ℓe
          → OrderedErrorAlgebra (i ⊔ es) (i ⊔ ℓe)
pointwise I V = record
  { Error        = I → Error
  ; ε₀           = λ _ → ε₀
  ; _⊕_          = λ ε δ j → ε j ⊕ δ j
  ; _⊑_          = λ ε δ → (j : I) → ε j ⊑ δ j
  ; ⊑-isPreorder = record
      { isEquivalence = isEquivalence
      ; reflexive     = λ { refl _ → ⊑-refl }
      ; trans         = λ le₁ le₂ j → ⊑-trans (le₁ j) (le₂ j)
      }
  ; ⊕-mono       = λ le₁ le₂ j → ⊕-mono (le₁ j) (le₂ j)
  ; ⊕-identityˡ  = λ _ → ⊕-identityˡ
  ; ⊕-identityʳ  = λ _ → ⊕-identityʳ
  }
  where open OrderedErrorAlgebra V

module Reindexing {i es ℓe : Level} {I : Set i} (V : OrderedErrorAlgebra es ℓe) where

  open import CategoricalCrypto.Approx.Controlled (pointwise I V)

  private module V = OrderedErrorAlgebra V

  reindex : (ρ : I → I) → Control
  reindex ρ = record
    { homomorphism = record
        { ⟦_⟧ = λ ε j → ε (ρ j)
        ; isOrderHomomorphism = record { cong = cong λ ε j → ε (ρ j) ; mono = λ le j → le (ρ j) }
        }
    ; preserves-ε₀ = λ _ → V.⊑-refl
    ; preserves-⊕  = λ _ → V.⊑-refl
    }

  -- Substitutions agreeing at every allowance reindex the same way.  This is
  -- how a model's own allowance identity becomes a control equality — the
  -- query model's three presheaf laws are each one instance
  -- (`UC.Quantitative.Query.Qᵠ`).
  reindex-cong : {ρ₁ ρ₂ : I → I} → ((j : I) → ρ₁ j ≡ ρ₂ j) → reindex ρ₁ ≐ᶜ reindex ρ₂
  reindex-cong {ρ₁} eq = (λ ε j → subst (ε (ρ₁ j) V.⊑_) (cong ε (eq j)) V.⊑-refl)
                       , λ ε j → subst (V._⊑ ε (ρ₁ j)) (cong ε (eq j)) V.⊑-refl
