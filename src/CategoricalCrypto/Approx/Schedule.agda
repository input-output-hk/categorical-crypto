{-# OPTIONS --safe --without-K #-}

-- Schedule-valued errors, and allowance reindexing as a control
-- (`docs/quantitative-uc-setup-plan.typ` §7.1, §7.2).
--
-- `Approx` is already generic in its error structure, so §7's "generalize to a
-- fixed ordered additive commutative monoid `V`" asks for an INSTANCE rather
-- than a second category: `pointwise I V` is the index-wise structure, and the
-- schedules the resource-aware layer needs are `pointwise ℕ ℚ-ordered` in the
-- closure allowance and `pointwise ℕ (pointwise ℕ ℚ-ordered)` at a family's
-- level and allowance.  Signed rationals are kept — `ℚ-ordered` is `ℚ`, not
-- `ℚ≥0`, which is the domain the existing bounds are stated over
-- (`UC.Approximate.GradedBound`).
--
-- `reindex` is the point of the module.  Substituting an allowance is the
-- control `ε ∘ ρ`, and it is EXACT — both its zero and its additivity law hold
-- by reflexivity — so the schedule substitutions the existing composition
-- theorems perform (`UC.Asymptotic.Compose`'s `λ n q → ε n (simCost q (cost c n))`)
-- are instances of composing controlled maps, not a UC-specific axiom.

open import Level using (Level; _⊔_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import CategoricalCrypto.Approx.Error using (OrderedErrorAlgebra)

module CategoricalCrypto.Approx.Schedule where

pointwise : {i es ℓe : Level} (I : Set i) → OrderedErrorAlgebra es ℓe
          → OrderedErrorAlgebra (i ⊔ es) (i ⊔ ℓe)
pointwise I V = record
  { errors = record
      { Error    = I → Error
      ; ε₀       = λ _ → ε₀
      ; _⊕_      = λ ε δ j → ε j ⊕ δ j
      ; _⊑_      = λ ε δ → (j : I) → ε j ⊑ δ j
      ; Positive = λ ε → (j : I) → Positive (ε j)
      ; half     = λ ε j → half (ε j)
      ; ε₀-least = λ pos j → ε₀-least (pos j)
      ; half-pos = λ pos j → half-pos (pos j)
      ; half-sum = λ ε j → half-sum (ε j)
      }
  ; ⊑-refl      = λ _ → ⊑-refl
  ; ⊑-trans     = λ le₁ le₂ j → ⊑-trans (le₁ j) (le₂ j)
  ; ⊕-identityˡ = λ _ → ⊕-identityˡ
  ; ⊕-identityʳ = λ _ → ⊕-identityʳ
  ; ⊕-mono      = λ le₁ le₂ j → ⊕-mono (le₁ j) (le₂ j)
  }
  where open OrderedErrorAlgebra V

module Reindexing {i es ℓe : Level} {I : Set i} (V : OrderedErrorAlgebra es ℓe) where

  open import CategoricalCrypto.Approx.Controlled (pointwise I V)

  private
    module V = OrderedErrorAlgebra V
    module P = OrderedErrorAlgebra (pointwise I V)

  reindex : (ρ : I → I) → Control
  reindex ρ = record
    { at           = λ ε j → ε (ρ j)
    ; preserves-ε₀ = λ _ → V.⊑-refl
    ; preserves-⊕  = λ _ → V.⊑-refl
    ; monotone     = λ le j → le (ρ j)
    }

  -- …and reindexing composes by composing the substitutions, the outer one
  -- applied first (plan §7.2's `φρ₂(φρ₁(ε)) = ε ∘ ρ₁ ∘ ρ₂`).
  reindex-∘ : (ρ₁ ρ₂ : I → I) (ε : P.Error)
            → Control.at (reindex ρ₂ ∘ᶜ reindex ρ₁) ε
            ≡ Control.at (reindex (λ k → ρ₁ (ρ₂ k))) ε
  reindex-∘ _ _ _ = refl
