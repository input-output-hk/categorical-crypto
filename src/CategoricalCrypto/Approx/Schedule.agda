{-# OPTIONS --safe --without-K #-}

-- Schedule-valued errors, and allowance reindexing as a control
-- (`docs/quantitative-uc-setup-plan.typ` §7.1, §7.2).
--
-- `Approx` is already generic in its error structure, so §7's "generalize to a
-- fixed ordered additive commutative monoid `V`" asks for an INSTANCE rather
-- than a second category: the schedules the resource-aware layer needs are
-- `pointwise ℕ ℚ-ordered` in the closure allowance and
-- `pointwise ℕ (pointwise ℕ ℚ-ordered)` at a family's level and allowance.
-- Signed rationals are kept — `ℚ-ordered` is `ℚ`, not `ℚ≥0`, the domain the
-- existing bounds are stated over (`UC.Approximate.GradedBound`).
--
-- Substituting an allowance is the control `ε ∘ ρ`, and it is EXACT — both its
-- zero and its additivity law hold by reflexivity — so the schedule
-- substitutions the existing composition theorems perform
-- (`UC.Model.Family.Contextual.Compose`'s
-- `λ n q → ε n (scale q (cost c n))`) are instances of composing controlled
-- maps, not a UC-specific axiom.

open import Data.Product.Base using (_,_; proj₁; proj₂)
open import Level using (Level; _⊔_)
open import Relation.Binary.PropositionalEquality using (_≡_; cong; isEquivalence; refl; subst)

open import CategoricalCrypto.Approx.Error using (OrderedErrorAlgebra; Refinement)

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

pointwise-refinement : {i es ℓe : Level} (I : Set i) (V : OrderedErrorAlgebra es ℓe)
                     → Refinement V → Refinement (pointwise I V)
pointwise-refinement I V R = record
  { Positive = λ ε → (j : I) → Positive (ε j)
  ; ε₀-least = λ pos j → ε₀-least (pos j)
  ; refine   = λ pos → let r = λ j → refine (pos j) in
        (λ j → proj₁ (r j)) , (λ j → proj₁ (proj₂ (r j)))
      , (λ j → proj₁ (proj₂ (proj₂ (r j)))) , (λ j → proj₁ (proj₂ (proj₂ (proj₂ (r j)))))
      , λ j → proj₂ (proj₂ (proj₂ (proj₂ (r j))))
  }
  where open Refinement R

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

  -- …and reindexing composes by composing the substitutions, the outer one
  -- applied first (plan §7.2's `φρ₂(φρ₁(ε)) = ε ∘ ρ₁ ∘ ρ₂`).
  reindex-∘ : (ρ₁ ρ₂ : I → I) (ε : I → V.Error)
            → Control.at (reindex ρ₂ ∘ᶜ reindex ρ₁) ε
            ≡ Control.at (reindex (λ k → ρ₁ (ρ₂ k))) ε
  reindex-∘ _ _ _ = refl
