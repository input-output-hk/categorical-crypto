{-# OPTIONS --safe --without-K #-}

-- 𝕊 restricted along the unit `Oneᴹ → ℐ` (`Graded.Trivial.unitᴹ`): one ancilla
-- and one simulator, both the unit (`docs/uc-setup-nondeterministic.md`
-- §1.3(e)).  When `return` is split — a standard setup's is λ⇐, split by λ⇒ —
-- the prefix context is the protocol followed by the splitting, so ≤UC along
-- the unit is ≈ℰ.

open import Level

open import CategoricalCrypto.UCSetup

module CategoricalCrypto.Abstract2.Regrade.Unit
  {o ℓ e o′ ℓ′ e′ cs ℓs : Level} (𝕊 : UCSetup o ℓ e o′ ℓ′ e′ cs ℓs) where

open import Data.Product.Base
open import Function.Bundles

open import Categories.Functor.Monoidal
open import Categories.Monad.Graded.Trivial

open import CategoricalCrypto.Abstract2
import CategoricalCrypto.Abstract2.Regrade as Regrade

open AbstractUC 𝕊

module U = Regrade 𝕊 (StrongMonoidalFunctor.monoidalFunctor (unitᴹ {o′ = 0ℓ} {ℓ′ = 0ℓ} {e′ = 0ℓ} ℐ))

private variable A B : 𝒞.Obj

module _ (split : ∀ {A} → T₀ ℐ.unit A 𝒞.⇒ A)
         (return∘split : ∀ {A} → return 𝒞.∘ split 𝒞.≈ 𝒞.id {T₀ ℐ.unit A}) where

  ≈ℰ⇒≈ᵁ|𝟙 : {f g : A 𝒞.⇒ T₀ ℐ.unit B} → f ≈ℰ g → f U.R.≈ᵁ g
  ≈ℰ⇒≈ᵁ|𝟙 {f = f} {g} e _ =
    ≈ℰ-trans (≈C⇒≈ℰ (after f)) (≈ℰ-trans (≈ℰ-cong-pre split e) (≈ℰ-sym (≈C⇒≈ℰ (after g))))
    where
      open 𝒞
      after : (h : A ⇒ T₀ ℐ.unit B) → U.R.μ _ _ ∘ U.R.T₁ _ h ≈ h ∘ split
      after h = introʳ return∘split ○ sym-assoc ○ (assoc ⟩∘⟨refl ○ assoc) ⟩∘⟨refl
              ○ (refl⟩∘⟨ unit-comp h) ⟩∘⟨refl ○ λ-cancel h ⟩∘⟨refl

  ≤UC|𝟙⇔≈ℰ : {f g : A 𝒞.⇒ T₀ ℐ.unit B} → f U.R.≤UC g ⇔ f ≈ℰ g
  ≤UC|𝟙⇔≈ℰ {f = f} {g} = mk⇔ {A = f U.R.≤UC g}
    (λ le → let _ , e = U.R.≤UC⇒dummy le in ≈ℰ-trans (U.R.≈ᵁ⇒≈ℰ e) (≈C⇒≈ℰ (sub-identityˡ g)))
    (λ e → U.R.dummy-complete (_ , ≈ℰ⇒≈ᵁ|𝟙 (≈ℰ-trans e (≈ℰ-sym (≈C⇒≈ℰ (sub-identityˡ g))))))
