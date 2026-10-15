{-# OPTIONS --safe --without-K #-}

module CategoricalCrypto.UCSetup.Coverage where

open import Data.Product.Base
open import Function.Bundles
open import Level

open import CategoricalCrypto.Abstract2.Morphism
open import CategoricalCrypto.UCSetup
open import CategoricalCrypto.UCSetup.Morphism

private variable
  o ℓ e oc ℓc ec o′ ℓ′ e′ oc′ ℓc′ ec′ cs ℓs : Level

module _ {𝕊 : UCSetup o ℓ e oc ℓc ec cs ℓs}
         {𝕊′ : UCSetup o′ ℓ′ e′ oc′ ℓc′ ec′ cs ℓs}
         (M : UCSetupMorphism 𝕊 𝕊′) where
  private
    module S = UCSetup 𝕊
    module T = UCSetup 𝕊′
  open UCSetupMorphism M

  -- Density concerns arbitrary target arrows, not just compiled arrows.
  -- The compiler and its naturality are the existing presheaf morphism ν.
  record TestCoverage : Set (oc ⊔ oc′ ⊔ ℓc′ ⊔ cs ⊔ ℓs) where
    field complete : ∀ {A B} {h k : A T.𝒞.⇒ F.₀ B}
                   → ((t : S.Env B) → T.pull h (ν.η B ⟨$⟩ t) T.Env.≈ T.pull k (ν.η B ⟨$⟩ t))
                   → (t : T.Env (F.₀ B)) → T.pull h t T.Env.≈ T.pull k t

  epi⇒TestCoverage : ν.Epi → TestCoverage
  epi⇒TestCoverage epi = record { complete = λ {A} {B} {h} {k} agree t →
    let s , eq = epi t in
    T.Env.trans (T.Env.sym (T.pull-cong h eq)) (T.Env.trans (agree s) (T.pull-cong k eq)) }

  covered-≈ℰ : TestCoverage → Transfer.Preserves-≈ℰ M
  covered-≈ℰ coverage {f = f} {g} eq = T.KE.mk∼ λ {t} →
    TestCoverage.complete coverage (λ s →
      T.Env.trans (ν.sym-commute f)
        (T.Env.trans (Func.cong (ν.η _) (S.KE.run∼ eq {s})) (ν.commute g))) t
