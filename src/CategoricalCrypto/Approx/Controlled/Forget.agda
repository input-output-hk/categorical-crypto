{-# OPTIONS --safe --without-K #-}

-- Zero-error forgetting of controlled maps
-- (`docs/quantitative-uc-setup-plan.typ` §7.2, last paragraph).
--
-- `Control.preserves-ε₀` is the whole of its content: an ε₀-comparison is
-- carried to an `at φ ε₀`-comparison, which is one again.  Composing this with
-- a controlled presheaf gives an ordinary `UCSetup`, so the resource-aware
-- theory can spend `Abstract2.Action`'s presheaf laws as exact zero-error
-- steps, exactly as the nonexpansive theory does through `Approx.Forget.F₀`.

open import Categories.Category.Instance.Setoids using (Setoids)
open import Categories.Functor using (Functor)

open import Data.Product.Base using (_,_)
open import Level using (Level)

open import CategoricalCrypto.Approx.Error using (OrderedErrorAlgebra)

module CategoricalCrypto.Approx.Controlled.Forget
  {es ℓe : Level} (E : OrderedErrorAlgebra es ℓe) where

open OrderedErrorAlgebra E
open import CategoricalCrypto.Approx.Controlled E
open import CategoricalCrypto.Approx.Space E

F₀ᶜ : (c ℓa : Level) → Functor (Ctrl c ℓa) (Setoids c ℓa)
F₀ᶜ c ℓa = record
  { F₀ = zeroSetoid
  ; F₁ = λ {_} {B} f → record
      { to   = Controlled.map f
      ; cong = λ h → ApproxSpace.≈[]-mono B
          (Control.preserves-ε₀ (Controlled.control f)) (Controlled.preserves f h)
      }
  ; identity     = λ {A} → ApproxSpace.≈[]-refl A
  ; homomorphism = λ {_} {_} {Z} → ApproxSpace.≈[]-refl Z
  ; F-resp-≈     = λ (_ , me) {x} → me x
  }
