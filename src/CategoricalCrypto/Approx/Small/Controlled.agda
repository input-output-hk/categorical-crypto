{-# OPTIONS --safe --without-K #-}

-- The small-error collapse on controlled maps
-- (`docs/quantitative-uc-setup-plan.typ` §8).
--
-- A nonexpansive map preserves `∼Small` outright (`Approx.Small.FSmall`); a
-- CONTROLLED map does so only when its control preserves the class, so the
-- collapse is taken on the wide subcategory `SmallPreserving` cuts out rather
-- than on `Ctrl`.  For the negligible class the qualifying reindexings are the
-- polynomial-preserving ones (`UC.Approximate.GradedBound-reindex`).

open import Categories.Category using (Category)
open import Categories.Category.Instance.Setoids using (Setoids)
open import Categories.Functor using (Functor)

open import Data.Product.Base using (_,_)
open import Level using (Level; _⊔_)

open import CategoricalCrypto.Approx.Error using (OrderedErrorAlgebra)

module CategoricalCrypto.Approx.Small.Controlled
  {es ℓe : Level} (E : OrderedErrorAlgebra es ℓe) where

open OrderedErrorAlgebra E
open import CategoricalCrypto.Approx.Controlled E
open import CategoricalCrypto.Approx.Small E
open import CategoricalCrypto.Approx.Space E

module CollapseControlled {ℓs : Level} (S : SmallClass ℓs) (c ℓa : Level) where

  open import Categories.Category.SubCategory (Ctrl c ℓa)
  open Collapse S c ℓa

  SmallPreserving : Control → Set (es ⊔ ℓs)
  SmallPreserving φ = {ε : Error} → Small ε → Small (Control.at φ ε)

  smallSub : SubCat (ApproxSpace c ℓa)
  smallSub = record
    { U    = λ X → X
    ; R    = λ f → SmallPreserving (Controlled.control f)
    ; Rid  = λ s → s
    ; _∘R_ = λ pf pg s → pf (pg s)
    }

  CtrlSmall : Category _ _ _
  CtrlSmall = SubCategory smallSub

  FSmallᶜ : Functor CtrlSmall (Setoids c (es ⊔ ℓs ⊔ ℓa))
  FSmallᶜ = record
    { F₀ = smallSetoid
    ; F₁ = λ (f , pres) → record
        { to = Controlled.map f
        ; cong = λ (ε , sε , h) →
            Control.at (Controlled.control f) ε , pres sε , Controlled.preserves f h }
    ; identity     = λ {A} → ∼Small-refl A
    ; homomorphism = λ {_} {_} {Z} → ∼Small-refl Z
    ; F-resp-≈     = λ {_} {B} (_ , me) {x} → ε₀ , small-ε₀ , me x
    }
