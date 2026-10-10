{-# OPTIONS --safe --without-K #-}

-- `Abstract2.Regrade` by `refl`: the pulled-back structure is 𝕊's at ι, and at
-- ι = id `inclusion` is `idᵁ 𝕊` field by field and ≤UC crosses both ways
-- (cf. `Abstract2.WideSubcategory.Trivial`).

open import Level

open import CategoricalCrypto.UCSetup

module CategoricalCrypto.Abstract2.Regrade.Pin
  {o ℓ e o′ ℓ′ e′ cs ℓs : Level} (𝕊 : UCSetup o ℓ e o′ ℓ′ e′ cs ℓs) where

open import Data.Product
open import Relation.Binary.PropositionalEquality

open import Categories.Category.Monoidal
open import Categories.Functor.Monoidal
open import Categories.Functor.Monoidal.Properties
import Categories.Morphism as Mor

open import CategoricalCrypto.Abstract2
import CategoricalCrypto.Abstract2.Regrade as Regrade
open import CategoricalCrypto.UCSetup.Morphism

open AbstractUC 𝕊

private variable
  A B : 𝒞.Obj
  X Y : ℐ.Obj

module _ {oⱼ ℓⱼ eⱼ : Level} {𝒥 : MonoidalCategory oⱼ ℓⱼ eⱼ} (ι : MonoidalFunctor 𝒥 ℐ) where
  open Regrade 𝕊 ι
  private
    module 𝒥 = MonoidalCategory 𝒥
    module ι = MonoidalFunctor ι

  T₀-pin : ∀ {X A} → R.T₀ X A ≡ T₀ (ι.₀ X) A
  T₀-pin = refl

  sub-pin : ∀ {X Y A} (c : X 𝒥.⇒ Y) → R.sub c {A} ≡ sub (ι.₁ c)
  sub-pin _ = refl

  return-pin : ∀ {A} → R.return {A} ≡ sub ι.ε 𝒞.∘ return
  return-pin = refl

  μ-pin : ∀ {W X A} → R.μ W X {A} ≡ sub (ι₂ W X) 𝒞.∘ μ (ι.₀ W) (ι.₀ X)
  μ-pin = refl

open Regrade 𝕊 (idF-Monoidal ℐ)

private
  module I = UCSetupMorphism inclusion
  module 𝟙 = UCSetupMorphism (idᵁ 𝕊)

F-pin : I.F ≡ 𝟙.F
F-pin = refl

Φ-pin : I.Φ ≡ 𝟙.Φ
Φ-pin = refl

κ-pin : ∀ {X A} → I.κ {X} {A} ≡ 𝟙.κ
κ-pin = refl

ν-pin : ∀ {A} → I.ν.η A ≡ 𝟙.ν.η A
ν-pin = refl

module Trivial where
  open Preserves ℐ.id ℐ.identity²

  to : {f : A 𝒞.⇒ T₀ X B} {g : A 𝒞.⇒ T₀ Y B} → f ≤UC g → f R.≤UC g
  to = restrict-≤UC (λ s → s , ℐ.Equiv.refl)

  from : {f : A 𝒞.⇒ T₀ X B} {g : A 𝒞.⇒ T₀ Y B} → f R.≤UC g → f ≤UC g
  from = unrestrict-≤UC (λ W → W , Mor.≅.refl ℐ.U)
