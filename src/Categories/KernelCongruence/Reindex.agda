{-# OPTIONS --safe --without-K #-}

open import Categories.Category
open import Categories.Functor

module Categories.KernelCongruence.Reindex
  {ob ℓb eb oc ℓc ec od ℓd ed}
  {B : Category ob ℓb eb} {C : Category oc ℓc ec} {D : Category od ℓd ed}
  (H : Functor B C) (F : Functor C D) where

import Categories.KernelCongruence as KernelCong

private
  module B = Category B
  module H = Functor H
  module KF = KernelCong C D F
  module K∘ = KernelCong B D (F ∘F H)
  variable
    X Y : B.Obj
    f g : B [ X , Y ]

∼⇒∼∘ : H.₁ f KF.∼ H.₁ g → f K∘.∼ g
∼⇒∼∘ e = K∘.mk∼ (KF.run∼ e)

∼∘⇒∼ : f K∘.∼ g → H.₁ f KF.∼ H.₁ g
∼∘⇒∼ e = KF.mk∼ (K∘.run∼ e)
