{-# OPTIONS --safe #-}

module CategoricalCrypto.Machine.Relational.Model where

open import Categories.Category
open import Categories.Category.Monoidal
open import Categories.Category.Monoidal.Construction.Reverse

open import CategoricalCrypto.Machine.Relational.Category
open import CategoricalCrypto.Machine.Relational.Monoidal

𝔾ᴿ : Category _ _ _
𝔾ᴿ = 𝓡

𝔾ᴿˢ : SymmetricMonoidalCategory _ _ _
𝔾ᴿˢ = record { U = 𝔾ᴿ ; monoidal = monoidal ; symmetric = symmetric }

𝔾ᴿᵐ : MonoidalCategory _ _ _
𝔾ᴿᵐ = SymmetricMonoidalCategory.monoidalCategory 𝔾ᴿˢ

-- Machine.UC uses the reverse tensor; the PM-facing target uses the plain one.
𝔾ᴿʳ : MonoidalCategory _ _ _
𝔾ᴿʳ = Reverse-MonoidalCategory 𝔾ᴿᵐ
