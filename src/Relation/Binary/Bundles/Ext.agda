{-# OPTIONS --safe --without-K #-}

open import Level
open import Relation.Binary.Bundles using (Setoid)

module Relation.Binary.Bundles.Ext where

private variable c ℓ : Level

-- `agda-categories`' `𝒞 [ f ≈ g ]`, for setoids: naming the setoid lets a
-- statement quantify over the equality it is taken at.
infix 4 _⟨_≈_⟩
_⟨_≈_⟩ : (A : Setoid c ℓ) → Setoid.Carrier A → Setoid.Carrier A → Set ℓ
_⟨_≈_⟩ = Setoid._≈_
