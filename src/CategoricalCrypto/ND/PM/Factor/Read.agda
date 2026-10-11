{-# OPTIONS --safe --without-K --guardedness #-}

open import Categories.Category.Monoidal.Bundle
import Categories.Morphism as Mor

open import Data.List.Base using (List; []; _++_)

open import CategoricalCrypto.ND.PM.Factor
open import CategoricalCrypto.ND.PM.Read
import CategoricalCrypto.ND.Grade as Grade
open import CategoricalCrypto.UC.Model.Seal
open import CategoricalCrypto.UC.Model.Symmetric
open import CategoricalCrypto.UC.Model.Wire

module CategoricalCrypto.ND.PM.Factor.Read where

private
  module G = SymmetricMonoidalCategory 𝔾ˢ
  module B = Grade 𝔾ˢ C

open Mor G.U
open import Categories.Morphism.Reasoning G.U
open G.HomReasoning
open B using (C⟦_⟧)

flat : (S⃗ : List Set) → Flat C⟦ S⃗ ⟧
flat S⃗ = record { iface = Cᶠ S⃗ ; iso = ψ S⃗ }

reads-C++ : (S⃗ T⃗ : List Set) → Reads (flat S⃗ ⊗ᶠ flat T⃗) (flat (S⃗ ++ T⃗)) (B.C++.from S⃗ T⃗) (joinᶠ S⃗ T⃗)
reads-C++ = ψ-C++

reads-C++⁻¹ : (S⃗ T⃗ : List Set) → Reads (flat (S⃗ ++ T⃗)) (flat S⃗ ⊗ᶠ flat T⃗) (B.C++.to S⃗ T⃗) (splitᶠ S⃗ T⃗)
reads-C++⁻¹ S⃗ T⃗ = pullʳ (ψ-C++⁻¹ S⃗ T⃗) ○ cancelˡ (_≅_.isoʳ (⊗ᵒ≅ (Cᶠ S⃗) (Cᶠ T⃗)))

reads-nil : Reads unitᶠ (flat []) G.id nilᶠ
reads-nil = G.identityʳ

reads-nil⁻¹ : Reads (flat []) unitᶠ G.id nilᶠ⁻¹
reads-nil⁻¹ = G.identityʳ ○ ⟺ (pullˡ (⟺ (procᵒ-∘ nilᶠ⁻¹ nilᶠ) ○ ≈ᴹ⇒≈ᵒ nil-isoˡ ○ procᵒ-id) ○ G.identityˡ)
