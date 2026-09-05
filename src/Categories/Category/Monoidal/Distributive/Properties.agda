{-# OPTIONS --safe --without-K #-}

-- One letter of the distributor.  `δ-unique` is the lever that replaces the
-- coproduct side's coherence chains: a map out of a distributed sum is its two
-- branches, so a ⊕-side equation is a pair of branch goals.

open import Categories.Category.Monoidal.Bundle
import Categories.Category.Monoidal.Distributive as MD

module Categories.Category.Monoidal.Distributive.Properties
  {o ℓ e} (𝒱 : SymmetricMonoidalCategory o ℓ e)
  (dist : MD.MonoidalDistributive 𝒱) where

open SymmetricMonoidalCategory 𝒱
open Equiv
open MD.MonoidalDistributive dist

open import Categories.Category.Monoidal.Reasoning monoidal
open import Categories.Morphism.Reasoning U

private variable A B X Y : Obj

δ-unique : {u v : X ⊗₀ (A + B) ⇒ Y}
         → u ∘ id ⊗₁ i₁ ≈ v ∘ id ⊗₁ i₁ → u ∘ id ⊗₁ i₂ ≈ v ∘ id ⊗₁ i₂ → u ≈ v
δ-unique e₁ e₂ = insertʳ distributeˡ.isoʳ
               ○ (∘-distribˡ-[] ○ []-cong₂ e₁ e₂ ○ ⟺ ∘-distribˡ-[]) ⟩∘⟨refl
               ○ cancelʳ distributeˡ.isoʳ

δ⇐-i₁ : δ⇐ ∘ id {X} ⊗₁ i₁ ≈ i₁ {X ⊗₀ A} {X ⊗₀ B}
δ⇐-i₁ = (refl⟩∘⟨ ⟺ inject₁) ○ cancelˡ distributeˡ.isoˡ

δ⇐-i₂ : δ⇐ ∘ id {X} ⊗₁ i₂ ≈ i₂ {X ⊗₀ A} {X ⊗₀ B}
δ⇐-i₂ = (refl⟩∘⟨ ⟺ inject₂) ○ cancelˡ distributeˡ.isoˡ

private
  -- `[ id , id ] : ⊥ + ⊥ ⇒ ⊥` is an iso, its inverse `i₁`, because maps out of
  -- the initial object are unique.
  ⊥+⊥-isoˡ : i₁ ∘ [ id {⊥} , id ] ≈ id
  ⊥+⊥-isoˡ = ⟺ (+-unique (pullʳ inject₁ ○ identityʳ)
                         (pullʳ inject₂ ○ identityʳ ○ ¡-unique₂ i₁ i₂)) ○ +-η

  ψ : (X ⊗₀ ⊥) + (X ⊗₀ ⊥) ⇒ X ⊗₀ ⊥
  ψ = id ⊗₁ [ id , id ] ∘ δ⇒

  ψ-isoˡ : (δ⇐ ∘ id ⊗₁ i₁) ∘ ψ {X} ≈ id
  ψ-isoˡ = center (merge₂ʳ ○ refl⟩⊗⟨ ⊥+⊥-isoˡ ○ ⊗.identity)
         ○ (refl⟩∘⟨ identityˡ) ○ distributeˡ.isoˡ

  ψ-i₁ : ψ {X} ∘ i₁ ≈ id
  ψ-i₁ = pullʳ inject₁ ○ merge₂ʳ ○ (refl⟩⊗⟨ inject₁) ○ ⊗.identity

  ψ-i₂ : ψ {X} ∘ i₂ ≈ id
  ψ-i₂ = pullʳ inject₂ ○ merge₂ʳ ○ (refl⟩⊗⟨ inject₂) ○ ⊗.identity

-- Binary distributivity already makes `X ⊗₀ ⊥` initial: the injections of
-- `(X ⊗₀ ⊥) + (X ⊗₀ ⊥)` agree, hence so do any two maps out of `X ⊗₀ ⊥`.
⊥-unique : {u v : X ⊗₀ ⊥ ⇒ Y} → u ≈ v
⊥-unique = ⟺ inject₁ ○ (refl⟩∘⟨ i-collapse) ○ inject₂
  where
    i-collapse : i₁ {X ⊗₀ ⊥} {X ⊗₀ ⊥} ≈ i₂
    i-collapse = insertˡ ψ-isoˡ ○ (refl⟩∘⟨ ψ-i₁) ○ identityʳ
               ○ ⟺ (insertˡ ψ-isoˡ ○ (refl⟩∘⟨ ψ-i₂) ○ identityʳ)
