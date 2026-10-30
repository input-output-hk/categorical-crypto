{-# OPTIONS --safe --without-K #-}

open import Categories.Category.Monoidal.Bundle
import Categories.Category.Monoidal.Distributive as MD

module Categories.Category.Monoidal.Distributive.Properties
  {o ℓ e} (𝒱 : SymmetricMonoidalCategory o ℓ e)
  (dist : MD.MonoidalDistributive 𝒱) where

open SymmetricMonoidalCategory 𝒱
open MD.MonoidalDistributive dist

open import Categories.Category.Monoidal.Reasoning monoidal
open import Categories.Morphism.Reasoning U

private variable A B X Y : Obj

δ-unique : {u v : X ⊗₀ (A + B) ⇒ Y}
         → u ∘ id ⊗₁ i₁ ≈ v ∘ id ⊗₁ i₁ → u ∘ id ⊗₁ i₂ ≈ v ∘ id ⊗₁ i₂ → u ≈ v
δ-unique e₁ e₂ = insertʳ distributeˡ.isoʳ
               ○ (∘-distribˡ-[] ○ []-cong₂ e₁ e₂ ○ ⟺ ∘-distribˡ-[]) ⟩∘⟨refl
               ○ cancelʳ distributeˡ.isoʳ

δ⇐-i₁ : δ⇐ ∘ id ⊗₁ i₁ ≈ i₁ {X ⊗₀ A} {X ⊗₀ B}
δ⇐-i₁ = (refl⟩∘⟨ ⟺ inject₁) ○ cancelˡ distributeˡ.isoˡ

δ⇐-i₂ : δ⇐ ∘ id ⊗₁ i₂ ≈ i₂ {X ⊗₀ A} {X ⊗₀ B}
δ⇐-i₂ = (refl⟩∘⟨ ⟺ inject₂) ○ cancelˡ distributeˡ.isoˡ

[]-δ⇐ : {S A₁ A₂ B₁ B₂ : Obj} {p : S ⊗₀ B₁ ⇒ Y} {t : S ⊗₀ B₂ ⇒ Y}
        (r : A₁ ⇒ B₁) (s : A₂ ⇒ B₂)
      → [ p , t ] ∘ δ⇐ ∘ id ⊗₁ (r +₁ s) ≈ [ p ∘ id ⊗₁ r , t ∘ id ⊗₁ s ] ∘ δ⇐
[]-δ⇐ r s =
  δ-unique (pullʳ (pullʳ (merge₂ʳ ○ (refl⟩⊗⟨ +₁∘i₁) ○ ⟺ merge₂ʳ)) ○ (refl⟩∘⟨ pullˡ δ⇐-i₁)
              ○ pullˡ inject₁ ○ ⟺ (pullʳ δ⇐-i₁ ○ inject₁))
           (pullʳ (pullʳ (merge₂ʳ ○ (refl⟩⊗⟨ +₁∘i₂) ○ ⟺ merge₂ʳ)) ○ (refl⟩∘⟨ pullˡ δ⇐-i₂)
              ○ pullˡ inject₂ ○ ⟺ (pullʳ δ⇐-i₂ ○ inject₂))

⊥-unique : {u v : X ⊗₀ ⊥ ⇒ Y} → u ≈ v
⊥-unique = ⟺ inject₁ ○ (refl⟩∘⟨ i-collapse) ○ inject₂
  where
    i-collapse : i₁ ≈ i₂
    i-collapse = ⟺ δ⇐-i₁ ○ (refl⟩∘⟨ (refl⟩⊗⟨ ¡-unique₂ i₁ i₂)) ○ δ⇐-i₂
