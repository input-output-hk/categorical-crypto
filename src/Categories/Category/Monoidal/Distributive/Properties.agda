{-# OPTIONS --safe --without-K #-}

open import Categories.Category.Monoidal.Bundle
import Categories.Category.Cocartesian.Ext as CE
import Categories.Category.Monoidal.Distributive as MD
import Categories.Category.Monoidal.Utilities as MonoidalUtilities

module Categories.Category.Monoidal.Distributive.Properties {o ℓ e}
  (𝒱 : SymmetricMonoidalCategory o ℓ e) (dist : MD.MonoidalDistributive 𝒱) where

open SymmetricMonoidalCategory 𝒱
open MD.MonoidalDistributive dist
open MonoidalUtilities.Shorthands monoidal
open CE U cocartesian
open import Categories.Category.Monoidal.Reassociation monoidal

open import Categories.Category.Monoidal.Reasoning monoidal
open import Categories.Category.Monoidal.Symmetric.Properties.Ext symmetric
open import Categories.Morphism.Reasoning U

private variable A B C D P Q R S T X Y : Obj

δ-unique : {u v : X ⊗₀ (A + B) ⇒ Y}
         → u ∘ id ⊗₁ i₁ ≈ v ∘ id ⊗₁ i₁ → u ∘ id ⊗₁ i₂ ≈ v ∘ id ⊗₁ i₂ → u ≈ v
δ-unique e₁ e₂ = insertʳ distributeˡ.isoʳ
  ○ (∘-distribˡ-[] ○ []-cong₂ e₁ e₂ ○ ⟺ ∘-distribˡ-[]) ⟩∘⟨refl ○ cancelʳ distributeˡ.isoʳ

δ⇐-i₁ : δ⇐ ∘ id ⊗₁ i₁ ≈ i₁ {X ⊗₀ A} {X ⊗₀ B}
δ⇐-i₁ = refl⟩∘⟨ ⟺ inject₁ ○ cancelˡ distributeˡ.isoˡ

δ⇐-i₂ : δ⇐ ∘ id ⊗₁ i₂ ≈ i₂ {X ⊗₀ A} {X ⊗₀ B}
δ⇐-i₂ = refl⟩∘⟨ ⟺ inject₂ ○ cancelˡ distributeˡ.isoˡ

⊗-[] : (f : A ⇒ C) (g : B ⇒ C) → id {X} ⊗₁ [ f , g ] ≈ [ id ⊗₁ f , id ⊗₁ g ] ∘ δ⇐
⊗-[] f g = δ-unique (merge₂ˡ ○ refl⟩⊗⟨ inject₁ ○ ⟺ (pullʳ δ⇐-i₁ ○ inject₁))
                    (merge₂ˡ ○ refl⟩⊗⟨ inject₂ ○ ⟺ (pullʳ δ⇐-i₂ ○ inject₂))

⊗-+₁ : (f : A ⇒ B) (g : C ⇒ D) → distributeˡ ∘ (id {X} ⊗₁ f +₁ id ⊗₁ g) ∘ δ⇐ ≈ id ⊗₁ (f +₁ g)
⊗-+₁ f g = pullˡ []∘+₁ ○ []-cong₂ merge₂ˡ merge₂ˡ ⟩∘⟨refl ○ ⟺ (⊗-[] (i₁ ∘ f) (i₂ ∘ g))

[]-δ⇐ : {S A₁ A₂ B₁ B₂ : Obj} {p : S ⊗₀ B₁ ⇒ Y} {t : S ⊗₀ B₂ ⇒ Y} (r : A₁ ⇒ B₁) (s : A₂ ⇒ B₂)
      → [ p , t ] ∘ δ⇐ ∘ id ⊗₁ (r +₁ s) ≈ [ p ∘ id ⊗₁ r , t ∘ id ⊗₁ s ] ∘ δ⇐
[]-δ⇐ r s = refl⟩∘⟨ (refl⟩∘⟨ ⟺ (⊗-+₁ r s) ○ cancelˡ distributeˡ.isoˡ) ○ pullˡ []∘+₁

distributeˡ-natural : (θ : X ⇒ Y) → distributeˡ ∘ (θ ⊗₁ id {A} +₁ θ ⊗₁ id {B}) ≈ θ ⊗₁ id ∘ distributeˡ
distributeˡ-natural θ = []∘+₁ ○ []-cong₂ (⟺ whisker-comm) (⟺ whisker-comm) ○ ⟺ ∘-distribˡ-[]

sum-pad : (θ : X ⇒ Y) → distributeˡ ∘ (θ ⊗₁ id {A} +₁ θ ⊗₁ id {B}) ∘ δ⇐ ≈ θ ⊗₁ id
sum-pad θ = pullˡ (distributeˡ-natural θ) ○ cancelʳ distributeˡ.isoʳ

δ⇐-natural : (θ : X ⇒ Y)
           → δ⇐ ∘ θ ⊗₁ id {A + B} ≈ ((θ ⊗₁ id) +₁ (θ ⊗₁ id)) ∘ δ⇐
δ⇐-natural θ = (refl⟩∘⟨ ⟺ (sum-pad θ)) ○ cancelˡ distributeˡ.isoˡ

δ⇐-assoc⇒ : (α⇒ {P} {S} {A} +₁ α⇒ {P} {S} {B}) ∘ δ⇐
            ≈ δ⇐ ∘ id ⊗₁ δ⇐ ∘ α⇒
δ⇐-assoc⇒ = δ-unique
  (pullʳ δ⇐-i₁ ○ +₁∘i₁
    ○ ⟺ (assoc ○ (refl⟩∘⟨ (pullʳ α⇒-id⊗-commute
      ○ pullˡ (merge₂ˡ ○ (refl⟩⊗⟨ δ⇐-i₁)))) ○ pullˡ δ⇐-i₁))
  (pullʳ δ⇐-i₂ ○ +₁∘i₂
    ○ ⟺ (assoc ○ (refl⟩∘⟨ (pullʳ α⇒-id⊗-commute
      ○ pullˡ (merge₂ˡ ○ (refl⟩⊗⟨ δ⇐-i₂)))) ○ pullˡ δ⇐-i₂))

⊥-unique : {u v : X ⊗₀ ⊥ ⇒ Y} → u ≈ v
⊥-unique = ⟺ inject₁
  ○ (refl⟩∘⟨ (⟺ δ⇐-i₁ ○ (refl⟩∘⟨ (refl⟩⊗⟨ ¡-unique₂ i₁ i₂)) ○ δ⇐-i₂)) ○ inject₂

------------------------------------------------------------------------
-- Coproducts of arrows between tensor contexts
------------------------------------------------------------------------

tstep : (X ⊗₀ A ⇒ Y ⊗₀ B) → (X ⊗₀ C ⇒ Y ⊗₀ D) → X ⊗₀ (A + C) ⇒ Y ⊗₀ (B + D)
tstep k l = distributeˡ ∘ (k +₁ l) ∘ δ⇐

tstep-cong : {k k′ : X ⊗₀ A ⇒ Y ⊗₀ B} {l l′ : X ⊗₀ C ⇒ Y ⊗₀ D}
           → k ≈ k′ → l ≈ l′ → tstep k l ≈ tstep k′ l′
tstep-cong e₁ e₂ = refl⟩∘⟨ +₁-cong₂ e₁ e₂ ⟩∘⟨refl

tstep-i₁ : {k : X ⊗₀ A ⇒ Y ⊗₀ B} {l : X ⊗₀ C ⇒ Y ⊗₀ D}
         → tstep k l ∘ id ⊗₁ i₁ ≈ id ⊗₁ i₁ ∘ k
tstep-i₁ = assoc ○ refl⟩∘⟨ (pullʳ δ⇐-i₁ ○ +₁∘i₁) ○ pullˡ inject₁

tstep-i₂ : {k : X ⊗₀ A ⇒ Y ⊗₀ B} {l : X ⊗₀ C ⇒ Y ⊗₀ D}
         → tstep k l ∘ id ⊗₁ i₂ ≈ id ⊗₁ i₂ ∘ l
tstep-i₂ = assoc ○ refl⟩∘⟨ (pullʳ δ⇐-i₂ ○ +₁∘i₂) ○ pullˡ inject₂

tstep-id : tstep (id {X ⊗₀ A}) (id {X ⊗₀ C}) ≈ id
tstep-id = refl⟩∘⟨ elimˡ id+₁id ○ distributeˡ.isoʳ

tstep-∘ : {k₂ : T ⊗₀ B ⇒ X ⊗₀ C} {l₂ : T ⊗₀ Q ⇒ X ⊗₀ R}
          {k₁ : S ⊗₀ A ⇒ T ⊗₀ B} {l₁ : S ⊗₀ P ⇒ T ⊗₀ Q}
        → tstep k₂ l₂ ∘ tstep k₁ l₁ ≈ tstep (k₂ ∘ k₁) (l₂ ∘ l₁)
tstep-∘ = assoc ○ refl⟩∘⟨ assoc ○ refl⟩∘⟨ refl⟩∘⟨ cancelˡ distributeˡ.isoˡ ○ refl⟩∘⟨ pullˡ +₁∘+₁

tstep-sim : {v : X ⇒ Y}
            {k : X ⊗₀ A ⇒ X ⊗₀ B} {k′ : Y ⊗₀ A ⇒ Y ⊗₀ B}
            {l : X ⊗₀ C ⇒ X ⊗₀ D} {l′ : Y ⊗₀ C ⇒ Y ⊗₀ D}
          → v ⊗₁ id ∘ k ≈ k′ ∘ v ⊗₁ id → v ⊗₁ id ∘ l ≈ l′ ∘ v ⊗₁ id
          → v ⊗₁ id ∘ tstep k l ≈ tstep k′ l′ ∘ v ⊗₁ id
tstep-sim {v = v} e₁ e₂ =
  ⟺ (sum-pad v) ⟩∘⟨refl ○ tstep-∘ ○ tstep-cong e₁ e₂ ○ ⟺ tstep-∘ ○ refl⟩∘⟨ sum-pad v

onL-tstep : {k : P ⊗₀ A ⇒ P ⊗₀ B} {l : P ⊗₀ C ⇒ P ⊗₀ D}
          → onL {Q = Q} (tstep k l) ≈ tstep (onL k) (onL l)
onL-tstep = δ-unique (onL-branch tstep-i₁ ○ ⟺ tstep-i₁) (onL-branch tstep-i₂ ○ ⟺ tstep-i₂)

onR-tstep : {k : Q ⊗₀ A ⇒ Q ⊗₀ B} {l : Q ⊗₀ C ⇒ Q ⊗₀ D}
          → onR {P = P} (tstep k l) ≈ tstep (onR k) (onR l)
onR-tstep = δ-unique (onR-branch tstep-i₁ ○ ⟺ tstep-i₁) (onR-branch tstep-i₂ ○ ⟺ tstep-i₂)

private
  ρ-i₁ : id {X} ⊗₁ ⊕.unitorʳ.from {A} ∘ id ⊗₁ i₁ ≈ id
  ρ-i₁ = merge₂ʳ ○ (refl⟩⊗⟨ ⊕.unitorʳ.isoʳ) ○ ⊗.identity

  λ-i₂ : id {X} ⊗₁ ⊕.unitorˡ.from {A} ∘ id ⊗₁ i₂ ≈ id
  λ-i₂ = merge₂ʳ ○ (refl⟩⊗⟨ ⊕.unitorˡ.isoʳ) ○ ⊗.identity

tstep-ρ : {k : X ⊗₀ A ⇒ X ⊗₀ B} {l : X ⊗₀ ⊥ ⇒ X ⊗₀ ⊥}
        → id ⊗₁ ⊕.unitorʳ.from ∘ tstep k l ≈ k ∘ id ⊗₁ ⊕.unitorʳ.from
tstep-ρ = δ-unique (pullʳ tstep-i₁ ○ pullˡ ρ-i₁ ○ identityˡ ○ ⟺ (pullʳ ρ-i₁ ○ identityʳ)) ⊥-unique

tstep-λ : {k : X ⊗₀ ⊥ ⇒ X ⊗₀ ⊥} {l : X ⊗₀ A ⇒ X ⊗₀ B}
        → id ⊗₁ ⊕.unitorˡ.from ∘ tstep k l ≈ l ∘ id ⊗₁ ⊕.unitorˡ.from
tstep-λ = δ-unique ⊥-unique (pullʳ tstep-i₂ ○ pullˡ λ-i₂ ○ identityˡ ○ ⟺ (pullʳ λ-i₂ ○ identityʳ))

tstep-swap : {k : X ⊗₀ A ⇒ Y ⊗₀ B} {l : X ⊗₀ C ⇒ Y ⊗₀ D}
           → id ⊗₁ +-swap ∘ tstep k l ≈ tstep l k ∘ id ⊗₁ +-swap
tstep-swap = δ-unique
  (pullʳ tstep-i₁ ○ pullˡ (merge₂ʳ ○ refl⟩⊗⟨ inject₁) ○ ⟺ (pullʳ (merge₂ʳ ○ refl⟩⊗⟨ inject₁) ○ tstep-i₂))
  (pullʳ tstep-i₂ ○ pullˡ (merge₂ʳ ○ refl⟩⊗⟨ inject₂) ○ ⟺ (pullʳ (merge₂ʳ ○ refl⟩⊗⟨ inject₂) ○ tstep-i₁))
