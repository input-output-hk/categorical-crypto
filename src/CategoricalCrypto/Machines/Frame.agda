{-# OPTIONS --safe --without-K #-}

-- The coherence library the machine layer runs on: how the two actions of a
-- paired state (`onL`/`onR`) interact with the state shuffles, with each other,
-- and with the point of a paired state.  The only genuinely braided content is
-- that the state braiding exchanges the two actions (`σ-onL`/`σ-onR`): there the
-- braiding crosses a whole block and is split by the hexagon
-- (`Symmetric.Properties.Ext`'s `σ-splitˡ`/`σ-splitʳ`).

open import Categories.Category.Monoidal.Bundle

import Categories.Category.Monoidal.Braided.Properties as BraidedProps
import Categories.Category.Monoidal.Utilities as MonoidalUtilities

open import Data.Product.Base

import CategoricalCrypto.Machines.Core as Core

module CategoricalCrypto.Machines.Frame {o ℓ e} (𝒱 : SymmetricMonoidalCategory o ℓ e) where

open SymmetricMonoidalCategory 𝒱
open BraidedProps.Shorthands braided
open Core 𝒱
open MonoidalUtilities.Shorthands monoidal

open import Categories.Category.Monoidal.Properties monoidal
open import Categories.Category.Monoidal.Properties.Ext monoidal

open import Categories.Category.Monoidal.Reasoning monoidal
open import Categories.Category.Monoidal.Symmetric.Properties.Ext symmetric
open import Categories.Morphism.Reasoning U
open BraidedProps braided
open MonoidalUtilities monoidal

private variable A B P Q R W W′ X Y Z : Obj

-- The reflection frontend wants the `MonoidalCategory` bundle, which the
-- symmetric one projects (`Categories.Category.Monoidal.Bundle`).
𝕄 : MonoidalCategory o ℓ e
𝕄 = monoidalCategory

------------------------------------------------------------------------
-- The two state actions: functoriality and congruence

onL-∘ : {h₂ : P ⊗₀ Y ⇒ P ⊗₀ B} {h₁ : P ⊗₀ X ⇒ P ⊗₀ Y}
      → onL {Q = Q} (h₂ ∘ h₁) ≈ onL h₂ ∘ onL h₁
onL-∘ = (refl⟩∘⟨ split₁ˡ ⟩∘⟨refl) ○ (refl⟩∘⟨ insertInner β-β ⟩∘⟨refl)
      ○ (refl⟩∘⟨ assoc) ○ sym-assoc ○ (refl⟩∘⟨ assoc)

onR-∘ : {T V : Obj} {h₂ : R ⊗₀ Y ⇒ T ⊗₀ V} {h₁ : Q ⊗₀ X ⇒ R ⊗₀ Y}
      → onR {P = P} (h₂ ∘ h₁) ≈ onR h₂ ∘ onR h₁
onR-∘ = (refl⟩∘⟨ split₂ʳ ⟩∘⟨refl) ○ (refl⟩∘⟨ insertInner associator.isoʳ ⟩∘⟨refl)
      ○ (refl⟩∘⟨ assoc) ○ sym-assoc ○ (refl⟩∘⟨ assoc)

onL-cong : {h h′ : P ⊗₀ X ⇒ P ⊗₀ Y} → h ≈ h′ → onL {Q = Q} h ≈ onL h′
onL-cong e = refl⟩∘⟨ e ⟩⊗⟨refl ⟩∘⟨refl

onR-cong : {h h′ : Q ⊗₀ X ⇒ R ⊗₀ Y} → h ≈ h′ → onR {P = P} h ≈ onR h′
onR-cong e = refl⟩∘⟨ refl⟩⊗⟨ e ⟩∘⟨refl

onL-id : onL {Q = Q} (id {P ⊗₀ A}) ≈ id
onL-id = (refl⟩∘⟨ elimˡ ⊗.identity) ○ β-β

onR-id : onR {P = P} (id {Q ⊗₀ A}) ≈ id
onR-id = (refl⟩∘⟨ elimˡ ⊗.identity) ○ associator.isoˡ

onL-str : (g : X ⇒ Y) → onL {Q = Q} (id {P} ⊗₁ g) ≈ id ⊗₁ g
onL-str g = (refl⟩∘⟨ (⟺ (β-natural g))) ○ pullˡ β-β ○ identityˡ

onR-id⊗ : (h : W ⇒ W′) → onR {Q = Q} {P = P} (id ⊗₁ h) ≈ id ⊗₁ h
onR-id⊗ h = pullˡ assoc-commute-to ○ cancelʳ associator.isoˡ ○ (⊗.identity ⟩⊗⟨refl)

onR-⊗id : (h : W ⇒ W′) → onR {P = P} (h ⊗₁ id {X}) ≈ (id ⊗₁ h) ⊗₁ id
onR-⊗id _ = pullˡ assoc-commute-to ○ cancelʳ associator.isoˡ

------------------------------------------------------------------------
-- Both actions carry a square natural in the interface

onL-branch : {k : P ⊗₀ A ⇒ P ⊗₀ B} {t : P ⊗₀ X ⇒ P ⊗₀ Y} {j : A ⇒ X} {j′ : B ⇒ Y}
           → t ∘ id ⊗₁ j ≈ id ⊗₁ j′ ∘ k
           → onL {Q = Q} t ∘ id ⊗₁ j ≈ id ⊗₁ j′ ∘ onL k
onL-branch {j = j} {j′} e = begin
  (β ∘ (_ ⊗₁ id ∘ β)) ∘ id ⊗₁ j        ≈⟨ assoc ○ (refl⟩∘⟨ assoc) ⟩
  β ∘ (_ ⊗₁ id ∘ (β ∘ id ⊗₁ j))        ≈⟨ refl⟩∘⟨ refl⟩∘⟨ β-natural j ⟩
  β ∘ (_ ⊗₁ id ∘ ((id ⊗₁ j) ⊗₁ id ∘ β))
    ≈⟨ refl⟩∘⟨ pullˡ (merge₁ˡ ○ e ⟩⊗⟨refl ○ split₁ˡ) ⟩
  β ∘ (((id ⊗₁ j′) ⊗₁ id ∘ _ ⊗₁ id) ∘ β)
    ≈⟨ refl⟩∘⟨ assoc ○ pullˡ (β-natural′ j′) ○ assoc ⟩
  id ⊗₁ j′ ∘ (β ∘ (_ ⊗₁ id ∘ β))       ∎

onR-branch : {k : Q ⊗₀ A ⇒ Q ⊗₀ B} {t : Q ⊗₀ X ⇒ Q ⊗₀ Y} {j : A ⇒ X} {j′ : B ⇒ Y}
           → t ∘ id ⊗₁ j ≈ id ⊗₁ j′ ∘ k
           → onR {P = P} t ∘ id ⊗₁ j ≈ id ⊗₁ j′ ∘ onR k
onR-branch {j = j} {j′} e = begin
  (α⇐ ∘ (id ⊗₁ _ ∘ α⇒)) ∘ id ⊗₁ j          ≈⟨ assoc ○ (refl⟩∘⟨ assoc) ⟩
  α⇐ ∘ (id ⊗₁ _ ∘ (α⇒ ∘ id ⊗₁ j))
    ≈⟨ refl⟩∘⟨ refl⟩∘⟨ ((refl⟩∘⟨ ((⟺ ⊗.identity) ⟩⊗⟨refl)) ○ assoc-commute-from) ⟩
  α⇐ ∘ (id ⊗₁ _ ∘ (id ⊗₁ (id ⊗₁ j) ∘ α⇒))
    ≈⟨ refl⟩∘⟨ pullˡ (merge₂ʳ ○ refl⟩⊗⟨ e ○ split₂ʳ) ⟩
  α⇐ ∘ ((id ⊗₁ (id ⊗₁ j′) ∘ id ⊗₁ _) ∘ α⇒)
    ≈⟨ refl⟩∘⟨ assoc
       ○ pullˡ (assoc-commute-to ○ (⊗.identity ⟩⊗⟨refl) ⟩∘⟨refl) ○ assoc ⟩
  id ⊗₁ j′ ∘ (α⇐ ∘ (id ⊗₁ _ ∘ α⇒))         ∎

------------------------------------------------------------------------
-- A state map on each factor conjugates both actions

onL-sim : {v : P ⇒ R} {w : Q ⇒ Z} {k : P ⊗₀ X ⇒ P ⊗₀ Y} {k′ : R ⊗₀ X ⇒ R ⊗₀ Y}
        → v ⊗₁ id ∘ k ≈ k′ ∘ v ⊗₁ id
        → (v ⊗₁ w) ⊗₁ id ∘ onL k ≈ onL k′ ∘ (v ⊗₁ w) ⊗₁ id
onL-sim {v = v} {w} e = begin
  (v ⊗₁ w) ⊗₁ id ∘ (β ∘ (_ ⊗₁ id ∘ β))
    ≈⟨ pullˡ (β-nat v id w) ○ assoc ⟩
  β ∘ ((v ⊗₁ id) ⊗₁ w ∘ (_ ⊗₁ id ∘ β))
    ≈⟨ refl⟩∘⟨ pullˡ (parallel e id-comm) ⟩
  β ∘ ((_ ⊗₁ id ∘ (v ⊗₁ id) ⊗₁ w) ∘ β)
    ≈⟨ refl⟩∘⟨ assoc ⟩
  β ∘ (_ ⊗₁ id ∘ ((v ⊗₁ id) ⊗₁ w ∘ β))
    ≈⟨ refl⟩∘⟨ refl⟩∘⟨ β-nat v w id ⟩
  β ∘ (_ ⊗₁ id ∘ (β ∘ (v ⊗₁ w) ⊗₁ id))
    ≈⟨ refl⟩∘⟨ sym-assoc ○ sym-assoc ⟩
  (β ∘ (_ ⊗₁ id ∘ β)) ∘ (v ⊗₁ w) ⊗₁ id  ∎

onR-sim : {v : P ⇒ R} {w : Q ⇒ Z} {k : Q ⊗₀ X ⇒ Q ⊗₀ Y} {k′ : Z ⊗₀ X ⇒ Z ⊗₀ Y}
        → w ⊗₁ id ∘ k ≈ k′ ∘ w ⊗₁ id
        → (v ⊗₁ w) ⊗₁ id ∘ onR k ≈ onR k′ ∘ (v ⊗₁ w) ⊗₁ id
onR-sim {v = v} {w} e = begin
  (v ⊗₁ w) ⊗₁ id ∘ (α⇐ ∘ (id ⊗₁ _ ∘ α⇒))
    ≈⟨ pullˡ (⟺ assoc-commute-to) ○ assoc ⟩
  α⇐ ∘ (v ⊗₁ (w ⊗₁ id) ∘ (id ⊗₁ _ ∘ α⇒))
    ≈⟨ refl⟩∘⟨ pullˡ (parallel id-comm e) ⟩
  α⇐ ∘ ((id ⊗₁ _ ∘ v ⊗₁ (w ⊗₁ id)) ∘ α⇒)
    ≈⟨ refl⟩∘⟨ assoc ⟩
  α⇐ ∘ (id ⊗₁ _ ∘ (v ⊗₁ (w ⊗₁ id) ∘ α⇒))
    ≈˘⟨ refl⟩∘⟨ refl⟩∘⟨ assoc-commute-from ⟩
  α⇐ ∘ (id ⊗₁ _ ∘ (α⇒ ∘ (v ⊗₁ w) ⊗₁ id))
    ≈⟨ refl⟩∘⟨ sym-assoc ○ sym-assoc ⟩
  (α⇐ ∘ (id ⊗₁ _ ∘ α⇒)) ∘ (v ⊗₁ w) ⊗₁ id  ∎

------------------------------------------------------------------------
-- The state braiding exchanges the two actions

σ-onR : {k : Q ⊗₀ A ⇒ Q ⊗₀ B} → σ⇒ ⊗₁ id ∘ onR k ≈ onL {Q = P} k ∘ σ⇒ ⊗₁ id
σ-onR {k = k} = begin
  σ⇒ ⊗₁ id ∘ (α⇐ ∘ (id ⊗₁ k ∘ α⇒))              ≈⟨ sym-assoc ⟩
  (σ⇒ ⊗₁ id ∘ α⇐) ∘ (id ⊗₁ k ∘ α⇒)              ≈⟨ unbraid k ⟩
  ((σ⇒ ⊗₁ id ∘ α⇐) ∘ σ⇒) ∘ (k ⊗₁ id ∘ (σ⇒ ∘ α⇒))
    ≈⟨ out ⟩∘⟨ (refl⟩∘⟨ inn) ⟩
  β ∘ (k ⊗₁ id ∘ (β ∘ σ⇒ ⊗₁ id))            ≈⟨ refl⟩∘⟨ sym-assoc ⟩
  β ∘ ((k ⊗₁ id ∘ β) ∘ σ⇒ ⊗₁ id)            ≈⟨ sym-assoc ⟩
  (β ∘ (k ⊗₁ id ∘ β)) ∘ σ⇒ ⊗₁ id            ∎
  where
    out : (σ⇒ ⊗₁ id ∘ α⇐) ∘ σ⇒ ≈ β
    out = (refl⟩∘⟨ σ-splitʳ) ○ cancelInner associator.isoˡ
        ○ (refl⟩∘⟨ assoc) ○ (refl⟩∘⟨ assoc) ○ cancelˡ σ⊗-inv

    inn : σ⇒ ∘ α⇒ ≈ β ∘ σ⇒ ⊗₁ id
    inn = (σ-splitˡ ⟩∘⟨refl) ○ cancelʳ associator.isoˡ ○ (refl⟩∘⟨ sym-assoc) ○ sym-assoc

σ-onL : {k : P ⊗₀ A ⇒ P ⊗₀ B} → σ⇒ ⊗₁ id ∘ onL k ≈ onR {P = Q} k ∘ σ⇒ ⊗₁ id
σ-onL = (refl⟩∘⟨ ⟺ (cancelʳ σ⊗-inv)) ○ (refl⟩∘⟨ ⟺ σ-onR ⟩∘⟨refl)
      ○ (refl⟩∘⟨ assoc) ○ cancelˡ σ⊗-inv

------------------------------------------------------------------------
-- Collapsing a trivial state factor

onR-collapseˡ : {k : Q ⊗₀ A ⇒ Q ⊗₀ B} → λ⇒ ⊗₁ id ∘ onR k ≈ k ∘ λ⇒ ⊗₁ id
onR-collapseˡ {k = k} = begin
  λ⇒ ⊗₁ id ∘ (α⇐ ∘ (id ⊗₁ k ∘ α⇒))   ≈˘⟨ coherence₁ ⟩∘⟨refl ⟩
  (λ⇒ ∘ α⇒) ∘ (α⇐ ∘ (id ⊗₁ k ∘ α⇒))  ≈⟨ cancelInner associator.isoʳ ⟩
  λ⇒ ∘ (id ⊗₁ k ∘ α⇒)                ≈⟨ pullˡ unitorˡ-commute-from ○ assoc ⟩
  k ∘ (λ⇒ ∘ α⇒)                      ≈⟨ refl⟩∘⟨ coherence₁ ⟩
  k ∘ λ⇒ ⊗₁ id                       ∎

onL-collapseʳ : {k : P ⊗₀ A ⇒ P ⊗₀ B} → ρ⇒ ⊗₁ id ∘ onL k ≈ k ∘ ρ⇒ ⊗₁ id
onL-collapseʳ = pullˡ ρ-β ○ pullˡ unitorʳ-commute-from ○ assoc
              ○ (refl⟩∘⟨ ((⟺ ρ-β ⟩∘⟨refl) ○ cancelʳ β-β))

------------------------------------------------------------------------
-- The point of a paired state

⊛-point₂ : (S T S′ T′ : State) {u : obj S ⇒ obj T} {v : obj S′ ⇒ obj T′}
         → u ∘ point S ≈ point T → v ∘ point S′ ≈ point T′
         → u ⊗₁ v ∘ point (S ⊛ S′) ≈ point (T ⊛ T′)
⊛-point₂ _ _ _ _ e₁ e₂ = pullˡ (⟺ ⊗.homomorphism ○ (e₁ ⟩⊗⟨ e₂))

-- The scalar prefixes merge because scalars are central (`scalar-λ⇐`).
⊛-point₂ˡ : (S T S′ T′ : State) {u : obj S ⇒ obj T} {v : obj S′ ⇒ obj T′}
            {σ τ : unit ⇒ unit}
          → u ∘ point S ≈ point T ∘ σ → v ∘ point S′ ≈ point T′ ∘ τ
          → u ⊗₁ v ∘ point (S ⊛ S′) ≈ point (T ⊛ T′) ∘ (σ ∘ τ)
⊛-point₂ˡ _ _ _ _ {σ = σ} {τ} e₁ e₂ =
    pullˡ (⟺ ⊗.homomorphism ○ (e₁ ⟩⊗⟨ e₂) ○ ⊗.homomorphism)
  ○ assoc ○ (refl⟩∘⟨ scalar-λ⇐ σ τ) ○ sym-assoc

λ-point : (S : State) → λ⇒ ∘ point (Iˢ ⊛ S) ≈ point S
λ-point S = pullˡ unitorˡ-commute-from ○ cancelʳ unitorˡ.isoʳ

ρ-point : (S : State) → ρ⇒ ∘ point (S ⊛ Iˢ) ≈ point S
ρ-point S = pullˡ unitorʳ-commute-from ○ cancelʳ ((⟺ coherence₃) ⟩∘⟨refl ○ unitorˡ.isoʳ)

⊛-assoc-point : (S T R : State) → α⇒ ∘ point ((S ⊛ T) ⊛ R) ≈ point (S ⊛ (T ⊛ R))
⊛-assoc-point S T R = begin
  α⇒ ∘ ((point S ⊗₁ point T ∘ λ⇐) ⊗₁ point R ∘ λ⇐)
    ≈⟨ refl⟩∘⟨ (split₁ʳ ⟩∘⟨refl) ○ (refl⟩∘⟨ assoc) ⟩
  α⇒ ∘ ((point S ⊗₁ point T) ⊗₁ point R ∘ (λ⇐ ⊗₁ id ∘ λ⇐))
    ≈⟨ sym-assoc ○ (assoc-commute-from ⟩∘⟨refl) ○ assoc ⟩
  point S ⊗₁ (point T ⊗₁ point R) ∘ (α⇒ ∘ (λ⇐ ⊗₁ id ∘ λ⇐))
    ≈⟨ refl⟩∘⟨ (pullˡ ((refl⟩∘⟨ ⟺ coherence-inv₁) ○ cancelˡ associator.isoʳ)
                ○ unitorˡ-commute-to) ⟩
  point S ⊗₁ (point T ⊗₁ point R) ∘ (id ⊗₁ λ⇐ ∘ λ⇐)
    ≈⟨ sym-assoc ○ (⟺ split₂ʳ ⟩∘⟨refl) ⟩
  point S ⊗₁ (point T ⊗₁ point R ∘ λ⇐) ∘ λ⇐  ∎
