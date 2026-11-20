{-# OPTIONS --safe --without-K #-}

-- Equations for the G construction

module Categories.GConstruction.CoreProofs where

open import Categories.Category
open import Categories.Category.Monoidal
open import Categories.Category.Monoidal.Traced
import Categories.Category.Monoidal.Traced.Ext as TE
open import Categories.Coherence.Symmetric.Tactic
import Categories.GConstruction.Core as Core
open import Data.Product

import Categories.Category.Monoidal.Braided.Properties as BProps
import Categories.Category.Monoidal.Utilities as U
import Categories.GConstruction.Trace as GT

module _ {a b c} (C : Category a b c) (M : Monoidal C) (T : Traced M) where

  open Category C
  open Traced T
  open import Categories.Category.Monoidal.Symmetric.Properties.Ext symmetric using (β-β)
  open U M using (triangle-inv; pentagon-inv)
  open U.Shorthands M
  open import Categories.Category.Monoidal.Reasoning M using (serialize₁₂; serialize₂₁; _⟩⊗⟨_)
  open import Categories.Morphism.Reasoning C
  open BProps.Shorthands braided
  private module W = GT C M T
  open W using (α; β; γ; Cˢ; mid; mid-unitˡ; mid-unitʳ; mid-assoc; trace-mid)
  open HomReasoning
  open TE T using (trace-β; trace-β′; trace-comm)

  private variable A A' B B' X Y A⁺ A⁻ B⁺ B⁻ D⁺ D⁻ E⁺ E⁻ P⁺ P⁻ Q⁺ Q⁻ R⁺ R⁻ : Obj

  open Core.Construction C M T

  ⌜⌝-resp-≈ : {u u' : A⁺ ⇒ B⁺} {v v' : B⁻ ⇒ A⁻} → u ≈ u' → v ≈ v' → ⌜ u , v ⌝ ≈ ⌜ u' , v' ⌝
  ⌜⌝-resp-≈ e₁ e₂ = refl⟩∘⟨ (e₁ ⟩⊗⟨ e₂)

  opaque
    unfolding _⊗₁ᴳ_

    ⊗₁ᴳ-resp-≈ : ∀ {f f' : A⁺ ⊗₀ B⁻ ⇒ A⁻ ⊗₀ B⁺} {g g' : D⁺ ⊗₀ E⁻ ⇒ D⁻ ⊗₀ E⁺} →
                 f ≈ f' → g ≈ g' → f ⊗₁ᴳ g ≈ f' ⊗₁ᴳ g'
    ⊗₁ᴳ-resp-≈ e₁ e₂ = refl⟩∘⟨ e₁ ⟩⊗⟨ e₂ ⟩∘⟨refl

    ⌜⌝-⊗ : {u : A⁺ ⇒ B⁺} {v : B⁻ ⇒ A⁻} {p : D⁺ ⇒ E⁺} {q : E⁻ ⇒ D⁻} →
           ⌜ u , v ⌝ ⊗₁ᴳ ⌜ p , q ⌝ ≈ ⌜ u ⊗₁ p , v ⊗₁ q ⌝
    ⌜⌝-⊗ = solve-smc Cˢ

  right-superposing : {f : A ⊗₀ X ⇒ B ⊗₀ X} → trace f ⊗₁ id {Y} ≈ trace (β ∘ f ⊗₁ id ∘ β)
  right-superposing {f = f} = begin
    trace f ⊗₁ id
      ≈⟨ introˡ commutative ○ pullʳ (braiding.⇒.commute _) ⟩
    σ⇒ ∘ id ⊗₁ trace f ∘ σ⇒
      ≈⟨ refl⟩∘⟨ Equiv.sym superposing ⟩∘⟨refl ⟩
    σ⇒ ∘ trace (α⇐ ∘ id ⊗₁ f ∘ α⇒) ∘ σ⇒
      ≈⟨ refl⟩∘⟨ ⟺ tightenᵣ ⟩
    σ⇒ ∘ trace ((α⇐ ∘ id ⊗₁ f ∘ α⇒) ∘ σ⇒ ⊗₁ id)
      ≈⟨ ⟺ tightenₗ ⟩
    trace (σ⇒ ⊗₁ id ∘ (α⇐ ∘ id ⊗₁ f ∘ α⇒) ∘ σ⇒ ⊗₁ id)
      ≈⟨ trace-resp-≈ (solve-smc Cˢ) ⟩
    trace (β ∘ f ⊗₁ id ∘ β) ∎

  ⊗-trace-mid : {u : A ⊗₀ X ⇒ B ⊗₀ X} {v : A' ⊗₀ Y ⇒ B' ⊗₀ Y} →
                trace u ⊗₁ trace v ≈ trace (mid ∘ u ⊗₁ v ∘ mid)
  ⊗-trace-mid =
    serialize₁₂
    ○ (right-superposing ⟩∘⟨ Equiv.sym superposing)
    ○ ⟺ tightenᵣ
    ○ trace-resp-≈ (refl⟩∘⟨ right-superposing)
    ○ trace-resp-≈ (⟺ tightenₗ)
    ○ trace-resp-≈ (trace-resp-≈ (solve-smc Cˢ))
    ○ vanishing₂

  opaque
    unfolding composeᴳ

    compose-resp-≈ : ∀ {A B D} {f h : B ⇒ᴳ D} {g i : A ⇒ᴳ B}
                   → f ≈ h → g ≈ i → composeᴳ f g ≈ composeᴳ h i
    compose-resp-≈ p q = trace-resp-≈ (refl⟩∘⟨ p ⟩⊗⟨ q ⟩∘⟨refl)

    identityˡ' : ∀ {A B} {f : A ⇒ᴳ B} → composeᴳ σ⇒ f ≈ f
    identityˡ' {A⁺ , A⁻} {B⁺ , B⁻} {f} =
      ⟺ (vanishing₂ {X = B⁻} {Y = B⁺})
      ○ trace-resp-≈ (trace-resp-≈ (solve-smc Cˢ) ○ tightenᵣ ○ trace-β′ ⟩∘⟨refl ○ cancelˡ β-β) ○ trace-β′

    identityʳ' : ∀ {A B} {f : A ⇒ᴳ B} → composeᴳ f σ⇒ ≈ f
    identityʳ' {A⁺ , A⁻} {B⁺ , B⁻} {f} =
      ⟺ (vanishing₂ {X = A⁻} {Y = A⁺})
      ○ trace-resp-≈ (trace-resp-≈
          {g = ((β ∘ σ⇒ ⊗₁ id ∘ β) ∘ f ⊗₁ id ∘ (σ⇒ ⊗₁ id ∘ β)) ⊗₁ id ∘ β ∘ (β ∘ σ⇒ ⊗₁ id) ⊗₁ id}
          (solve-smc Cˢ) ○ tightenₗ ○ refl⟩∘⟨ (tightenᵣ ○ elimˡ trace-β) ○ solve-smc Cˢ)
      ○ tightenᵣ ○ trace-β′ ⟩∘⟨refl ○ cancelˡ commutative

    assoc' : ∀ {A B D E} {f : A ⇒ᴳ B} {g : B ⇒ᴳ D} {h : D ⇒ᴳ E}
           → composeᴳ (composeᴳ h g) f ≈ composeᴳ h (composeᴳ g f)
    assoc' =
      trace-resp-≈ (refl⟩∘⟨ pushˡ serialize₁₂)
      ○ trace-resp-≈ (refl⟩∘⟨ right-superposing ⟩∘⟨refl)
      ○ trace-resp-≈ (refl⟩∘⟨ ⟺ tightenᵣ)
      ○ trace-resp-≈ (⟺ tightenₗ)
      ○ trace-comm
      ○ trace-resp-≈ (trace-resp-≈ (solve-smc Cˢ))
      ○ trace-resp-≈ tightenₗ
      ○ trace-resp-≈ (refl⟩∘⟨ tightenᵣ)
      ○ trace-resp-≈ (refl⟩∘⟨ superposing ⟩∘⟨refl)
      ○ trace-resp-≈ (refl⟩∘⟨ pullˡ (⟺ serialize₂₁))

  ⌜⌝-id : ⌜ id , id ⌝ ≈ σ⇒ {A⁺} {A⁻}
  ⌜⌝-id = elimʳ ⊗.identity

  opaque
    unfolding composeᴳ

    absorbˡ : {u : B⁺ ⇒ D⁺} {v : D⁻ ⇒ B⁻} {g : A⁺ ⊗₀ B⁻ ⇒ A⁻ ⊗₀ B⁺} →
              composeᴳ ⌜ u , v ⌝ g ≈ id ⊗₁ u ∘ g ∘ id ⊗₁ v
    absorbˡ = trace-resp-≈ (solve-smc Cˢ) ○ tightenₗ ○ (refl⟩∘⟨ tightenᵣ) ○ refl⟩∘⟨ identityˡ' ⟩∘⟨refl

    absorbʳ : {p : A⁺ ⇒ B⁺} {q : B⁻ ⇒ A⁻} {f : B⁺ ⊗₀ D⁻ ⇒ B⁻ ⊗₀ D⁺} →
              composeᴳ f ⌜ p , q ⌝ ≈ q ⊗₁ id ∘ f ∘ p ⊗₁ id
    absorbʳ = trace-resp-≈ (solve-smc Cˢ) ○ tightenₗ ○ (refl⟩∘⟨ tightenᵣ) ○ refl⟩∘⟨ identityʳ' ⟩∘⟨refl

  ⌜⌝-∘ : {u : B⁺ ⇒ D⁺} {v : D⁻ ⇒ B⁻} {p : A⁺ ⇒ B⁺} {q : B⁻ ⇒ A⁻} →
         composeᴳ ⌜ u , v ⌝ ⌜ p , q ⌝ ≈ ⌜ u ∘ p , q ∘ v ⌝
  ⌜⌝-∘ = absorbˡ ○ solve-smc Cˢ

  ⌜⌝-⊗ˡ : {p : D⁺ ⇒ E⁺} {q : E⁻ ⇒ D⁻} → σ⇒ {A⁺} {A⁻} ⊗₁ᴳ ⌜ p , q ⌝ ≈ ⌜ id ⊗₁ p , id ⊗₁ q ⌝
  ⌜⌝-⊗ˡ = ⊗₁ᴳ-resp-≈ (⟺ ⌜⌝-id) Equiv.refl ○ ⌜⌝-⊗

  ⌜⌝-⊗ʳ : {u : A⁺ ⇒ B⁺} {v : B⁻ ⇒ A⁻} → ⌜ u , v ⌝ ⊗₁ᴳ σ⇒ {D⁺} {D⁻} ≈ ⌜ u ⊗₁ id , v ⊗₁ id ⌝
  ⌜⌝-⊗ʳ = ⊗₁ᴳ-resp-≈ Equiv.refl (⟺ ⌜⌝-id) ○ ⌜⌝-⊗

  identityᴳ : σ⇒ {A⁺} {A⁻} ⊗₁ᴳ σ⇒ {B⁺} {B⁻} ≈ σ⇒
  identityᴳ = ⊗₁ᴳ-resp-≈ (⟺ ⌜⌝-id) (⟺ ⌜⌝-id) ○ ⌜⌝-⊗ ○ ⌜⌝-resp-≈ ⊗.identity ⊗.identity ○ ⌜⌝-id

  opaque
    unfolding _⊗₁ᴳ_ composeᴳ

    homomorphismᴳ : {f : A⁺ ⊗₀ B⁻ ⇒ A⁻ ⊗₀ B⁺} {f′ : B⁺ ⊗₀ D⁻ ⇒ B⁻ ⊗₀ D⁺}
                    {g : P⁺ ⊗₀ Q⁻ ⇒ P⁻ ⊗₀ Q⁺} {g′ : Q⁺ ⊗₀ R⁻ ⇒ Q⁻ ⊗₀ R⁺} →
                    composeᴳ f′ f ⊗₁ᴳ composeᴳ g′ g ≈ composeᴳ (f′ ⊗₁ᴳ g′) (f ⊗₁ᴳ g)
    homomorphismᴳ =
      refl⟩∘⟨ ⊗-trace-mid ⟩∘⟨refl ○ refl⟩∘⟨ ⟺ tightenᵣ ○ ⟺ tightenₗ
      ○ trace-resp-≈ (solve-smc Cˢ) ○ ⟺ trace-mid

  opaque
    unfolding _⊗₁ᴳ_ composeᴳ

    triangleᴳ : composeᴳ (σ⇒ {A⁺} {A⁻} ⊗₁ᴳ ⌜ λ⇒ , λ⇐ ⌝) ⌜ α⇒ , α⇐ ⌝ ≈ ⌜ ρ⇒ , ρ⇐ ⌝ ⊗₁ᴳ σ⇒ {B⁺} {B⁻}
    triangleᴳ = compose-resp-≈ ⌜⌝-⊗ˡ Equiv.refl
              ○ ⌜⌝-∘ ○ ⌜⌝-resp-≈ triangle triangle-inv ○ ⟺ ⌜⌝-⊗ʳ

    pentagonᴳ : composeᴳ (σ⇒ {A⁺} {A⁻} ⊗₁ᴳ ⌜ α⇒ {B⁺} {D⁺} , α⇐ {B⁻} {D⁻} ⌝)
                         (composeᴳ ⌜ α⇒ , α⇐ ⌝ (⌜ α⇒ , α⇐ ⌝ ⊗₁ᴳ σ⇒ {E⁺} {E⁻}))
              ≈ composeᴳ ⌜ α⇒ {A⁺} , α⇐ ⌝ ⌜ α⇒ , α⇐ ⌝
    pentagonᴳ = compose-resp-≈ ⌜⌝-⊗ˡ (compose-resp-≈ Equiv.refl ⌜⌝-⊗ʳ ○ ⌜⌝-∘)
              ○ ⌜⌝-∘ ○ ⌜⌝-resp-≈ pentagon pentagon-inv ○ ⟺ ⌜⌝-∘

    unitorˡ-commuteᴳ : {f : A⁺ ⊗₀ B⁻ ⇒ A⁻ ⊗₀ B⁺} →
                       composeᴳ ⌜ λ⇒ , λ⇐ ⌝ (σ⇒ ⊗₁ᴳ f) ≈ composeᴳ f ⌜ λ⇒ , λ⇐ ⌝
    unitorˡ-commuteᴳ = absorbˡ ○ mid-unitˡ ○ ⟺ absorbʳ

    unitorʳ-commuteᴳ : {f : A⁺ ⊗₀ B⁻ ⇒ A⁻ ⊗₀ B⁺} →
                       composeᴳ ⌜ ρ⇒ , ρ⇐ ⌝ (f ⊗₁ᴳ σ⇒) ≈ composeᴳ f ⌜ ρ⇒ , ρ⇐ ⌝
    unitorʳ-commuteᴳ = absorbˡ ○ mid-unitʳ ○ ⟺ absorbʳ

    assoc-commuteᴳ : {f : A⁺ ⊗₀ B⁻ ⇒ A⁻ ⊗₀ B⁺} {g : D⁺ ⊗₀ E⁻ ⇒ D⁻ ⊗₀ E⁺} {h : P⁺ ⊗₀ Q⁻ ⇒ P⁻ ⊗₀ Q⁺} →
                     composeᴳ ⌜ α⇒ , α⇐ ⌝ ((f ⊗₁ᴳ g) ⊗₁ᴳ h) ≈ composeᴳ (f ⊗₁ᴳ (g ⊗₁ᴳ h)) ⌜ α⇒ , α⇐ ⌝
    assoc-commuteᴳ = absorbˡ ○ mid-assoc ○ ⟺ absorbʳ
