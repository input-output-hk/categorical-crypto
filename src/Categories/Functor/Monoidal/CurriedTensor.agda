{-# OPTIONS --safe --without-K #-}

-- The curried tensor X ↦ (X ⊗ -) as a monoidal functor M → Endofunctors 𝒞.

open import Categories.Category.Monoidal

module Categories.Functor.Monoidal.CurriedTensor {o ℓ e} (M : MonoidalCategory o ℓ e) where

open import Data.Product

open import Categories.Category
open import Categories.Category.Construction.Functors
open import Categories.Category.Monoidal.Construction.Endofunctors
open import Categories.Category.Product
open import Categories.Coherence.Monoidal.Tactic using (solve-mor)
open import Categories.Functor renaming (id to idF)
open import Categories.Functor.Monoidal
open import Categories.NaturalTransformation

private
  module M = MonoidalCategory M
  𝒞 = M.U
  module 𝒞 = Category 𝒞
  E = Endofunctors 𝒞
  module E = MonoidalCategory E
  𝒞×𝒞 = Product 𝒞 𝒞

open M
open import Categories.Category.Monoidal.Utilities M.monoidal
open Shorthands

curriedTensor : MonoidalFunctor M E
curriedTensor = record { F = F ; isMonoidal = isMon }
  where
  open Functor
  F : Functor 𝒞 E.U
  F = curry.F₀ M.⊗

  Src Tgt : Functor 𝒞×𝒞 E.U
  Src = E.⊗ ∘F (F ⁂ F)
  Tgt = F ∘F M.⊗

  ε : NaturalTransformation idF (F₀ F unit)
  ε = ntHelper record { η = λ _ → λ⇐ ; commute = λ _ → M.unitorˡ-commute-to }

  homo-η : ∀ XY → F₀ Src XY E.⇒ F₀ Tgt XY
  homo-η (X , Y) = ntHelper record { η = λ _ → α⇐ ; commute = inner }
    where
    open Category.HomReasoning 𝒞
    inner : ∀ {A B} (f : 𝒞 [ A , B ]) → α⇐ 𝒞.∘ 𝒞.id ⊗₁ 𝒞.id ⊗₁ f 𝒞.≈ 𝒞.id ⊗₁ f 𝒞.∘ α⇐
    inner f = begin
        α⇐ 𝒞.∘ (𝒞.id ⊗₁ (𝒞.id ⊗₁ f)) ≈⟨ M.assoc-commute-to ⟩
        ((𝒞.id ⊗₁ 𝒞.id) ⊗₁ f) 𝒞.∘ α⇐ ≈⟨ F-resp-≈ M.⊗ (identity M.⊗ , 𝒞.Equiv.refl) ⟩∘⟨refl ⟩
        (𝒞.id ⊗₁ f) 𝒞.∘ α⇐            ∎

  homo-commute : ∀ {XY X′Y′} (f : 𝒞×𝒞 [ XY , X′Y′ ]) → homo-η X′Y′ E.∘ F₁ Src f E.≈ F₁ Tgt f E.∘ homo-η XY
  homo-commute (m , n) = begin
      α⇐ 𝒞.∘ 𝒞.id ⊗₁ n ⊗₁ 𝒞.id 𝒞.∘ m ⊗₁ 𝒞.id ≈⟨ refl⟩∘⟨ merge ⟩
      α⇐ 𝒞.∘ m ⊗₁ n ⊗₁ 𝒞.id                   ≈⟨ M.assoc-commute-to ⟩
      (m ⊗₁ n) ⊗₁ 𝒞.id 𝒞.∘ α⇐                 ∎
    where
      open Category.HomReasoning 𝒞
      merge : 𝒞.id ⊗₁ (n ⊗₁ 𝒞.id) 𝒞.∘ m ⊗₁ 𝒞.id 𝒞.≈ m ⊗₁ n ⊗₁ 𝒞.id
      merge = ⟺ (homomorphism M.⊗) ○ F-resp-≈ M.⊗ (𝒞.identityˡ , 𝒞.identityʳ)

  ⊗-homo : NaturalTransformation Src Tgt
  ⊗-homo = ntHelper record { η = homo-η ; commute = homo-commute }

  assoc-law : ∀ {X Y Z x} →
      α⇒ {X} {Y} {Z} ⊗₁ 𝒞.id {x}
    𝒞.∘ α⇐ {X ⊗₀ Y} {Z} {x}
    𝒞.∘ 𝒞.id {X ⊗₀ Y} ⊗₁ 𝒞.id {Z ⊗₀ x}
    𝒞.∘ α⇐ {X} {Y} {Z ⊗₀ x}
    𝒞.≈ α⇐ {X} {Y ⊗₀ Z} {x}
    𝒞.∘ (𝒞.id {X} ⊗₁ α⇐ {Y} {Z} {x} 𝒞.∘ 𝒞.id) 𝒞.∘ 𝒞.id
  assoc-law = solve-mor M

  unitˡ-law : ∀ {X x} →
      λ⇒ {X} ⊗₁ 𝒞.id {x}
    𝒞.∘ α⇐ {unit} {X} {x}
    𝒞.∘ 𝒞.id {unit} ⊗₁ 𝒞.id {X ⊗₀ x}
    𝒞.∘ λ⇐ {X ⊗₀ x}
    𝒞.≈ 𝒞.id {X ⊗₀ x}
  unitˡ-law = solve-mor M

  unitʳ-law : ∀ {X x} →
      ρ⇒ {X} ⊗₁ 𝒞.id {x}
    𝒞.∘ α⇐ {X} {unit} {x}
    𝒞.∘ 𝒞.id {X} ⊗₁ λ⇐ {x}
    𝒞.∘ 𝒞.id
    𝒞.≈ 𝒞.id {X ⊗₀ x}
  unitʳ-law = solve-mor M

  isMon : IsMonoidalFunctor M E F
  isMon = record
    { ε = ε ; ⊗-homo = ⊗-homo
    ; associativity = assoc-law ; unitaryˡ = unitˡ-law ; unitaryʳ = unitʳ-law }
