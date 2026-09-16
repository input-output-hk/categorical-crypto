{-# OPTIONS --safe --without-K #-}

-- The curried tensor X ↦ (X ⊗ -) as a monoidal functor M → Endofunctors 𝒞.

open import Categories.Category.Monoidal

module Categories.Functor.Monoidal.CurriedTensor {o ℓ e} (M : MonoidalCategory o ℓ e) where

open import Data.Fin
open import Data.Product
open import Data.Vec using (_∷_; [])

open import Categories.Category
open import Categories.Category.Construction.Functors
open import Categories.Category.Monoidal.Construction.Endofunctors
open import Categories.Category.Product
import Categories.Coherence.Monoidal as Coh
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
    α⇒ ⊗₁ 𝒞.id 𝒞.∘ α⇐ 𝒞.∘ 𝒞.id ⊗₁ 𝒞.id 𝒞.∘ α⇐ 𝒞.≈ α⇐ 𝒞.∘ (𝒞.id ⊗₁ α⇐ 𝒞.∘ 𝒞.id) 𝒞.∘ 𝒞.id
  assoc-law {X} {Y} {Z} {x} = S.solveM lhs rhs
    where
      module S = Coh.Structural M (X ∷ Y ∷ Z ∷ x ∷ [])
      x₀ = S.Var zero
      y₀ = S.Var (suc zero)
      z₀ = S.Var (suc (suc zero))
      q₀ = S.Var (suc (suc (suc zero)))
      lhs = (S.α⇒ {x₀} {y₀} {z₀} S.⊗₁ S.id {q₀}) S.∘
            (S.α⇐ {x₀ S.⊗₀ y₀} {z₀} {q₀} S.∘
             ((S.id {x₀ S.⊗₀ y₀} S.⊗₁ S.id {z₀ S.⊗₀ q₀}) S.∘ S.α⇐ {x₀} {y₀} {z₀ S.⊗₀ q₀}))
      rhs = S.α⇐ {x₀} {y₀ S.⊗₀ z₀} {q₀} S.∘
            (((S.id {x₀} S.⊗₁ S.α⇐ {y₀} {z₀} {q₀}) S.∘ S.id) S.∘ S.id)

  unitˡ-law : ∀ {X x} → λ⇒ ⊗₁ 𝒞.id 𝒞.∘ α⇐ 𝒞.∘ 𝒞.id ⊗₁ 𝒞.id 𝒞.∘ λ⇐ 𝒞.≈ 𝒞.id
  unitˡ-law {X} {x} = S.solveM lhs (S.id {x₀ S.⊗₀ q₀})
    where
      module S = Coh.Structural M (X ∷ x ∷ [])
      x₀ = S.Var zero
      q₀ = S.Var (suc zero)
      lhs = (S.λ⇒ {x₀} S.⊗₁ S.id {q₀}) S.∘
            (S.α⇐ {S.unit} {x₀} {q₀} S.∘
             ((S.id {S.unit} S.⊗₁ S.id {x₀ S.⊗₀ q₀}) S.∘ S.λ⇐ {x₀ S.⊗₀ q₀}))

  unitʳ-law : ∀ {X x} → ρ⇒ ⊗₁ 𝒞.id 𝒞.∘ α⇐ 𝒞.∘ 𝒞.id ⊗₁ λ⇐ 𝒞.∘ 𝒞.id 𝒞.≈ 𝒞.id
  unitʳ-law {X} {x} = S.solveM lhs (S.id {x₀ S.⊗₀ q₀})
    where
      module S = Coh.Structural M (X ∷ x ∷ [])
      x₀ = S.Var zero
      q₀ = S.Var (suc zero)
      lhs = (S.ρ⇒ {x₀} S.⊗₁ S.id {q₀}) S.∘
            (S.α⇐ {x₀} {S.unit} {q₀} S.∘
             ((S.id {x₀} S.⊗₁ S.λ⇐ {q₀}) S.∘ S.id))

  isMon : IsMonoidalFunctor M E F
  isMon = record
    { ε = ε ; ⊗-homo = ⊗-homo
    ; associativity = assoc-law ; unitaryˡ = unitˡ-law ; unitaryʳ = unitʳ-law }
