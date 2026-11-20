{-# OPTIONS --safe --without-K #-}

-- If W is a commutative monoid on a traced SMC, Kl(W ⊗-) is also a traced SMC

open import Categories.Category
open import Categories.Category.Construction.Kleisli
open import Categories.Category.Monoidal
open import Categories.Category.Monoidal.Construction.Kleisli
import Categories.Category.Monoidal.Construction.Kleisli.Writer.Core as Core
open import Categories.Category.Monoidal.Construction.Kleisli.Symmetric
open import Categories.Category.Monoidal.Symmetric
open import Categories.Category.Monoidal.Traced
open import Categories.Monad.Construction.Action
open import Categories.Object.CommutativeMonoid
import Categories.Category.Monoidal.Braided.Properties as BProps
import Categories.Category.Monoidal.Utilities as U

module Categories.Category.Monoidal.Construction.Kleisli.Writer
  {o ℓ e} {C : Category o ℓ e} {M : Monoidal C}
  (T : Traced M) (W : CommutativeMonoid (Traced.braided T)) where

open Category C
open Traced T
open BProps.Shorthands braided

open U.Shorthands M
open CommutativeMonoid W using (monoid) renaming (Carrier to E)

open Core.Trace T monoid
open Core.Sliding T W
open import Categories.Category.Monoidal.Reasoning M
open import Categories.Monad.Construction.Action.Commutative symmetric
open import Categories.Morphism.Reasoning C
open import Categories.Monad.Commutative.Properties
import Categories.Monad.Strong.Properties as SP
open CommutativeProperties braided (actionCommutativeMonad W)
open TripleNotation (ActionM M monoid)

writerCategory : Category o ℓ e
writerCategory = Kleisli (ActionM M monoid)

writerMonoidal : Monoidal writerCategory
writerMonoidal = Kleisli-Monoidal symmetric (actionCommutativeMonad W)

writerSymmetric : Symmetric writerMonoidal
writerSymmetric = Kleisli-Symmetric symmetric (actionCommutativeMonad W)

private
  module K = Category writerCategory
  module KM = Monoidal writerMonoidal
  module Strength = SP.Left.Shorthands (actionStrength monoid)
  variable A B D F X : Obj

  tensor-idʳ : {f : A ⇒ E ⊗₀ B} → f KM.⊗₁ K.id {X} ≈ α⇒ ∘ f ⊗₁ id
  tensor-idʳ = ψ-τ' ○ right-strength-normal monoid ⟩∘⟨refl

  tensor-idˡ : {f : A ⇒ E ⊗₀ B} → K.id {X} KM.⊗₁ f ≈ Strength.σ ∘ id ⊗₁ f
  tensor-idˡ = ψ-σ'

  pure-sandwich : {f : A ⇒ E ⊗₀ B} {a : B ⇒ D} {b : F ⇒ A} →
    (K.id ∘ a) K.∘ f K.∘ K.id ∘ b ≈ id ⊗₁ a ∘ f ∘ b
  pure-sandwich = *⇒F₁ ⟩∘⟨refl ○ refl⟩∘⟨ pullˡ *-identityʳ

writerTraced : Traced writerMonoidal
writerTraced = record
  { symmetric    = writerSymmetric
  ; trace        = traceW
  ; trace-resp-≈ = traceW-resp-≈
  ; slide = λ {f = f} {g} →
      traceW-resp-≈ (K.∘-resp-≈ʳ tensor-idˡ)
      ○ slideW f g
      ○ traceW-resp-≈ (K.∘-resp-≈ˡ (⟺ tensor-idˡ))
  ; tightenₗ    = traceW-resp-≈ (K.∘-resp-≈ˡ tensor-idʳ) ○ tightenₗW
  ; tightenᵣ    = traceW-resp-≈ (K.∘-resp-≈ʳ tensor-idʳ) ○ tightenᵣW
  ; vanishing₁  = traceW-resp-≈ tensor-idʳ ○ vanishing₁W
  ; vanishing₂  = traceW-resp-≈ (traceW-resp-≈ pure-sandwich) ○ vanishing₂W
  ; superposing =
      traceW-resp-≈ (pure-sandwich ○ refl⟩∘⟨ tensor-idˡ ⟩∘⟨refl) ○ superposingW ○ ⟺ tensor-idˡ
  ; yanking = yankingW
  }
