{-# OPTIONS --safe --without-K --guardedness #-}

-- `UC.Machine.Relational` across the seal (`UC.Model.Seal`'s third
-- discipline): interface maps on `𝔾ᵒ`'s objects and the relation on its homs,
-- exported with their closure laws from inside one `opaque` block, so that a
-- consumer relating two interpretations of a circuit never unfolds `𝔾ᵒ`.

module CategoricalCrypto.UC.Model.Relational where

open import Categories.Category.Monoidal.Bundle
import Categories.Category.Monoidal.Utilities as MU

open import Data.Product.Base using (_,_)
import Data.Sum.Base as Sum
open import Level
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst₂)

open import CategoricalCrypto.Iface
open import CategoricalCrypto.Machines.Pointwise using (module K)
open import CategoricalCrypto.Machines.Sim.Relational.Pointwise using (module RS)
open import CategoricalCrypto.UC.Machine
open import CategoricalCrypto.UC.Model.Seal

import CategoricalCrypto.UC.Machine.Relational as UM

private
  module G = MonoidalCategory 𝔾ᵒ

open MU.Shorthands G.monoidal

private variable
  A A′ C C′ : Iface
  X X′ Y Y′ Z Z′ W W′ : G.Obj

infixr 10 _⊗ᵐ_

opaque
  unfolding 𝔾ᵒ ifaceᵒ procᵒ ⊗ᵒ

  -- Letter maps, forward on both polarities.
  Mapᵒ : G.Obj → G.Obj → Set
  Mapᵒ = UM.Map

  idᵐ : Mapᵒ X X
  idᵐ = UM.idᵐ

  _⊗ᵐ_ : Mapᵒ X X′ → Mapᵒ Y Y′ → Mapᵒ (X G.⊗₀ Y) (X′ G.⊗₀ Y′)
  _⊗ᵐ_ = UM._⊗ᵐ_

  ifaceᵐ : (Pos A → Pos A′) → (Neg A → Neg A′) → Mapᵒ (ifaceᵒ A) (ifaceᵒ A′)
  ifaceᵐ a⁺ a⁻ = a⁺ , a⁻

  ifaceᵐ-id : ifaceᵐ {A} (λ a → a) (λ a → a) ≡ idᵐ
  ifaceᵐ-id = refl

  ifaceᵐ-⊗ : {a⁺ : Pos A → Pos A′} {a⁻ : Neg A → Neg A′} {c⁺ : Pos C → Pos C′} {c⁻ : Neg C → Neg C′}
           → ifaceᵐ a⁺ a⁻ ⊗ᵐ ifaceᵐ c⁺ c⁻
           ≡ subst₂ Mapᵒ (sym (⊗ᵒ A C)) (sym (⊗ᵒ A′ C′)) (ifaceᵐ (Sum.map a⁺ c⁺) (Sum.map a⁻ c⁻))
  ifaceᵐ-⊗ = refl

  HSimᵒ : Mapᵒ X X′ → Mapᵒ Y Y′ → X G.⇒ Y → X′ G.⇒ Y′ → Set₁
  HSimᵒ = UM.HSim

  HSimᵒ-resp : {μ : Mapᵒ X X′} {ν : Mapᵒ Y Y′} {f f′ : X G.⇒ Y} {g g′ : X′ G.⇒ Y′}
             → f′ G.≈ f → HSimᵒ μ ν f g → g G.≈ g′ → HSimᵒ μ ν f′ g′
  HSimᵒ-resp = UM.HSim-resp

  -- Along identities the relation is the hom equality.
  HSimᵒ⇒≈ : {f g : X G.⇒ Y} → HSimᵒ (idᵐ {X}) (idᵐ {Y}) f g → f G.≈ g
  HSimᵒ⇒≈ = UM.HSim⇒≈ᴹ

  HSimᵒ-proc : {B B′ : Iface} {p : Proc A B} {q : Proc A′ B′}
               (a⁺ : Pos A → Pos A′) (a⁻ : Neg A → Neg A′) (b⁺ : Pos B → Pos B′) (b⁻ : Neg B → Neg B′)
             → p RS.≲[ K.pureᵏ (Sum.map a⁺ b⁻) ∣ K.pureᵏ (Sum.map a⁻ b⁺) ] q
             → HSimᵒ (ifaceᵐ a⁺ a⁻) (ifaceᵐ b⁺ b⁻) (procᵒ p) (procᵒ q)
  HSimᵒ-proc _ _ _ _ = UM.≲[]⇒HSim

  HSimᵒ-id : (μ : Mapᵒ X X′) → HSimᵒ μ μ (G.id {X}) (G.id {X′})
  HSimᵒ-id = UM.HSim-id

  HSimᵒ-∘ : {μX : Mapᵒ X X′} {μY : Mapᵒ Y Y′} {μZ : Mapᵒ Z Z′}
            {g : Y G.⇒ Z} {g′ : Y′ G.⇒ Z′} {f : X G.⇒ Y} {f′ : X′ G.⇒ Y′}
          → HSimᵒ μY μZ g g′ → HSimᵒ μX μY f f′ → HSimᵒ μX μZ (g G.∘ f) (g′ G.∘ f′)
  HSimᵒ-∘ = UM.HSim-∘

  HSimᵒ-⊗ : {μX : Mapᵒ X X′} {μY : Mapᵒ Y Y′} {μZ : Mapᵒ Z Z′} {μW : Mapᵒ W W′}
            {f : X G.⇒ Y} {f′ : X′ G.⇒ Y′} {g : Z G.⇒ W} {g′ : Z′ G.⇒ W′}
          → HSimᵒ μX μY f f′ → HSimᵒ μZ μW g g′
          → HSimᵒ (μX ⊗ᵐ μZ) (μY ⊗ᵐ μW) (f G.⊗₁ g) (f′ G.⊗₁ g′)
  HSimᵒ-⊗ = UM.HSim-⊗

  HSimᵒ-λ⇒ : (μ : Mapᵒ X X′) → HSimᵒ (idᵐ {G.unit} ⊗ᵐ μ) μ (λ⇒ {X}) (λ⇒ {X′})
  HSimᵒ-λ⇒ = UM.HSim-λ⇒

  HSimᵒ-λ⇐ : (μ : Mapᵒ X X′) → HSimᵒ μ (idᵐ {G.unit} ⊗ᵐ μ) (λ⇐ {X}) (λ⇐ {X′})
  HSimᵒ-λ⇐ = UM.HSim-λ⇐

  HSimᵒ-ρ⇒ : (μ : Mapᵒ X X′) → HSimᵒ (μ ⊗ᵐ idᵐ {G.unit}) μ (ρ⇒ {X}) (ρ⇒ {X′})
  HSimᵒ-ρ⇒ = UM.HSim-ρ⇒

  HSimᵒ-ρ⇐ : (μ : Mapᵒ X X′) → HSimᵒ μ (μ ⊗ᵐ idᵐ {G.unit}) (ρ⇐ {X}) (ρ⇐ {X′})
  HSimᵒ-ρ⇐ = UM.HSim-ρ⇐

  HSimᵒ-α⇒ : (μX : Mapᵒ X X′) (μY : Mapᵒ Y Y′) (μZ : Mapᵒ Z Z′)
           → HSimᵒ ((μX ⊗ᵐ μY) ⊗ᵐ μZ) (μX ⊗ᵐ (μY ⊗ᵐ μZ)) (α⇒ {X} {Y} {Z}) (α⇒ {X′} {Y′} {Z′})
  HSimᵒ-α⇒ = UM.HSim-α⇒

  HSimᵒ-α⇐ : (μX : Mapᵒ X X′) (μY : Mapᵒ Y Y′) (μZ : Mapᵒ Z Z′)
           → HSimᵒ (μX ⊗ᵐ (μY ⊗ᵐ μZ)) ((μX ⊗ᵐ μY) ⊗ᵐ μZ) (α⇐ {X} {Y} {Z}) (α⇐ {X′} {Y′} {Z′})
  HSimᵒ-α⇐ = UM.HSim-α⇐
