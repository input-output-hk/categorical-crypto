{-# OPTIONS --safe --without-K --guardedness #-}

-- A choice is selected on demand: the first activation is retained until the
-- new choice factor supplies its pick. Branch initialisation happens only
-- after that pick; requests by the selected branch remain online.

open import Categories.Category using (Category)
open import Categories.Category.Monoidal.Bundle

open import Data.List.Base using (List; []; _∷_; _++_)
open import Data.Product.Base
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Unit.Base using (tt)
import Data.Unit.Polymorphic.Base as PolyUnit
open import Level using (0ℓ)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import ProbabilisticLogic.Dp

open import CategoricalCrypto.Iface
open import CategoricalCrypto.Machines.Base
open import CategoricalCrypto.ND.PM.Factor
open import CategoricalCrypto.ND.Relabel using (Pick)
open import CategoricalCrypto.SSP.Iface using (Ch)
open import CategoricalCrypto.ND.SSP.Choice using (Cᴵ⟦_⟧)
open import CategoricalCrypto.UC.Machine

import CategoricalCrypto.Machines.Core as Core

module CategoricalCrypto.ND.PM.Choice where

private
  module MC = Core (𝒱ₚ 0ℓ)
  variable
    A B D : Iface
    S : Set
    S⃗ T⃗ : List Set

Proc⁺ : List Set → Iface → Iface → Set₁
Proc⁺ S⃗ A B = Proc A (Cᶠ S⃗ ⊗ᴵ B)

module Online {S : Set} {S⃗ : List Set} {A B : Iface} (P : S → Proc⁺ S⃗ A B) where
  Input : Set
  Input = Pos A ⊎ (Pick S⃗ ⊎ Neg B)

  data State : Set where
    fresh : State
    wait : Input → State
    active : (s : S) → MC.St (P s) → State

  emit : Neg A ⊎ (Ch Cᴵ⟦ S⃗ ⟧ ⊎ Pos B) → Neg A ⊎ ((Ch Cᴵ⟦ S ∷ S⃗ ⟧) ⊎ Pos B)
  emit (inj₁ a) = inj₁ a
  emit (inj₂ (inj₁ c)) = inj₂ (inj₁ (inj₂ c))
  emit (inj₂ (inj₂ b)) = inj₂ (inj₂ b)

  run : (s : S) → MC.St (P s) → Input → Dₚ (State × (Neg A ⊎ (Ch Cᴵ⟦ S ∷ S⃗ ⟧ ⊎ Pos B)))
  run s t i = mapₚ (λ (t′ , o) → active s t′ , emit o) (MC.step (P s) (t , i))

  feed : State → Input → Dₚ (State × (Neg A ⊎ (Ch Cᴵ⟦ S ∷ S⃗ ⟧ ⊎ Pos B)))
  feed fresh i = returnₚ (wait i , inj₂ (inj₁ (inj₁ tt)))
  feed (wait _) _ = botₚ
  feed (active s t) i = run s t i

  step : State × (Pos A ⊎ (Pick (S ∷ S⃗) ⊎ Neg B))
       → Dₚ (State × (Neg A ⊎ (Ch Cᴵ⟦ S ∷ S⃗ ⟧ ⊎ Pos B)))
  step (t , inj₁ a) = feed t (inj₁ a)
  step (wait i , inj₂ (inj₁ (inj₁ _ , s))) = MC.point (MC.state (P s)) PolyUnit.tt >>=ₚ λ t → run s t i
  step (fresh , inj₂ (inj₁ (inj₁ _ , _))) = botₚ
  step (active _ _ , inj₂ (inj₁ (inj₁ _ , _))) = botₚ
  step (t , inj₂ (inj₁ (inj₂ c , p))) = feed t (inj₂ (inj₁ (c , p)))
  step (t , inj₂ (inj₂ b)) = feed t (inj₂ (inj₂ b))

  machine : Proc⁺ (S ∷ S⃗) A B
  machine = MC.mk (initˢ State fresh) step

  choose-request : (a : Pos A) → step (fresh , inj₁ a) ≡ returnₚ (wait (inj₁ a) , inj₂ (inj₁ (inj₁ tt)))
  choose-request _ = refl

  choose-resume : (i : Input) (s : S)
                → step (wait i , inj₂ (inj₁ (inj₁ tt , s))) ≡ (MC.point (MC.state (P s)) PolyUnit.tt >>=ₚ λ t → run s t i)
  choose-resume _ _ = refl

choose : (S → Proc⁺ S⃗ A B) → Proc⁺ (S ∷ S⃗) A B
choose {S} {S⃗} {A} {B} = Online.machine {S} {S⃗} {A} {B}
