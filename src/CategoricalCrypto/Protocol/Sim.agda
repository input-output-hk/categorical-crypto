{-# OPTIONS --safe --without-K #-}

-- Simulations of protocols: a state map under which each step tree becomes the
-- other's, trees compared by `_≈ᶜ_` (extensional, so no funext).  The hom
-- equality is their equivalence closure, as for machines (`Machines.Sim`).

open import Data.Product.Base
open import Function.Base
open import Level
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
import Relation.Binary.Construct.Closure.Equivalence as EqC

open import CategoricalCrypto.Iface
open import CategoricalCrypto.Protocol

module CategoricalCrypto.Protocol.Sim where

private variable A B : Iface

infix 4 _≈ᶜ_ _≲ᵖ_ _≈ᵖ_

data _≈ᶜ_ {A : Iface} {X : Set} : Calls A X → Calls A X → Set where
  ret  : ∀ {x x′} → x ≡ x′ → ret x ≈ᶜ ret x′
  call : ∀ {q k k′} → (∀ r → k r ≈ᶜ k′ r) → call q k ≈ᶜ call q k′
  coin : ∀ {μ k k′} → (∀ b → k b ≈ᶜ k′ b) → coin μ k ≈ᶜ coin μ k′
  dead : dead ≈ᶜ dead

record _≲ᵖ_ (P P′ : Protocol A B) : Set where
  field θ      : St P → St P′
        θ-init : θ (init P) ≡ init P′
        θ-step : ∀ s b⁻ → step P s b⁻ >>=ᶜ (ret ∘ map₁ θ) ≈ᶜ step P′ (θ s) b⁻
open _≲ᵖ_ public

_≈ᵖ_ : Rel (Protocol A B) (suc 0ℓ)
_≈ᵖ_ = EqC.EqClosure _≲ᵖ_
