{-# OPTIONS --safe --guardedness #-}

module CategoricalCrypto.Machine.Relational.Presentation.ClassicalFunctor where

open import Axiom.ExcludedMiddle
open import Categories.Category.Monoidal.Bundle
open import Categories.Functor using (Functor)
open import Data.Product.Base
open import Level using (0ℓ)
open import Relation.Binary.PropositionalEquality

import CategoricalCrypto.Channel.Core as Ch
open import CategoricalCrypto.Iface
open import CategoricalCrypto.Machine.Relational
import CategoricalCrypto.Machine.Relational.Model as Native
import CategoricalCrypto.Machine.Relational.Wiring as W
import CategoricalCrypto.Machine.Relational.Presentation.Classical as Classical
import CategoricalCrypto.Machine.Relational.Presentation.ClassicalStructural as Structural
import CategoricalCrypto.Machine.Relational.Presentation.ClassicalTensor as Tensor
import CategoricalCrypto.Machine.Relational.Presentation.ClassicalWiring as Wiring
open import CategoricalCrypto.Machine.Relational.Presentation.Descent using (channel; canonical)
import CategoricalCrypto.Machines.Positive.Bridge as Bridge
import CategoricalCrypto.Machines.Positive.Model as Model
import CategoricalCrypto.Machines.Positive.Raw as Raw
import CategoricalCrypto.Machines.Positive.Repack as Re
import CategoricalCrypto.UC.Machine as UC
import CategoricalCrypto.UC.Machine.Wire.Algebra as Wire
import CategoricalCrypto.UC.Model.Seal as Seal

private
  module R = Re.At 0ℓ
  module G = Raw.At 0ℓ
  module Q = MonoidalCategory Model.𝔾₊

object : Q.Obj → Ch.Channel
object A = channel (Seal.objᵒ A)

object-iface : ∀ A → object (Seal.ifaceᵒ A) ≡ channel A
object-iface A = cong channel (Seal.objᵒ-ifaceᵒ A)

module WithLEM (lem : ExcludedMiddle 0ℓ) where
  open Classical.WithLEM lem
  open Wiring.WithLEM lem
  open Structural.WithLEM lem

  opaque
    unfolding Seal.𝔾ᵒ Seal.objᵒ Seal.procᵒ Seal.ifaceᵒ Seal.objᵒ-ifaceᵒ
              Ch._⊗₀_ compile-step canonical Model.positive-congruence Model._≈⁺_

    arrow : {A B : Q.Obj} → A Q.⇒ B → Initialized (object A) (object B)
    arrow f = compile (R.repack f)

    arrow-cong : {A B : Q.Obj} {f g : A Q.⇒ B} → f Q.≈ g → arrow f ≈ᴿ arrow g
    arrow-cong eq = congruence eq

    arrow-id : {A : Q.Obj} → arrow (Q.id {A}) ≈ᴿ W.id
    arrow-id = ≈ᴿ-trans (congruence (R.repack-resp (R.PS.⟺ᴹ Wire.wire-id))) wire-id

    arrow-compose : {A B C : Q.Obj} (g : B Q.⇒ C) (f : A Q.⇒ B)
      → arrow (g Q.∘ f) ≈ᴿ (arrow g W.∘ arrow f)
    arrow-compose g f = ≈ᴿ-trans
      (congruence (R.QS._○ᴹ_ (R.repack-resp (R.PS.⟺ᴹ (G.composeₚ-project g f)))
        (Bridge.repack-compose 0ℓ g f)))
      (compose (R.repack g) (R.repack f))

    canonical-agreement : {A B : Iface} (f : UC.Proc A B)
      → subst₂ Initialized (object-iface A) (object-iface B) (arrow (Seal.procᵒ f)) ≈ᴿ canonical f
    canonical-agreement f = ≈ᴿ-refl

  functor : Functor Q.U Native.𝔾ᴿ
  functor = record
    { F₀ = object ; F₁ = arrow
    ; identity = arrow-id
    ; homomorphism = λ { {f = f} {g} → arrow-compose g f }
    ; F-resp-≈ = arrow-cong
    }
