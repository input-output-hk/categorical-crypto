{-# OPTIONS --safe --guardedness #-}

module CategoricalCrypto.Machine.Relational.Presentation.ClassicalSetup where

open import Axiom.ExcludedMiddle
open import Categories.Category.Monoidal.Bundle
open import Categories.Functor using (Functor)
open import Categories.Functor.Monoidal
open import Categories.Functor.Presheaf.Morphism
open import Categories.NaturalTransformation using (ntHelper)
open import Function.Bundles
open import Level using (0ℓ)
open import Relation.Binary.Bundles
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)

import CategoricalCrypto.Channel.Core as Ch
open import CategoricalCrypto.Iface
import CategoricalCrypto.UC.Machine as UC
open import CategoricalCrypto.Machine.Relational.Presentation.Descent using (canonical)
open import CategoricalCrypto.Machine.Relational
import CategoricalCrypto.Machine.Relational.Model as NativeModel
import CategoricalCrypto.Machine.Relational.Observation as Observation
import CategoricalCrypto.Machine.Relational.Setup as Native
import CategoricalCrypto.Machine.Relational.Wiring as W
import CategoricalCrypto.Machine.Relational.Presentation.Classical as Classical
import CategoricalCrypto.Machine.Relational.Presentation.ClassicalFunctor as F
import CategoricalCrypto.Machine.Relational.Presentation.ClassicalMonoidal as Monoidal
import CategoricalCrypto.Machine.Relational.Presentation.ClassicalTests as Tests
import CategoricalCrypto.Machines.Positive.Model as Model
import CategoricalCrypto.Machines.Positive.Repack as Re
import CategoricalCrypto.Machines.Positive.Setup as Positive
import CategoricalCrypto.UC.Model.Seal as Seal
import CategoricalCrypto.UC.Model.Setup as PM
import CategoricalCrypto.Standard2.Morphism as StdM
open import CategoricalCrypto.UCSetup.Morphism

private
  module Q = MonoidalCategory Model.𝔾₊
  module R = Re.At 0ℓ

module WithLEM (lem : ExcludedMiddle 0ℓ) where
  module C = Classical.WithLEM lem
  module Map = F.WithLEM lem
  module Strong = Monoidal.WithLEM lem
  module T = Tests.WithLEM lem

  opaque
    unfolding Seal.𝔾ᵒ Seal.objᵒ Seal.ifaceᵒ Seal.procᵒ Map.arrow Model.positive-congruence
              Seal.objᵒ-ifaceᵒ C.compile-step Ch._⊗₀_ canonical

    tests : PresheafMorphism Map.functor Positive.ℰ₊ Native.ℰᴿ
    tests = record { ν = ntHelper record
      { η = λ A → record
        { to = λ t → C.compile (R.repack t)
        ; cong = T.tests-cong }
      ; commute = λ f {t} m → Observation.eval-resp
          (W.∘-cong (Map.arrow-compose t f) ≈ᴿ-refl)
      } }

    test-canonical : ∀ {A} (t : UC.Proc A UC.Ωᴵ)
      → subst (λ X → Initialized X Observation.Ω) (F.object-iface A)
          (PresheafMorphism.η tests (Seal.ifaceᵒ A) ⟨$⟩ Seal.procᵒ t) ≈ᴿ canonical t
    test-canonical t = ≈ᴿ-refl

  PMmay→native : UCSetupMorphism Positive.Target.StdSetup Native.StdSetup
  PMmay→native = StdM.StdUCMorphism Model.𝔾₊ NativeModel.𝔾ᴿᵐ Positive.ℰ₊ Native.ℰᴿ
    Strong.PMmay→native tests

  PM→native : UCSetupMorphism PM.StdSetup Native.StdSetup
  PM→native = composeᵁ PMmay→native Positive.PM→positive

  private
    module Direct = UCSetupMorphism PM→native
    module May = UCSetupMorphism PMmay→native
    module Forget = UCSetupMorphism Positive.PM→positive
    module DirectStrong = StrongMonoidalFunctor Strong.PM→native

  forgetting-objects : ∀ A → Direct.F.₀ A ≡ DirectStrong.F₀ A
  forgetting-objects A = refl

  forgetting-arrows : ∀ {A B} (f : A PM.⇒ B)
    → Direct.F.₁ f ≈ᴿ DirectStrong.F₁ f
  forgetting-arrows f = ≈ᴿ-refl

  forgetting-tests : ∀ {A} (t : Setoid.Carrier (Functor.F₀ PM.ℰᵒ A))
    → Setoid._≈_ (Functor.F₀ Native.ℰᴿ (Direct.F.₀ A))
       (Direct.ν.η A ⟨$⟩ t)
       (May.ν.η (Forget.F.₀ A) ⟨$⟩ (Forget.ν.η A ⟨$⟩ t))
  forgetting-tests {A} t = Setoid.refl (Functor.F₀ Native.ℰᴿ (Direct.F.₀ A))

  original-test-canonical : ∀ {A} (t : UC.Proc A UC.Ωᴵ)
    → subst (λ X → Initialized X Observation.Ω) (F.object-iface A)
        (Direct.ν.η (Seal.ifaceᵒ A) ⟨$⟩ Seal.procᵒ t) ≈ᴿ canonical t
  original-test-canonical = test-canonical
