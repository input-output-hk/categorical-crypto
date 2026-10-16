{-# OPTIONS --safe --guardedness #-}

module CategoricalCrypto.Machine.Relational.Presentation.ClassicalTensor where

open import Axiom.ExcludedMiddle
open import Data.Product.Base
open import Data.Sum.Base
open import Data.Unit.Polymorphic.Base
open import Function.Base using (id)
open import Level using (0ℓ)
open import Relation.Binary.PropositionalEquality

open import ProbabilisticLogic.Dp
open import ProbabilisticLogic.Dp.Reasoning

open import CategoricalCrypto.Channel.Core
open import CategoricalCrypto.Machine.Relational
import CategoricalCrypto.Machine.Relational.Wiring as W
import CategoricalCrypto.Machine.Relational.Presentation.Classical as Classical
import CategoricalCrypto.Machine.Relational.Presentation.ClassicalWiring as Wiring
import CategoricalCrypto.Machine.Relational.Presentation.Positive as EP
import CategoricalCrypto.Machine.Relational.Presentation.Wiring as PW
import CategoricalCrypto.Machines.Pointwise as Point
import CategoricalCrypto.Machines.Pure as Pure
import CategoricalCrypto.Machines.Sandwich as Sandwich
import CategoricalCrypto.Machines.Positive.Raw as Raw
import CategoricalCrypto.Machines.Positive.Repack as Re
import CategoricalCrypto.Machines.Positive.Tensor as Tensor

private
  module R = Re.At 0ℓ
  module G = Raw.At 0ℓ
  variable A B C D : Channel

module WithLEM (lem : ExcludedMiddle 0ℓ) where
  open Classical.WithLEM lem
  open Wiring.WithLEM lem

  opaque
    unfolding _⊗₀_

    tensor-proc : EP.Proc A B → EP.Proc C D → EP.Proc (A ⊗₀ C) (B ⊗₀ D)
    tensor-proc f g = G.tensor₊ f g

  module Proof (f : EP.Proc A B) (g : EP.Proc C D) where
    private
      p = R.unpack f
      q = R.unpack g
      P = PW.tensor-presentation (present f) (present g)
      native₀ = R.unpack (EP.toPositive P)
      normal = Sandwich.sandwichᴹ (p R.PT.⊗ᵉ q) Pure.midfn Pure.midfn
      Input Output : Set
      Input = (Channel.inType A ⊎ Channel.inType C) ⊎ (Channel.outType B ⊎ Channel.outType D)
      Output = (Channel.outType A ⊎ Channel.outType C) ⊎ (Channel.inType B ⊎ Channel.inType D)

    opaque
      unfolding _⊗₀_

      native-step : (R.Q.St f × R.Q.St g) × Input → Dₚ ((R.Q.St f × R.Q.St g) × Output)
      native-step = R.P.step native₀

    private
      native : R.P.Machine Input Output
      native = R.P.mk (R.P.state native₀) native-step

    left : ∀ s t i → R.P.step (p R.PT.⊗ᵉ q) ((s , t) , inj₁ i)
      ≈ₚ mapₚ (λ r → (proj₁ r , t) , inj₁ (proj₂ r)) (R.P.step p (s , i))
    left s t i = Pure.tstep-inj₁ (R.P.onL (R.P.step p)) (R.P.onR (R.P.step q)) (s , t) i
      ⟨≈⟩ bindˣ (Point.onL-pt (R.P.step p) s t i)
      ⟨≈⟩ map-fuse (R.P.step p (s , i)) (λ r → (proj₁ r , t) , proj₂ r)
        (λ r → proj₁ r , inj₁ (proj₂ r)) (λ r → (proj₁ r , t) , inj₁ (proj₂ r)) (λ _ → refl)

    right : ∀ s t i → R.P.step (p R.PT.⊗ᵉ q) ((s , t) , inj₂ i)
      ≈ₚ mapₚ (λ r → (s , proj₁ r) , inj₂ (proj₂ r)) (R.P.step q (t , i))
    right s t i = Pure.tstep-inj₂ (R.P.onL (R.P.step p)) (R.P.onR (R.P.step q)) (s , t) i
      ⟨≈⟩ bindˣ (Point.onR-pt (R.P.step q) s t i)
      ⟨≈⟩ map-fuse (R.P.step q (t , i)) (λ r → (s , proj₁ r) , proj₂ r)
        (λ r → proj₁ r , inj₂ (proj₂ r)) (λ r → (s , proj₁ r) , inj₂ (proj₂ r)) (λ _ → refl)

    opaque
      unfolding _⊗₀_ destruct-⊗ construct-⊗ ⊗-sym ⊗-right-assoc ⊗-left-assoc
                ⊗-right-intro ⊗-ᵀ-distrib ⊗-ᵀ-factor ⊗-right-neutral ⊗-fusion ⊗-combine
                compile-step present EP.positive-step PW.tensor-presentation PW.pair-presentation PW.pair-step native-step

      step-square : ∀ z → R.P.step normal z ≈ₚ R.P.step native z
      step-square ((s , t) , inj₁ (inj₁ i)) = map-arg _ (left s t (inj₁ i))
        ⟨≈⟩ map-eq _ _ _ (λ { (_ , inj₁ (inj₁ _)) → refl ; (_ , inj₁ (inj₂ _)) → refl
                            ; (_ , inj₂ (inj₁ _)) → refl ; (_ , inj₂ (inj₂ _)) → refl })
      step-square ((s , t) , inj₁ (inj₂ i)) = map-arg _ (right s t (inj₁ i))
        ⟨≈⟩ map-eq _ _ _ (λ { (_ , inj₁ (inj₁ _)) → refl ; (_ , inj₁ (inj₂ _)) → refl
                            ; (_ , inj₂ (inj₁ _)) → refl ; (_ , inj₂ (inj₂ _)) → refl })
      step-square ((s , t) , inj₂ (inj₁ i)) = map-arg _ (left s t (inj₂ i))
        ⟨≈⟩ map-eq _ _ _ (λ { (_ , inj₁ (inj₁ _)) → refl ; (_ , inj₁ (inj₂ _)) → refl
                            ; (_ , inj₂ (inj₁ _)) → refl ; (_ , inj₂ (inj₂ _)) → refl })
      step-square ((s , t) , inj₂ (inj₂ i)) = map-arg _ (right s t (inj₂ i))
        ⟨≈⟩ map-eq _ _ _ (λ { (_ , inj₁ (inj₁ _)) → refl ; (_ , inj₁ (inj₂ _)) → refl
                            ; (_ , inj₂ (inj₁ _)) → refl ; (_ , inj₂ (inj₂ _)) → refl })

      point-square : mapₚ id (R.P.point (R.P.state normal) tt) ≈ₚ R.P.point (R.P.state native) tt
      point-square = >>=ₚ-identityʳ _ ⟨≈⟩ Point.point-⊛ (R.P.state p) (R.P.state q) tt

      normal-native : normal R.PS.≈ᴹ native
      normal-native = R.PS.≲⇒≈ᴹ (Point.simFn id (λ { tt → point-square })
        (λ z → >>=ₚ-identityʳ _ ⟨≈⟩ step-square z))

    opaque
      unfolding _⊗₀_ tensor-proc native-step

      agreement : tensor-proc f g R.QS.≈ᴹ EP.toPositive P
      agreement = R.QS._○ᴹ_ (R.QS.⟺ᴹ (Tensor.normal-form f g))
        (R.QS._○ᴹ_ (R.repack-resp normal-native) (R.repack-unpack (EP.toPositive P)))

  opaque
    unfolding _⊗₀_

    tensor : (f : EP.Proc A B) (g : EP.Proc C D)
      → compile (tensor-proc f g) ≈ᴿ (compile f W.⊗₁ compile g)
    tensor f g = ≈ᴿ-trans (congruence (Proof.agreement f g))
      (presentation (PW.tensor-presentation (present f) (present g)))
