{-# OPTIONS --safe --guardedness #-}

module CategoricalCrypto.Machine.Relational.Presentation.ClassicalWiring where

open import Axiom.ExcludedMiddle
open import Data.Product.Base
open import Data.Sum.Base
open import Data.Unit.Polymorphic.Base
open import Function.Base using (id)
open import Level using (0ℓ)
open import Relation.Binary.PropositionalEquality

open import ProbabilisticLogic.Dp
open import ProbabilisticLogic.Dp.Positive.Monad

open import CategoricalCrypto.Channel.Core
open import CategoricalCrypto.Machine.Relational
open import CategoricalCrypto.Machine.Relational.Presentation
open import CategoricalCrypto.Machine.Relational.Presentation.Canonical
import CategoricalCrypto.Machine.Relational.Presentation.Classical as Classical
import CategoricalCrypto.Machine.Relational.Presentation.Coherence as Coherence
open import CategoricalCrypto.Machine.Relational.Presentation.Composition
import CategoricalCrypto.Machine.Relational.Presentation.Feedback as Feedback
import CategoricalCrypto.Machine.Relational.Presentation.Positive as EP
import CategoricalCrypto.Machine.Relational.Presentation.Trace as Trace
import CategoricalCrypto.Machine.Relational.Wiring as W
import CategoricalCrypto.Machines.Positive.Feedback as F
import CategoricalCrypto.Machines.Positive.Pointwise as Point
import CategoricalCrypto.Machines.Positive.Raw as Raw
import CategoricalCrypto.Machines.Positive.Repack as Re

private
  module R = Re.At 0ℓ
  module G = Raw.At 0ℓ
  variable A B C : Channel

module WithLEM (lem : ExcludedMiddle 0ℓ) where
  open Classical.WithLEM lem

  opaque
    unfolding _⊗₀_ compile-step EP.positive-step

    present : (f : EP.Proc A B) → Presentation (compile f)
    present f = presentₚ (R.Q.point (R.Q.state f) tt) (λ s i → R.Q.step f (s , i))

    roundtrip : (f : EP.Proc A B) → EP.toPositive (present f) R.QS.≈ᴹ f
    roundtrip f = R.QS.≲⇒≈ᴹ (Point.simFn id
      (λ { tt → ≈ₚ⇒≈₊ (>>=ₚ-identityʳ _) })
      (λ p → ≈ₚ⇒≈₊ (>>=ₚ-identityʳ _)))

  compose : (g : EP.Proc B C) (f : EP.Proc A B)
    → compile (G.compose₊ g f) ≈ᴿ (compile g W.∘ compile f)
  compose {B} {C} {A} g f = ≈ᴿ-trans
    (congruence (R.QS._○ᴹ_ (G.compose₊-project g f)
      (R.QS._○ᴹ_ (G.QG.∘-resp-≈ {EP.interface A} {EP.interface B} {EP.interface C}
        (R.QS.⟺ᴹ (roundtrip g)) (R.QS.⟺ᴹ (roundtrip f)))
        (R.QS.⟺ᴹ (Coherence.toPositive-compose (present g) (present f))))))
    (presentation (compose-presentation (present g) (present f)))

  feedback : (f : EP.Proc (A ⊗₀ C) (B ⊗₀ C))
    → compile (F.feedback₊ (Feedback.tensor-positive (present f))) ≈ᴿ W.trace (compile f)
  feedback f = ≈ᴿ-trans (congruence (R.QS.⟺ᴹ (Feedback.toPositive-trace (present f))))
    (presentation (Trace.trace-presentation (present f)))
