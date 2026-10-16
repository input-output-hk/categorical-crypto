{-# OPTIONS --safe --guardedness #-}

-- Exact-label descent already forces literal support congruence on one-state
-- machines: stable equality unconditionally, decidable equality with funext.
module CategoricalCrypto.Machine.Relational.Presentation.Descent where

open import Axiom.Extensionality.Propositional
open import Categories.Category.Monoidal.Bundle
open import Categories.Functor using (Functor)
open import Categories.Functor.Monoidal using (StrongMonoidalFunctor)
open import Data.Empty
open import Data.Maybe.Base
open import Data.Product.Base
open import Data.Sum.Base
open import Data.Sum.Properties using (inj₂-injective)
open import Data.Unit.Polymorphic.Base
open import Level using (0ℓ)
open import Relation.Binary.Definitions using (DecidableEquality)
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary.Negation

open import ProbabilisticLogic.Dp
open import ProbabilisticLogic.Dp.Positive
open import ProbabilisticLogic.Dp.Positive.Composition
open import ProbabilisticLogic.Dp.Positive.Decidability
open import ProbabilisticLogic.Dp.Positive.Monad
open import ProbabilisticLogic.Dp.Reasoning

import CategoricalCrypto.Channel.Core as Ch
open import CategoricalCrypto.Iface
open import CategoricalCrypto.Machine.Relational
open import CategoricalCrypto.Machine.Relational.Presentation.Canonical
import CategoricalCrypto.Machines.Positive.Model as Model
import CategoricalCrypto.Machines.Positive.Repack as Re
import CategoricalCrypto.UC.Machine as UC
import CategoricalCrypto.UC.Model.Seal as Seal

private
  module R = Re.At 0ℓ
  module P = MonoidalCategory Seal.𝔾ᵒ
  module Q = MonoidalCategory Model.𝔾₊
  module F = StrongMonoidalFunctor Model.forget-probabilities
  module Forget = Functor F.F
  variable
    A B : Iface
    X : Set
    d e : Dₚ X
    x y : X

channel : Iface → Ch.Channel
channel A = Pos A Ch.⇿ Neg A

opaque
  unfolding Ch._⊗₀_

  canonical : UC.Proc A B → Initialized (channel A) (channel B)
  canonical f = fromₚ (R.P.point (R.P.state f) tt) (λ s i → R.P.step f (s , i))

-- These hypotheses concern the public sealed categories, not a surrogate
-- equality on kernels or an equality defined by compiling native relations.
PMDescent : Set₁
PMDescent = ∀ {A B} {f g : UC.Proc A B}
  → Seal.procᵒ {A} {B} f P.≈ Seal.procᵒ {A} {B} g
  → canonical {A} {B} f ≈ᴿ canonical {A} {B} g

PMmayDescent : Set₁
PMmayDescent = ∀ {A B} {f g : UC.Proc A B}
  → Forget.F₁ (Seal.procᵒ {A} {B} f) Q.≈ Forget.F₁ (Seal.procᵒ {A} {B} g)
  → canonical {A} {B} f ≈ᴿ canonical {A} {B} g

pmmay-descent⇒pm-descent : PMmayDescent → PMDescent
pmmay-descent⇒pm-descent descend {A} {B} eq = descend {A} {B} (Forget.F-resp-≈ eq)

emit : Dₚ X → UC.Proc (⊤ ⇿ ⊥) (X ⇿ ⊥)
emit d = R.P.mk R.P.Iˢ (λ p → mapₚ (λ x → proj₁ p , inj₂ x) d)

emit-resp : d ≈ₚ e
  → Seal.procᵒ {⊤ ⇿ ⊥} {X ⇿ ⊥} (emit d) P.≈ Seal.procᵒ {⊤ ⇿ ⊥} {X ⇿ ⊥} (emit e)
emit-resp eq = Seal.≈ᴹ⇒≈ᵒ {⊤ ⇿ ⊥} {_ ⇿ ⊥}
  (R.PS.≲⇒≈ᴹ (R.PS.mk-cong (λ p → map-arg (λ x → proj₁ p , inj₂ x) eq)))

emit-positive-resp : d ≈₊ e
  → Forget.F₁ (Seal.procᵒ {⊤ ⇿ ⊥} {X ⇿ ⊥} (emit d)) Q.≈
    Forget.F₁ (Seal.procᵒ {⊤ ⇿ ⊥} {X ⇿ ⊥} (emit e))
emit-positive-resp eq = Model.pack-positive-resp {⊤ ⇿ ⊥} {_ ⇿ ⊥}
  (R.QS.≲⇒≈ᴹ (R.QS.mk-cong (λ p → map-cong (λ x → proj₁ p , inj₂ x) eq)))

opaque
  unfolding Ch._⊗₀_ canonical

  emit-bisim⇒support : canonical (emit d) ≈ᴿ canonical (emit e)
    → Positive d x → Positive e x
  emit-bisim⇒support {d = d} {e} {x} bisim path =
    let t , init , related = initial-to bisim (positive-return tt)
        t′ , step , related′ = step-to bisim {i = inj₁ tt} {o = just (inj₂ x)} related
          (map-path (λ x → tt , inj₂ x) path)
        y , path′ , eq = map-unpath (λ y → t , inj₂ y) step
    in subst (Positive e) (inj₂-injective (cong proj₂ eq)) path′

pm-descent⇒literal-support : PMDescent → LiteralSupportCongruence 0ℓ
pm-descent⇒literal-support descend eq = emit-bisim⇒support
  (descend {⊤ ⇿ ⊥} {_ ⇿ ⊥} (emit-resp eq))

pmmay-descent⇒literal-support : PMmayDescent
  → {X : Set} {d e : Dₚ X} {x : X} → d ≈₊ e → Positive d x → Positive e x
pmmay-descent⇒literal-support descend eq = emit-bisim⇒support
  (descend {⊤ ⇿ ⊥} {_ ⇿ ⊥} (emit-positive-resp eq))

pm-descent⇒stable-equality : PMDescent → ¬ ¬ (x ≡ y) → x ≡ y
pm-descent⇒stable-equality descend =
  literal-support-congruence⇒stable-equality (pm-descent⇒literal-support descend)

pmmay-descent⇒stable-equality : PMmayDescent → ¬ ¬ (x ≡ y) → x ≡ y
pmmay-descent⇒stable-equality descend =
  pm-descent⇒stable-equality (pmmay-descent⇒pm-descent descend)

pm-descent⇒decidable-equality : Extensionality 0ℓ 0ℓ → PMDescent → DecidableEquality X
pm-descent⇒decidable-equality ext descend =
  literal-support⇒decidable-equality ext (pm-descent⇒literal-support descend)

pmmay-descent⇒decidable-equality : Extensionality 0ℓ 0ℓ → PMmayDescent → DecidableEquality X
pmmay-descent⇒decidable-equality ext descend =
  pm-descent⇒decidable-equality ext (pmmay-descent⇒pm-descent descend)

return-emit-equal : ¬ ¬ (x ≡ y)
  → Seal.procᵒ {⊤ ⇿ ⊥} {X ⇿ ⊥} (emit (returnₚ x)) P.≈
    Seal.procᵒ {⊤ ⇿ ⊥} {X ⇿ ⊥} (emit (returnₚ y))
return-emit-equal nn = emit-resp (return-double-negation nn)

return-emit-bisim⇒equal : canonical (emit (returnₚ x)) ≈ᴿ canonical (emit (returnₚ y)) → x ≡ y
return-emit-bisim⇒equal {x = x} bisim =
  sym (positive-return-reflect (emit-bisim⇒support bisim (positive-return x)))

support-mismatch : d ≈ₚ e → Positive d x → ¬ Positive e x
  → (Seal.procᵒ {⊤ ⇿ ⊥} {X ⇿ ⊥} (emit d) P.≈ Seal.procᵒ {⊤ ⇿ ⊥} {X ⇿ ⊥} (emit e))
    × ¬ (canonical (emit d) ≈ᴿ canonical (emit e))
support-mismatch eq path absent = emit-resp eq , λ bisim → absent (emit-bisim⇒support bisim path)
