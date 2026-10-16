{-# OPTIONS --safe #-}

module CategoricalCrypto.Machine.Relational.Tests where

open import Categories.Category
open import Categories.Functor.Monoidal using (StrongMonoidalFunctor)
open import Data.Bool.Base
open import Data.Empty
open import Data.Maybe.Base
open import Data.Product.Base
open import Data.Unit.Base
open import Function.Bundles
open import Relation.Binary.PropositionalEquality hiding (J)
open import Relation.Nullary.Negation

open import CategoricalCrypto.Channel.Core
import CategoricalCrypto.Machine.Core as M
import CategoricalCrypto.Machine.Iso as Old
open import CategoricalCrypto.Machine.Relational
import CategoricalCrypto.Machine.Relational.Category as Cat
open import CategoricalCrypto.Machine.Relational.Iso
open import CategoricalCrypto.Machine.Relational.Isomorphism
open import CategoricalCrypto.Machine.Relational.Model
open import CategoricalCrypto.Machine.Relational.Observation
import CategoricalCrypto.Machine.Relational.Setup as Setup
import CategoricalCrypto.Machine.Relational.Simulation as Sim
import CategoricalCrypto.Machine.Relational.Wiring as W

private
  module G = Category 𝔾ᴿ
  module F = StrongMonoidalFunctor Iso→native
  variable A : Channel

-- The Boolean successor is unconstrained, so the erasure is genuinely
-- noninjective, rather than a hidden bijection on the reachable states.
ghost-machine : M.Machine A A
ghost-machine = M.MkMachine {State = Bool} λ _ i o _ → M.Machine.stepRel M.id tt i o tt

ghost : Initialized A A
ghost = F.F₁ ghost-machine

ghost-erasure : ghost {A} G.≈ G.id
ghost-erasure = record
  { Related = λ _ _ → ⊤
  ; initial-to = λ _ → tt , refl , tt
  ; initial-from = λ _ → true , tt , tt
  ; step-to = λ _ p → tt , p , tt
  ; step-from = λ _ p → true , p , tt
  }

ghost-not-iso : ¬ (ghost-machine {A} Old.≅ᴹ M.id)
ghost-not-iso φ = impossible
  (trans (sym (Old._≅ᴹ_.from∘to φ true)) (Old._≅ᴹ_.from∘to φ false))
  where
  impossible : true ≡ false → ⊥
  impossible ()

ghost-tests : (t : Initialized A Ω) → Setup.E.Obs._≋_ (t W.∘ ghost) t
ghost-tests t = Setup.E.Obs.≈⇒≋
  (≈ᴿ-trans (W.∘-cong ≈ᴿ-refl ghost-erasure) Cat.identityʳ)

ghost-all-preparations : (t : Initialized A Ω) (p : Initialized J A) (b : Bool)
  → eval ((t W.∘ ghost) W.∘ p) b ⇔ eval (t W.∘ p) b
ghost-all-preparations t p = ghost-tests t p

-- The real StdUC consumer supplies the adversary itself as simulator. Its
-- U-kernel conclusion includes arbitrary native prefix contexts and tests.
ghost-UC : Setup._≤UC_ {A = I ⊗₀ Ω} {X = I} {B = Ω} {Y = I} ghost W.id
ghost-UC a = a , Setup.≈C⇒≈ᵁ (W.∘-cong ≈ᴿ-refl ghost-erasure)

reply : Bool → Initialized J Ω
reply b = all-states (M.MkMachine {State = ⊤} λ _ _ o _ → o ≡ just (verdict b))

refuse diverge : Initialized J Ω
refuse = all-states (M.MkMachine {State = ⊤} λ _ _ o _ → o ≡ nothing)
diverge = all-states (M.MkMachine {State = ⊤} λ _ _ _ _ → ⊥)

reply-succeeds : (b : Bool) → eval (reply b) b
reply-succeeds b = tt , tt , tt , refl

refusal-no-success : (b : Bool) → ¬ eval refuse b
refusal-no-success b (_ , _ , _ , ())

divergence-no-success : (b : Bool) → ¬ eval diverge b
divergence-no-success b (_ , _ , _ , ())

opaque
  unfolding _⊗₀_ verdict

  true-not-false : ¬ eval (reply false) true
  true-not-false (_ , _ , _ , ())

  false-not-true : ¬ eval (reply true) false
  false-not-true (_ , _ , _ , ())

-- Separation is at the public Observable test setoid, not just the readout:
-- its universal quantifier includes the native identity preparation at J.
test-separation : {P Q : Initialized J Ω} {b : Bool}
  → eval P b → ¬ eval Q b → ¬ Setup.E.Obs._≋_ P Q
test-separation {b = b} yes no eq = no
  (eval-to Cat.identityʳ (Equivalence.to (eq W.id b)
    (eval-to (≈ᴿ-sym Cat.identityʳ) yes)))

true≠false : ¬ Setup.E.Obs._≋_ (reply true) (reply false)
true≠false = test-separation (reply-succeeds true) true-not-false

false≠refusal : ¬ Setup.E.Obs._≋_ (reply false) refuse
false≠refusal = test-separation (reply-succeeds false) (refusal-no-success false)

false≠divergence : ¬ Setup.E.Obs._≋_ (reply false) diverge
false≠divergence = test-separation (reply-succeeds false) (divergence-no-success false)

true≠refusal : ¬ Setup.E.Obs._≋_ (reply true) refuse
true≠refusal = test-separation (reply-succeeds true) (refusal-no-success true)

true≠divergence : ¬ Setup.E.Obs._≋_ (reply true) diverge
true≠divergence = test-separation (reply-succeeds true) (divergence-no-success true)

divergence-below-reply : (b : Bool) → diverge Sim.≲ᴿ reply b
divergence-below-reply b = record
  { Related = λ _ _ → ⊤
  ; initial-to = λ _ → tt , tt , tt
  ; step-to = λ _ ()
  }

reply-not-below-divergence : (b : Bool) → ¬ (reply b Sim.≲ᴿ diverge)
reply-not-below-divergence b φ = divergence-no-success b (Sim.forward φ (reply-succeeds b))

forward-all-tests : {p q : Initialized J A} → p Sim.≲ᴿ q → (t : Initialized A Ω)
  → ∀ {b} → eval (t W.∘ p) b → eval (t W.∘ q) b
forward-all-tests φ t = Sim.observe Sim.reflexive φ
