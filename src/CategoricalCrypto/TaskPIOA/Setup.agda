{-# OPTIONS --safe --without-K #-}

-- Automata are resources. Arrows are typed installation/wiring contexts;
-- their tensor keeps independent resource slots, not an erased schedule.
module CategoricalCrypto.TaskPIOA.Setup where

open import Categories.Category.Instance.Sets
open import Categories.Category.Instance.Setoids
open import Categories.Category.Monoidal
open import Categories.Category.Monoidal.Instance.Sets
open import Categories.FreeMonoidal
open import Categories.Functor.Presheaf
open import Data.List.Base using (List)
open import Data.Product.Base
open import Data.Rational.Base using (ℚ)
open import Data.Unit.Polymorphic using (tt)
open import Level
open import Relation.Binary.Bundles using (Setoid)
open import Relation.Binary.PropositionalEquality

open import CategoricalCrypto.TaskPIOA.Core
open import CategoricalCrypto.TaskPIOA.Product
import CategoricalCrypto.Standard2 as Standard
open import ProbabilisticLogic.Distribution.RationalDist

open FreeMonoidalHelper Mon Signature using (ObjTerm; unit; Var; _⊗₀_)

data Generator : ObjTerm → ObjTerm → Set where
  install : ∀ {S} → Automaton S → Generator unit (Var S)
  connect : ∀ {A B J} → Wiring A B J
    → Generator (Var A ⊗₀ Var B) (Var (productSignature A B J))

wiringData : FreeMonoidalData
wiringData = record { v = Mon ; X = Signature ; mor = Generator }

module Syntax = FreeMonoidal wiringData

sets : ⟦ Mon ⟧ᵥ
sets = record { C = Sets 0ℓ ; Monoidal-C = Product.Sets-Monoidal ; Symmetric-C = noSymmetric }

module Values = FreeObjInterp Mon Signature sets Automaton

interpretGenerator : ∀ {A B} → Generator A B → Values.⟦ A ⟧₀ → Values.⟦ B ⟧₀
interpretGenerator (install M) _ = M
interpretGenerator (connect w) (M , N) = product w M N

interpretation : FreeFunctorData wiringData
interpretation = record { ⟦v⟧ = sets ; ⟦_⟧ᵖ₀ = Automaton ; ⟦_⟧ᵖ₁ = interpretGenerator }

module Interpretation = FreeFunctor interpretation
open Interpretation using (⟦_⟧₁; ⟦⟧-resp-≈)

Wiringᴹ : MonoidalCategory 0ℓ 0ℓ 0ℓ
Wiringᴹ = Interpretation.FreeMonoidalM

record Test (A : ObjTerm) : Set where
  constructor test
  field target : Signature
        closed : inputs target ≡ empty
        context : Syntax.HomTerm A (Var target)
        schedule : Schedule target
        reward : List (Output target) → ℚ
open Test public

evaluate : ∀ {A} → Test A → Values.⟦ A ⟧₀ → ℚ
evaluate t x = lookupᴰℚ (entries (traceDist (⟦ context t ⟧₁ x) (schedule t))) (reward t)

_≋_ : ∀ {A} → Test A → Test A → Set
t ≋ u = ∀ x → evaluate t x ≡ evaluate u x

Tests : ObjTerm → Setoid 0ℓ 0ℓ
Tests A = record
  { Carrier = Test A
  ; _≈_ = _≋_
  ; isEquivalence = record
    { refl = λ _ → refl ; sym = λ p x → sym (p x) ; trans = λ p q x → trans (p x) (q x) }
  }

pull : ∀ {A B} → Syntax.HomTerm A B → Test B → Test A
pull f t = test (target t) (closed t) (context t Syntax.∘ f) (schedule t) (reward t)

plugging : ∀ {A B} (f : Syntax.HomTerm A B) t x
  → evaluate (pull f t) x ≡ evaluate t (⟦ f ⟧₁ x)
plugging f t x = refl

ℰ-native : Presheaf Syntax.FreeMonoidal (Setoids 0ℓ 0ℓ)
ℰ-native = record
  { F₀ = Tests
  ; F₁ = λ f → record { to = pull f ; cong = λ p x → p (⟦ f ⟧₁ x) }
  ; identity = λ _ → refl
  ; homomorphism = λ _ → refl
  ; F-resp-≈ = λ eq {t} x → cong (evaluate t) (⟦⟧-resp-≈ eq x)
  }

module UC = Standard.StdUC Wiringᴹ ℰ-native

resource : ∀ {S} → Automaton S → Syntax.HomTerm unit (unit ⊗₀ Var S)
resource M = Syntax.λ⇐ Syntax.∘ Syntax.var (install M)

nativeTest : ∀ {S} (E : Environment S)
  → Schedule (productSignature S (signature E) empty)
  → (List (Output (productSignature S (signature E) empty)) → ℚ)
  → Test (Var S)
nativeTest {S} E ρ P = test (productSignature S (signature E) empty) refl
  (Syntax.var (connect (wiring E)) Syntax.∘
    (Syntax.id Syntax.⊗₁ Syntax.var (install (automaton E))) Syntax.∘ Syntax.ρ⇐) ρ P

native-correspondence : ∀ {S} (M : Automaton S) E ρ P
  → evaluate (nativeTest E ρ P) M ≡ lookupᴰℚ (entries (observe M E ρ)) P
native-correspondence M E ρ P = refl
