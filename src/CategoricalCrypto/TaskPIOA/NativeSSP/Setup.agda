{-# OPTIONS --safe --without-K #-}

-- Equality checks both input delivery and local kernels, before any test is
-- selected. The quotient therefore remains congruent under open wiring.
module CategoricalCrypto.TaskPIOA.NativeSSP.Setup where

open import Categories.Category.Instance.Sets
open import Categories.Category.Instance.Setoids
open import Categories.Category.Monoidal
open import Categories.Category.Monoidal.Construction.Quotient
open import Categories.Category.Monoidal.Instance.Sets
open import Categories.FreeMonoidal
open import Categories.Functor.Presheaf
open import Data.List.Base using (List)
open import Data.Product.Base
open import Data.Rational.Base using (ℚ)
open import Data.Unit.Base using (⊤; tt)
open import Level
open import Relation.Binary.Bundles using (Setoid)
open import Relation.Binary.PropositionalEquality

open import CategoricalCrypto.SSP.Observation using (evalC)
import CategoricalCrypto.Standard2 as Standard
open import CategoricalCrypto.TaskPIOA.Core using
  (Signature; Wiring; inputs; empty; productSignature; Schedule; Output)
open import CategoricalCrypto.TaskPIOA.NativeSSP.Core
open import CategoricalCrypto.TaskPIOA.NativeSSP.Product
open import CategoricalCrypto.TaskPIOA.Simulation
open import CategoricalCrypto.TaskPIOA.Simulation.Properties
open import ProbabilisticLogic.Distribution.RationalDist hiding (_∼_)
open import ProbabilisticLogic.Distribution.RationalDist.Expectation using (maybeℚ)

open FreeMonoidalHelper Mon Signature using (ObjTerm; unit; Var; _⊗₀_)

data Generator : ObjTerm → ObjTerm → Set where
  install : ∀ {S} → Machine S → Generator unit (Var S)
  wire : ∀ {A B J} → Wiring A B J
    → Generator (Var A ⊗₀ Var B) (Var (productSignature A B J))

wiringData : FreeMonoidalData
wiringData = record { v = Mon ; X = Signature ; mor = Generator }

module Syntax = FreeMonoidal wiringData

sets : ⟦ Mon ⟧ᵥ
sets = record { C = Sets 0ℓ ; Monoidal-C = Product.Sets-Monoidal ; Symmetric-C = noSymmetric }

module Values = FreeObjInterp Mon Signature sets Machine

interpretGenerator : ∀ {A B} → Generator A B → Values.⟦ A ⟧₀ → Values.⟦ B ⟧₀
interpretGenerator (install M) _ = M
interpretGenerator (wire w) (M , N) = connect w M N

interpretation : FreeFunctorData wiringData
interpretation = record { ⟦v⟧ = sets ; ⟦_⟧ᵖ₀ = Machine ; ⟦_⟧ᵖ₁ = interpretGenerator }

module Interpretation = FreeFunctor interpretation
open Interpretation using (⟦_⟧₁; ⟦⟧-resp-≈)

Related : (A : ObjTerm) → Values.⟦ A ⟧₀ → Values.⟦ A ⟧₀ → Set
Related unit _ _ = ⊤
Related (Var S) M N = Simulation (sampleMachine M) (sampleMachine N)
  × Simulation (sampleMachine N) (sampleMachine M)
Related (A ⊗₀ B) (a , b) (c , d) = Related A a c × Related B b d

related-refl : ∀ A x → Related A x x
related-refl unit x = tt
related-refl (Var S) M = identity-simulation (sampleMachine M) , identity-simulation (sampleMachine M)
related-refl (A ⊗₀ B) (a , b) = related-refl A a , related-refl B b

related-sym : ∀ A {x y} → Related A x y → Related A y x
related-sym unit r = tt
related-sym (Var S) (p , q) = q , p
related-sym (A ⊗₀ B) (p , q) = related-sym A p , related-sym B q

related-trans : ∀ A {x y z} → Related A x y → Related A y z → Related A x z
related-trans unit p q = tt
related-trans (Var S) (p , p′) (q , q′) = compose-simulation q p , compose-simulation p′ q′
related-trans (A ⊗₀ B) (p , p′) (q , q′) = related-trans A p q , related-trans B p′ q′

connect-related : ∀ {A B J} (w : Wiring A B J) {M M′ N N′}
  → Related (Var A) M M′ → Related (Var B) N N′
  → Related (Var (productSignature A B J)) (connect w M N) (connect w M′ N′)
connect-related w {M} {M′} {N} {N′} (p , p′) (q , q′) =
  compose-simulation (sample-connect w M′ N′)
    (compose-simulation (product-simulation w p q) (connect-sample w M N)) ,
  compose-simulation (sample-connect w M N)
    (compose-simulation (product-simulation w p′ q′) (connect-sample w M′ N′))

wiring-preserves : ∀ {A B} (f : Syntax.HomTerm A B) {x y}
  → Related A x y → Related B (⟦ f ⟧₁ x) (⟦ f ⟧₁ y)
wiring-preserves (Syntax.var (install {S} M)) r = related-refl (Var S) M
wiring-preserves (Syntax.var (wire w)) (p , q) = connect-related w p q
wiring-preserves Syntax.id r = r
wiring-preserves (f Syntax.∘ g) r = wiring-preserves f (wiring-preserves g r)
wiring-preserves (f Syntax.⊗₁ g) (p , q) = wiring-preserves f p , wiring-preserves g q
wiring-preserves Syntax.λ⇒ (p , q) = q
wiring-preserves Syntax.λ⇐ p = tt , p
wiring-preserves Syntax.ρ⇒ (p , q) = p
wiring-preserves Syntax.ρ⇐ p = p , tt
wiring-preserves Syntax.α⇒ ((p , q) , r) = p , q , r
wiring-preserves Syntax.α⇐ (p , q , r) = (p , q) , r
wiring-preserves (Syntax.σ ⦃ () ⦄)

_∼_ : ∀ {A B} → Syntax.HomTerm A B → Syntax.HomTerm A B → Set
_∼_ {B = B} f g = ∀ x → Related B (⟦ f ⟧₁ x) (⟦ g ⟧₁ x)

quotient-laws : MonoidalCongruence Interpretation.FreeMonoidalM 0ℓ
quotient-laws = record
  { _∼_ = _∼_
  ; ∼-equiv = record
    { refl = λ {f} x → related-refl _ (⟦ f ⟧₁ x)
    ; sym = λ p x → related-sym _ (p x)
    ; trans = λ p q x → related-trans _ (p x) (q x) }
  ; ≈⇒∼ = λ {B = B} {f} eq x → subst (Related B (⟦ f ⟧₁ x)) (⟦⟧-resp-≈ eq x)
      (related-refl B (⟦ f ⟧₁ x))
  ; ∘-resp-∼ = λ {f = f} {i = i} p q x → related-trans _ (wiring-preserves f (q x)) (p (⟦ i ⟧₁ x))
  ; ⊗-resp-∼ = λ p q (x , y) → p x , q y }

Wiringᴹ : MonoidalCategory 0ℓ 0ℓ 0ℓ
Wiringᴹ = quotient Interpretation.FreeMonoidalM quotient-laws

record Test (A : ObjTerm) : Set where
  constructor test
  field target : Signature
        closed : inputs target ≡ empty
        context : Syntax.HomTerm A (Var target)
        schedule : Schedule target
        reward : List (Output target) → ℚ
open Test public

evaluate : ∀ {A} → Test A → Values.⟦ A ⟧₀ → ℚ
evaluate t x = lookupᴰℚ (entries (evalC (execution (⟦ context t ⟧₁ x) (schedule t)))) (maybeℚ (reward t))

evaluate-trace : ∀ {A} (t : Test A) x
  → evaluate t x ≡ lookupᴰℚ (entries (trace (⟦ context t ⟧₁ x) (schedule t))) (reward t)
evaluate-trace t x = trans (execution-trace (⟦ context t ⟧₁ x) (schedule t) (maybeℚ (reward t)))
  (lookupᴰℚ-Dmap _ (trace (⟦ context t ⟧₁ x) (schedule t)) (maybeℚ (reward t)))

_≋_ : ∀ {A} → Test A → Test A → Set
t ≋ u = ∀ x → evaluate t x ≡ evaluate u x

test-preserves : ∀ {A} (t : Test A) {x y} → Related A x y → evaluate t x ≡ evaluate t y
test-preserves t {x} {y} r = trans (evaluate-trace t x)
  (trans (trace-sample (⟦ context t ⟧₁ x) (schedule t) (reward t))
    (trans (trace-match (proj₁ (wiring-preserves (context t) r)) (schedule t) (reward t))
      (trans (sym (trace-sample (⟦ context t ⟧₁ y) (schedule t) (reward t)))
        (sym (evaluate-trace t y)))))

Tests : ObjTerm → Setoid 0ℓ 0ℓ
Tests A = record
  { Carrier = Test A ; _≈_ = _≋_
  ; isEquivalence = record
    { refl = λ _ → refl ; sym = λ p x → sym (p x) ; trans = λ p q x → trans (p x) (q x) } }

pull : ∀ {A B} → Syntax.HomTerm A B → Test B → Test A
pull f t = test (target t) (closed t) (context t Syntax.∘ f) (schedule t) (reward t)

ℰ-native : Presheaf (MonoidalCategory.U Wiringᴹ) (Setoids 0ℓ 0ℓ)
ℰ-native = record
  { F₀ = Tests
  ; F₁ = λ f → record { to = pull f ; cong = λ p x → p (⟦ f ⟧₁ x) }
  ; identity = λ _ → refl ; homomorphism = λ _ → refl
  ; F-resp-≈ = λ eq {t} x → test-preserves t (eq x) }

module UC = Standard.StdUC Wiringᴹ ℰ-native

resource : ∀ {S} → Machine S → Syntax.HomTerm unit (unit ⊗₀ Var S)
resource M = Syntax.λ⇐ Syntax.∘ Syntax.var (install M)

nativeTest : ∀ {S} (E : Environment S)
  → Schedule (productSignature S (signature E) empty)
  → (List (Output (productSignature S (signature E) empty)) → ℚ)
  → Test (Var S)
nativeTest {S} E ρ P = test (productSignature S (signature E) empty) refl
  (Syntax.var (wire (wiring E)) Syntax.∘
    (Syntax.id Syntax.⊗₁ Syntax.var (install (machine E))) Syntax.∘ Syntax.ρ⇐) ρ P

native-correspondence : ∀ {S} (M : Machine S) E ρ P
  → evaluate (nativeTest E ρ P) M
    ≡ lookupᴰℚ (entries (trace (connect (wiring E) M (machine E)) ρ)) P
native-correspondence M E ρ P = evaluate-trace (nativeTest E ρ P) M
