{-# OPTIONS --safe --without-K #-}

module CategoricalCrypto.TaskPIOA.NativeSSP.Morphism where

open import Categories.Category.Monoidal
open import Categories.Category.Monoidal.Construction.Quotient
open import Categories.FreeMonoidal
open import Categories.Functor renaming (id to idF)
open import Categories.Functor.Monoidal
open import Categories.Functor.Monoidal.Properties
open import Categories.Functor.Presheaf.Morphism
open import Categories.NaturalTransformation using (ntHelper)
open import Categories.NaturalTransformation.NaturalIsomorphism using (niHelper)
open import Data.Product.Base
open import Data.Unit.Base using (⊤; tt)
import Data.Unit.Polymorphic as Unit
open import Relation.Binary.PropositionalEquality

open import CategoricalCrypto.Standard2.Morphism using (StdUCMorphism)
open import CategoricalCrypto.TaskPIOA.Core using (Signature; Automaton; Wiring; productSignature)
import CategoricalCrypto.TaskPIOA.Product as SP
import CategoricalCrypto.TaskPIOA.Setup as S
open import CategoricalCrypto.TaskPIOA.NativeSSP.Core
open import CategoricalCrypto.TaskPIOA.NativeSSP.Product
import CategoricalCrypto.TaskPIOA.NativeSSP.Setup as N
open import CategoricalCrypto.TaskPIOA.Simulation
open import CategoricalCrypto.TaskPIOA.Simulation.Properties
open import CategoricalCrypto.UCSetup.Morphism using (UCSetupMorphism)

open S.Syntax using (ObjTerm; unit; Var; _⊗₀_)

compileGenerator : ∀ {A B} → S.Generator A B → N.Syntax.HomTerm A B
compileGenerator (S.install M) = N.Syntax.var (N.install (compile M))
compileGenerator (S.connect w) = N.Syntax.var (N.wire w)

module Compile = FreeMonoidalHelper.Bind Mon Signature compileGenerator

compileContext : ∀ {A B} → S.Syntax.HomTerm A B → N.Syntax.HomTerm A B
compileContext = Compile.bind

sampleGenerator : ∀ {A B} → N.Generator A B → S.Syntax.HomTerm A B
sampleGenerator (N.install M) = S.Syntax.var (S.install (sampleMachine M))
sampleGenerator (N.wire w) = S.Syntax.var (S.connect w)

module Sample = FreeMonoidalHelper.Bind Mon Signature sampleGenerator

sampleContext : ∀ {A B} → N.Syntax.HomTerm A B → S.Syntax.HomTerm A B
sampleContext = Sample.bind

compiler : StrongMonoidalFunctor S.Wiringᴹ N.Wiringᴹ
compiler = record
  { F = record
    { F₀ = λ A → A ; F₁ = compileContext
    ; identity = λ {A} → N.related-refl A
    ; homomorphism = λ {X} {Y} {Z} {f} {g} x →
        N.related-refl Z (N.Interpretation.⟦ compileContext (g S.Syntax.∘ f) ⟧₁ x)
    ; F-resp-≈ = λ eq → MonoidalCongruence.≈⇒∼ N.quotient-laws (Compile.bind-resp-≈ eq) }
  ; isStrongMonoidal = record
    { ε = I.ε
    ; ⊗-homo = niHelper record
      { η = λ _ → N.Syntax.id ; η⁻¹ = λ _ → N.Syntax.id
      ; commute = λ {(A , B)} {(C , D)} (f , g) (x , y) →
          N.related-refl C (N.Interpretation.⟦ compileContext f ⟧₁ x) ,
          N.related-refl D (N.Interpretation.⟦ compileContext g ⟧₁ y)
      ; iso = λ (A , B) → record
        { isoˡ = λ (x , y) → N.related-refl A x , N.related-refl B y
        ; isoʳ = λ (x , y) → N.related-refl A x , N.related-refl B y } }
    ; associativity = I.associativity ; unitaryˡ = I.unitaryˡ ; unitaryʳ = I.unitaryʳ } }
  where
  module T = MonoidalCategory N.Wiringᴹ
  module I = IsStrongMonoidalFunctor (idF-IsStrongMonoidal N.Wiringᴹ)

Cross : (A : ObjTerm) → N.Values.⟦ A ⟧₀ → S.Values.⟦ A ⟧₀ → Set
Cross unit _ _ = ⊤
Cross (Var S) M N = Simulation (sampleMachine M) N × Simulation N (sampleMachine M)
Cross (A ⊗₀ B) (a , b) (c , d) = Cross A a c × Cross B b d

sampleValues : ∀ A → N.Values.⟦ A ⟧₀ → S.Values.⟦ A ⟧₀
sampleValues unit _ = Unit.tt
sampleValues (Var S) M = sampleMachine M
sampleValues (A ⊗₀ B) (a , b) = sampleValues A a , sampleValues B b

sample-values-related : ∀ A x → Cross A x (sampleValues A x)
sample-values-related unit x = tt
sample-values-related (Var S) M = identity-simulation (sampleMachine M) , identity-simulation (sampleMachine M)
sample-values-related (A ⊗₀ B) (a , b) = sample-values-related A a , sample-values-related B b

cross-connect : ∀ {A B J} (w : Wiring A B J) {M M′ N N′}
  → Cross (Var A) M M′ → Cross (Var B) N N′
  → Cross (Var (productSignature A B J)) (connect w M N) (SP.product w M′ N′)
cross-connect w {M} {M′} {N} {N′} (p , p′) (q , q′) =
  compose-simulation (product-simulation w p q) (connect-sample w M N) ,
  compose-simulation (sample-connect w M N) (product-simulation w p′ q′)

compile-correct : ∀ {A B} (f : S.Syntax.HomTerm A B) {x y}
  → Cross A x y → Cross B (N.Interpretation.⟦ compileContext f ⟧₁ x) (S.Interpretation.⟦ f ⟧₁ y)
compile-correct (S.Syntax.var (S.install M)) r = compile-simulation M , sample-compile-simulation M
compile-correct (S.Syntax.var (S.connect w)) (p , q) = cross-connect w p q
compile-correct S.Syntax.id r = r
compile-correct (f S.Syntax.∘ g) r = compile-correct f (compile-correct g r)
compile-correct (f S.Syntax.⊗₁ g) (p , q) = compile-correct f p , compile-correct g q
compile-correct S.Syntax.λ⇒ (p , q) = q
compile-correct S.Syntax.λ⇐ p = tt , p
compile-correct S.Syntax.ρ⇒ (p , q) = p
compile-correct S.Syntax.ρ⇐ p = p , tt
compile-correct S.Syntax.α⇒ ((p , q) , r) = p , q , r
compile-correct S.Syntax.α⇐ (p , q , r) = (p , q) , r
compile-correct (S.Syntax.σ ⦃ () ⦄)

sample-correct : ∀ {A B} (f : N.Syntax.HomTerm A B) {x y}
  → Cross A x y → Cross B (N.Interpretation.⟦ f ⟧₁ x) (S.Interpretation.⟦ sampleContext f ⟧₁ y)
sample-correct (N.Syntax.var (N.install {S} M)) r = sample-values-related (Var S) M
sample-correct (N.Syntax.var (N.wire w)) (p , q) = cross-connect w p q
sample-correct N.Syntax.id r = r
sample-correct (f N.Syntax.∘ g) r = sample-correct f (sample-correct g r)
sample-correct (f N.Syntax.⊗₁ g) (p , q) = sample-correct f p , sample-correct g q
sample-correct N.Syntax.λ⇒ (p , q) = q
sample-correct N.Syntax.λ⇐ p = tt , p
sample-correct N.Syntax.ρ⇒ (p , q) = p
sample-correct N.Syntax.ρ⇐ p = p , tt
sample-correct N.Syntax.α⇒ ((p , q) , r) = p , q , r
sample-correct N.Syntax.α⇐ (p , q , r) = (p , q) , r
sample-correct (N.Syntax.σ ⦃ () ⦄)

compileTest : ∀ {A} → S.Test A → N.Test A
compileTest t = N.test (S.target t) (S.closed t) (compileContext (S.context t)) (S.schedule t) (S.reward t)

sampleTest : ∀ {A} → N.Test A → S.Test A
sampleTest t = S.test (N.target t) (N.closed t) (sampleContext (N.context t)) (N.schedule t) (N.reward t)

compile-evaluate : ∀ {A} (t : S.Test A) x
  → N.evaluate (compileTest t) x ≡ S.evaluate t (sampleValues A x)
compile-evaluate {A} t x = trans (N.evaluate-trace (compileTest t) x)
  (trans (trace-sample (N.Interpretation.⟦ compileContext (S.context t) ⟧₁ x) (S.schedule t) (S.reward t))
    (trace-match (proj₁ (compile-correct (S.context t) (sample-values-related A x))) (S.schedule t) (S.reward t)))

sample-evaluate : ∀ {A} (t : N.Test A) x
  → N.evaluate t x ≡ S.evaluate (sampleTest t) (sampleValues A x)
sample-evaluate {A} t x = trans (N.evaluate-trace t x)
  (trans (trace-sample (N.Interpretation.⟦ N.context t ⟧₁ x) (N.schedule t) (N.reward t))
    (trace-match (proj₁ (sample-correct (N.context t) (sample-values-related A x))) (N.schedule t) (N.reward t)))

ν : PresheafMorphism (StrongMonoidalFunctor.F compiler) S.ℰ-native N.ℰ-native
ν = record { ν = ntHelper record
  { η = λ A → record
    { to = compileTest
    ; cong = λ {t} {u} eq x → trans (compile-evaluate t x)
        (trans (eq (sampleValues A x)) (sym (compile-evaluate u x))) }
  ; commute = λ f {t} x → refl } }

ν-epi : PresheafMorphism.Epi ν
ν-epi t = sampleTest t , λ x → trans (compile-evaluate (sampleTest t) x) (sym (sample-evaluate t x))

bridge : UCSetupMorphism S.UC.StdSetup N.UC.StdSetup
bridge = StdUCMorphism S.Wiringᴹ N.Wiringᴹ S.ℰ-native N.ℰ-native compiler ν

native-roundtrip : ∀ {S} (M : Machine S)
  → N.Syntax.var (N.install (compile (sampleMachine M))) N.∼ N.Syntax.var (N.install M)
native-roundtrip M _ = compile-simulation (sampleMachine M) , sample-compile-simulation (sampleMachine M)

compile-connect : ∀ {A B J} (w : Wiring A B J) (M : Automaton A) (N : Automaton B)
  → N.Related (Var (productSignature A B J)) (compile (SP.product w M N)) (connect w (compile M) (compile N))
compile-connect w M N =
  compose-simulation (proj₂ cross) (compile-simulation (SP.product w M N)) ,
  compose-simulation (sample-compile-simulation (SP.product w M N)) (proj₁ cross)
  where cross = cross-connect w (compile-simulation M , sample-compile-simulation M)
          (compile-simulation N , sample-compile-simulation N)

install-connect-square : ∀ {A B J} (w : Wiring A B J) (M : Automaton A) (L : Automaton B)
  → N.Syntax.var (N.install (compile (SP.product w M L)))
    N.∼ (N.Syntax.var (N.wire w) N.Syntax.∘
      (N.Syntax.var (N.install (compile M)) N.Syntax.⊗₁ N.Syntax.var (N.install (compile L)))
      N.Syntax.∘ N.Syntax.λ⇐)
install-connect-square w M L _ = compile-connect w M L

compileEnvironment : ∀ {S} → SP.Environment S → Environment S
compileEnvironment E = record
  { signature = SP.signature E ; machine = compile (SP.automaton E) ; wiring = SP.wiring E }

native-test-square : ∀ {S} (E : SP.Environment S) ρ P
  → compileTest (S.nativeTest E ρ P) ≡ N.nativeTest (compileEnvironment E) ρ P
native-test-square E ρ P = refl
