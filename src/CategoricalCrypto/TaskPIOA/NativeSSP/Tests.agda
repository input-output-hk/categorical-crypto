{-# OPTIONS --safe --without-K #-}

module CategoricalCrypto.TaskPIOA.NativeSSP.Tests where

open import Categories.Functor.Presheaf.Morphism
open import Data.Bool.Base
open import Data.List.Base using (List; []; _∷_)
open import Data.Maybe.Base using (just; nothing)
open import Data.Product.Base
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; ½; _/_)
open import Data.Integer.Base using (+_)
open import Data.Sum.Base using (inj₁; inj₂; _⊎_)
open import Data.Unit.Base
import Data.Unit.Polymorphic as Unit
open import Relation.Binary.PropositionalEquality

open import CategoricalCrypto.SSP.Dist.Kernel using (done; toss; sample)
open import CategoricalCrypto.SSP.Observation using (evalC)
import CategoricalCrypto.SSP.Protocol as P
open import CategoricalCrypto.TaskPIOA.Core using
  (Signature; Wiring; Ports; bit; empty; one; productSignature; Output)
import CategoricalCrypto.TaskPIOA.Setup as S
import CategoricalCrypto.TaskPIOA.Security as SourceSecurity
import CategoricalCrypto.TaskPIOA.Tests as Examples
import CategoricalCrypto.TaskPIOA.SSPAdapterTests as Rational
open import CategoricalCrypto.TaskPIOA.NativeSSP.Core
open import CategoricalCrypto.TaskPIOA.NativeSSP.Product
import CategoricalCrypto.TaskPIOA.NativeSSP.Setup as N
open import CategoricalCrypto.TaskPIOA.NativeSSP.Morphism
open import CategoricalCrypto.TaskPIOA.NativeSSP.Security
open import ProbabilisticLogic.Distribution.RationalDist
open import ProbabilisticLogic.Distribution.RationalDist.Expectation using (maybeℚ)

network : Machine (productSignature (Examples.coinSignature empty) Examples.receiverSignature empty)
network = connect Examples.wire (compile Examples.pulse) (compile Examples.receiver)

receiver-test : N.Test (N.Syntax.Var (productSignature (Examples.coinSignature empty) Examples.receiverSignature empty))
receiver-test = N.test _ refl N.Syntax.id Examples.send-first Examples.receiver-accepts

sender-delivers : N.evaluate receiver-test network ≡ 1ℚ
sender-delivers = refl

read-before-delivery : N.evaluate (N.test _ refl N.Syntax.id Examples.read-first Examples.receiver-accepts) network ≡ 0ℚ
read-before-delivery = refl

boundaryPorts : Ports bit (bit CategoricalCrypto.TaskPIOA.Core.⊕ bit)
boundaryPorts = record
  { name = inj₁ ; find = λ where (inj₁ b) → just b ; (inj₂ _) → nothing
  ; complete = λ _ → refl
  ; sound = λ where (inj₁ b) .b refl → refl ; (inj₂ _) _ () }

broadcast : Wiring Examples.receiverSignature Examples.receiverSignature bit
broadcast = record
  { left = boundaryPorts ; right = boundaryPorts
  ; boundary-live = λ i → inj₁ (i , refl) }

broadcast-machine : Machine (productSignature Examples.receiverSignature Examples.receiverSignature bit)
broadcast-machine = connect broadcast (compile Examples.receiver) (compile Examples.receiver)

both-receive-public-input : lookupᴰℚ (entries
  (evalC (P.step (protocol broadcast-machine) (false , false) (inj₁ true) tt)))
  (maybeℚ (λ where ((true , true) , nothing) → 1ℚ ; _ → 0ℚ)) ≡ 1ℚ
both-receive-public-input = refl

disabled-successfully-stutters : lookupᴰℚ (entries
  (evalC (P.step (protocol (compile Examples.pulse)) false (inj₂ true) tt)))
  (maybeℚ (λ where (false , nothing) → 1ℚ ; _ → 0ℚ)) ≡ 1ℚ
disabled-successfully-stutters = refl

noncanonical : Machine (Examples.coinSignature empty)
noncanonical = record
  { memory = bit ; start = false ; deliver = λ ()
  ; select = λ where q false → just (inj₂ tt) ; q true → just (inj₁ q)
  ; owned = λ where q false a refl → refl ; q true a refl → refl
  ; transition = λ where (inj₂ _) _ → toss Rational.biased done ; (inj₁ _) q → done q }

correlation-reward : List Bool → ℚ
correlation-reward (false ∷ false ∷ []) = 1ℚ
correlation-reward (true ∷ true ∷ []) = 1ℚ
correlation-reward _ = 0ℚ

first-reward : List Bool → ℚ
first-reward (true ∷ _) = 1ℚ
first-reward _ = 0ℚ

persistent-joint-correlation : lookupᴰℚ (entries (trace noncanonical Rational.repeat-word)) correlation-reward ≡ 1ℚ
persistent-joint-correlation = refl

non-dyadic-native-execution : lookupᴰℚ (entries (evalC (execution noncanonical Rational.repeat-word)))
  (maybeℚ first-reward) ≡ + 2 / 3
non-dyadic-native-execution = refl

arbitrary-native-test : N.Test N.Syntax.unit
arbitrary-native-test = N.test (Examples.coinSignature empty) refl
  (N.Syntax.var (N.install noncanonical)) Rational.repeat-word first-reward

noncanonical-context-coverage : compileTest (sampleTest arbitrary-native-test) N.≋ arbitrary-native-test
noncanonical-context-coverage = proj₂ (ν-epi arbitrary-native-test)

noncanonical-context-reward : N.evaluate arbitrary-native-test Unit.tt ≡ + 2 / 3
noncanonical-context-reward = refl

leak-wire : Wiring (Examples.coinSignature empty) (Examples.coinSignature empty) empty
leak-wire = record
  { left = record { name = λ () ; find = λ _ → nothing ; complete = λ () ; sound = λ _ _ () }
  ; right = record { name = λ () ; find = λ _ → nothing ; complete = λ () ; sound = λ _ _ () }
  ; boundary-live = λ () }

simulator : S.Syntax.HomTerm S.Syntax.unit (S.Syntax.Var (Examples.coinSignature empty))
simulator = S.Syntax.var (S.install Examples.pulse)

ideal-resource : S.Syntax.HomTerm S.Syntax.unit (S.Syntax.unit S.Syntax.⊗₀ S.Syntax.Var (Examples.coinSignature empty))
ideal-resource = S.resource Examples.pulse

real-resource : S.Syntax.HomTerm S.Syntax.unit
  (S.Syntax.Var (Examples.coinSignature empty) S.Syntax.⊗₀ S.Syntax.Var (Examples.coinSignature empty))
real-resource = S.UC.sub simulator S.Syntax.∘ ideal-resource

source-nonidentity-simulation : real-resource S.UC.≤UC ideal-resource
source-nonidentity-simulation = S.UC.dummy-complete (simulator , S.UC.≈ᵁ-refl)

native-nonidentity-simulation : Transport.G real-resource N.UC.≤UC Transport.G ideal-resource
native-nonidentity-simulation = preserves-≤UC source-nonidentity-simulation

native-simulator-action : Transport.G real-resource
  N.∼ (N.UC.sub (compileContext simulator) N.Syntax.∘ Transport.G ideal-resource)
native-simulator-action = simulator-square simulator ideal-resource

leak-consumer : N.Test
  (N.Syntax.Var (Examples.coinSignature empty) N.Syntax.⊗₀ N.Syntax.Var (Examples.coinSignature empty))
leak-consumer = N.test _ refl (N.Syntax.var (N.wire leak-wire))
  (inj₁ false ∷ inj₁ true ∷ []) Examples.nonempty

installed-simulator-is-observed : N.evaluate
  (N.pull (Transport.G real-resource) leak-consumer) Unit.tt ≡ 1ℚ
installed-simulator-is-observed = refl

source-target-simulator-consumer : N.evaluate
  (compileTest (S.pull real-resource
    (S.test _ refl (S.Syntax.var (S.connect leak-wire))
      (inj₁ false ∷ inj₁ true ∷ []) Examples.nonempty))) Unit.tt
  ≡ S.evaluate (S.pull real-resource
    (S.test _ refl (S.Syntax.var (S.connect leak-wire))
      (inj₁ false ∷ inj₁ true ∷ []) Examples.nonempty)) Unit.tt
source-target-simulator-consumer = compile-evaluate
  (S.pull real-resource (S.test _ refl (S.Syntax.var (S.connect leak-wire))
    (inj₁ false ∷ inj₁ true ∷ []) Examples.nonempty)) Unit.tt

masked-native-security : Transport.G (S.resource Examples.real) N.UC.≤UC Transport.G (S.resource Examples.ideal)
masked-native-security = preserves-≤UC Examples.masked-output-secure

masked-native-uniform : Transport.G (S.resource Examples.real) N.UC.≈ᵁ Transport.G (S.resource Examples.ideal)
masked-native-uniform = preserves-≈ᵁ {f = S.resource Examples.real} {g = S.resource Examples.ideal}
  (SourceSecurity.uniform⇒≈ᵁ {f = S.resource Examples.real} {g = S.resource Examples.ideal}
    (λ _ → tt , Examples.masked-simulation))

masked-native-closing-reward : N.evaluate
  (N.nativeTest (compileEnvironment Examples.echoEnvironment) Examples.adaptive-word Examples.first-ciphertext)
  (compile Examples.real) ≡ ½
masked-native-closing-reward = refl
