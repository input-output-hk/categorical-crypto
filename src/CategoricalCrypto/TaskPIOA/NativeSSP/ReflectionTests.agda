{-# OPTIONS --safe --without-K #-}

module CategoricalCrypto.TaskPIOA.NativeSSP.ReflectionTests where

open import Data.Bool.Base
open import Data.Integer.Base using (+_)
open import Data.List.Base using (List; []; _∷_)
open import Data.Maybe.Base using (just)
open import Data.Product.Base
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; _/_)
open import Data.Sum.Base using (inj₁; inj₂; _⊎_)
open import Data.Unit.Base
import Data.Unit.Polymorphic as Unit
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary using (¬_)

open import CategoricalCrypto.SSP.Dist.Kernel using (done; toss)
import CategoricalCrypto.TaskPIOA.Core as Source
open import CategoricalCrypto.TaskPIOA.Core using (Wiring; empty; bit; productSignature; Schedule)
import CategoricalCrypto.TaskPIOA.Setup as S
import CategoricalCrypto.TaskPIOA.Security as SourceSecurity
import CategoricalCrypto.TaskPIOA.SSPAdapterTests as Rational
import CategoricalCrypto.TaskPIOA.Tests as Examples
open import CategoricalCrypto.TaskPIOA.NativeSSP.Core
open import CategoricalCrypto.TaskPIOA.NativeSSP.Morphism
open import CategoricalCrypto.TaskPIOA.NativeSSP.Security
import CategoricalCrypto.TaskPIOA.NativeSSP.Setup as N

noncanonical : Machine (Examples.coinSignature empty)
noncanonical = record
  { memory = bit ; start = false ; deliver = λ ()
  ; select = λ where q false → just (inj₂ tt) ; q true → just (inj₁ q)
  ; owned = λ where q false a refl → refl ; q true a refl → refl
  ; transition = λ where (inj₂ _) _ → toss Rational.biased done ; (inj₁ _) q → done q }

masked-reflected-uniform : S.resource Examples.real S.UC.≈ᵁ S.resource Examples.ideal
masked-reflected-uniform = reflects-≈ᵁ {f = S.resource Examples.real} {g = S.resource Examples.ideal}
  (preserves-≈ᵁ {f = S.resource Examples.real} {g = S.resource Examples.ideal}
    (SourceSecurity.uniform⇒≈ᵁ {f = S.resource Examples.real} {g = S.resource Examples.ideal}
      (λ _ → tt , Examples.masked-simulation)))

masked-reflected-security : S.resource Examples.real S.UC.≤UC S.resource Examples.ideal
masked-reflected-security = reflects-≤UC (preserves-≤UC Examples.masked-output-secure)

right-sender-wire : Wiring Examples.receiverSignature (Examples.coinSignature empty) empty
right-sender-wire = record
  { left = Source.right Examples.wire ; right = Source.left Examples.wire
  ; boundary-live = λ () }

Receiver Network : S.Syntax.ObjTerm
Receiver = N.Syntax.Var Examples.receiverSignature
Network = N.Syntax.Var (productSignature Examples.receiverSignature (Examples.coinSignature empty) empty)

native-converter : N.Syntax.HomTerm Receiver Network
native-converter = N.Syntax.var (N.wire right-sender-wire) N.Syntax.∘
  (N.Syntax.id N.Syntax.⊗₁ N.Syntax.var (N.install noncanonical)) N.Syntax.∘ N.Syntax.ρ⇐

source-converter : S.Syntax.HomTerm Receiver Network
source-converter = sampleContext native-converter

source-ideal : S.Syntax.HomTerm S.Syntax.unit (Receiver S.Syntax.⊗₀ S.Syntax.unit)
source-ideal = S.Syntax.ρ⇐ S.Syntax.∘ S.Syntax.var (S.install Examples.receiver)

source-real : S.Syntax.HomTerm S.Syntax.unit (Network S.Syntax.⊗₀ S.Syntax.unit)
source-real = S.UC.sub source-converter S.Syntax.∘ source-ideal

native-converter-witness : Transport.G source-real
  N.UC.≈ᵁ (N.UC.sub native-converter N.Syntax.∘ Transport.G source-ideal)
native-converter-witness = N.UC.≈ᵁ-trans
  (N.UC.≈C⇒≈ᵁ (simulator-square source-converter source-ideal))
  (N.UC.≈ᵁ-sym (Coverage.SimulatorRepresentation.action
    (simulator-representation native-converter) (Transport.G source-ideal)))

native-converter-security : Transport.G source-real N.UC.≤UC Transport.G source-ideal
native-converter-security = N.UC.dummy-complete (native-converter , native-converter-witness)

reflected-converter-witness : source-real S.UC.≤UC source-ideal
reflected-converter-witness = reflects-≤UC-witness native-converter native-converter-witness

reflected-converter-security : source-real S.UC.≤UC source-ideal
reflected-converter-security = reflects-≤UC native-converter-security

converter-word : Schedule (productSignature Examples.receiverSignature (Examples.coinSignature empty) empty)
converter-word = inj₂ false ∷ inj₂ true ∷ inj₁ tt ∷ []

receiver-reward : List (Bool ⊎ Bool) → ℚ
receiver-reward [] = 0ℚ
receiver-reward (inj₂ _ ∷ xs) = receiver-reward xs
receiver-reward (inj₁ true ∷ _) = 1ℚ
receiver-reward (inj₁ false ∷ _) = 0ℚ

converter-test : N.Test Network
converter-test = N.test _ refl N.Syntax.id converter-word receiver-reward

native-converter-reward : N.evaluate (N.pull native-converter converter-test)
  (compile Examples.receiver) ≡ + 2 / 3
native-converter-reward = refl

source-converter-reward : S.evaluate (S.pull source-converter (sampleTest converter-test))
  (sampleMachine (compile Examples.receiver)) ≡ + 2 / 3
source-converter-reward = trans
  (sym (sample-evaluate (N.pull native-converter converter-test) (compile Examples.receiver)))
  native-converter-reward

compiled-source-converter-reward : N.evaluate
  (compileTest (S.pull source-converter (sampleTest converter-test)))
  (compileValues Receiver (sampleMachine (compile Examples.receiver))) ≡ + 2 / 3
compiled-source-converter-reward = trans
  (compile-source-evaluate (S.pull source-converter (sampleTest converter-test))
    (sampleMachine (compile Examples.receiver))) source-converter-reward

pulse-converter : N.Syntax.HomTerm Receiver Network
pulse-converter = N.Syntax.var (N.wire right-sender-wire) N.Syntax.∘
  (N.Syntax.id N.Syntax.⊗₁ N.Syntax.var (N.install (compile Examples.pulse))) N.Syntax.∘ N.Syntax.ρ⇐

pulse-converter-reward : N.evaluate (N.pull pulse-converter converter-test)
  (compile Examples.receiver) ≡ 1ℚ
pulse-converter-reward = refl

source-pulse-converter-reward : S.evaluate
  (S.pull (sampleContext pulse-converter) (sampleTest converter-test))
  (sampleMachine (compile Examples.receiver)) ≡ 1ℚ
source-pulse-converter-reward = trans
  (sym (sample-evaluate (N.pull pulse-converter converter-test) (compile Examples.receiver)))
  pulse-converter-reward

two-thirds-not-one : ¬ (+ 2 / 3 ≡ 1ℚ)
two-thirds-not-one ()

source-converter-tests-distinguished : ¬
  (S.pull source-converter (sampleTest converter-test)
    S.≋ S.pull (sampleContext pulse-converter) (sampleTest converter-test))
source-converter-tests-distinguished eq = two-thirds-not-one (trans (sym source-converter-reward)
  (trans (eq (sampleMachine (compile Examples.receiver))) source-pulse-converter-reward))

native-converter-tests-distinguished : ¬
  (N.pull native-converter converter-test N.≋ N.pull pulse-converter converter-test)
native-converter-tests-distinguished eq = two-thirds-not-one (trans (sym native-converter-reward)
  (trans (eq (compile Examples.receiver)) pulse-converter-reward))

converter-is-nontrivial : ¬ (native-converter N.∼ pulse-converter)
converter-is-nontrivial eq = two-thirds-not-one (trans (sym native-converter-reward)
  (trans (N.test-preserves converter-test (eq (compile Examples.receiver))) pulse-converter-reward))

send-test read-test : S.Test S.Syntax.unit
send-test = S.test _ refl (S.Syntax.var (S.install Examples.network))
  Examples.send-first Examples.receiver-accepts
read-test = S.test _ refl (S.Syntax.var (S.install Examples.network))
  Examples.read-first Examples.receiver-accepts

source-send-reward : S.evaluate send-test Unit.tt ≡ 1ℚ
source-send-reward = refl

source-read-reward : S.evaluate read-test Unit.tt ≡ 0ℚ
source-read-reward = refl

native-send-reward : N.evaluate (compileTest send-test) (compileValues S.Syntax.unit Unit.tt) ≡ 1ℚ
native-send-reward = trans (compile-source-evaluate send-test Unit.tt) source-send-reward

native-read-reward : N.evaluate (compileTest read-test) (compileValues S.Syntax.unit Unit.tt) ≡ 0ℚ
native-read-reward = trans (compile-source-evaluate read-test Unit.tt) source-read-reward

source-order-distinguished : ¬ (send-test S.≋ read-test)
source-order-distinguished eq with eq Unit.tt
... | ()

native-order-distinguished : ¬ (compileTest send-test N.≋ compileTest read-test)
native-order-distinguished eq = source-order-distinguished (ν-mono {S.Syntax.unit} {send-test} {read-test} eq)
