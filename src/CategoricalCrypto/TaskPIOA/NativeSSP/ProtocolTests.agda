{-# OPTIONS --safe --without-K #-}

module CategoricalCrypto.TaskPIOA.NativeSSP.ProtocolTests where

open import Data.Bool.Base
open import Data.List.Base using ([]; _∷_)
open import Data.Maybe.Base using (just; nothing)
open import Data.Product.Base using (_,_)
open import Data.Sum.Base using (inj₁; inj₂)
open import Data.Unit.Base
open import Relation.Binary.PropositionalEquality

open import CategoricalCrypto.SSP.Dist.Kernel using (_>>=ᶜ_)
open import CategoricalCrypto.SSP.Iface using (Ωᴵ)
open import CategoricalCrypto.SSP.Observation using (runᵖ)
import CategoricalCrypto.SSP.Protocol as P
open import CategoricalCrypto.TaskPIOA.Core using (productSignature; empty)
import CategoricalCrypto.TaskPIOA.Tests as Fixture
open import CategoricalCrypto.TaskPIOA.NativeSSP.Core
open import CategoricalCrypto.TaskPIOA.NativeSSP.Protocol
open import ProbabilisticLogic.Distribution.RationalDist using (return-ℚ)

private
  S = productSignature (Fixture.coinSignature empty) Fixture.receiverSignature empty
  W = installed Fixture.wire (compile Fixture.pulse) (compile Fixture.receiver)

  send : P.Calls (Boundary S) ⊤
  send = P.call (inj₂ (inj₁ false)) tt λ _ →
    P.call (inj₂ (inj₁ true)) tt λ _ → P.ret tt

  read : P.Calls (Boundary S) Bool
  read = P.call (inj₂ (inj₂ tt)) tt λ where
    (just (inj₂ b)) → P.ret b
    _ → P.ret false

  consumer : P.Calls (Boundary S) Bool → P.Protocol (Boundary S) Ωᴵ
  consumer t = record { St = ⊤ ; init = tt ; step = λ _ _ _ → P.mapᶜ (tt ,_) t }

actual-send-before-read : scheduled {S} W Fixture.send-first (P.init W)
  ≡ P.ret (inj₁ true ∷ inj₂ true ∷ [])
actual-send-before-read = refl

actual-read-before-send : scheduled {S} W Fixture.read-first (P.init W)
  ≡ P.ret (inj₂ false ∷ inj₁ true ∷ [])
actual-read-before-send = refl

actual-disabled-ack : P.step W (P.init W) (inj₂ (inj₁ true)) tt ≡ P.ret (P.init W , nothing)
actual-disabled-ack = refl

actual-boolean-send-before-read :
  runᵖ (consumer (send >>=ᶜ λ _ → read) P.∘ᵖ W) ≡ return-ℚ (just true)
actual-boolean-send-before-read = refl

actual-boolean-read-before-send :
  runᵖ (consumer (read >>=ᶜ λ b → send >>=ᶜ λ _ → P.ret b) P.∘ᵖ W) ≡ return-ℚ (just false)
actual-boolean-read-before-send = refl
