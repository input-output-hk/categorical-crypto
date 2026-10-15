{-# OPTIONS --safe --without-K #-}

module CategoricalCrypto.TaskPIOA.NativeSSP.ProtocolTests where

open import Data.Bool.Base
open import Data.List.Base using ([]; _∷_)
open import Data.Maybe.Base using (nothing)
open import Data.Product.Base using (_,_)
open import Data.Sum.Base using (inj₁; inj₂)
open import Data.Unit.Base
open import Relation.Binary.PropositionalEquality

import CategoricalCrypto.SSP.Protocol as P
open import CategoricalCrypto.TaskPIOA.Core using (productSignature; empty)
import CategoricalCrypto.TaskPIOA.Tests as Fixture
open import CategoricalCrypto.TaskPIOA.NativeSSP.Core
open import CategoricalCrypto.TaskPIOA.NativeSSP.Protocol

private
  S = productSignature (Fixture.coinSignature empty) Fixture.receiverSignature empty
  W = installed Fixture.wire (compile Fixture.pulse) (compile Fixture.receiver)

actual-send-before-read : scheduled {S} W Fixture.send-first (P.init W)
  ≡ P.ret (inj₁ true ∷ inj₂ true ∷ [])
actual-send-before-read = refl

actual-read-before-send : scheduled {S} W Fixture.read-first (P.init W)
  ≡ P.ret (inj₂ false ∷ inj₁ true ∷ [])
actual-read-before-send = refl

actual-disabled-ack : P.step W (P.init W) (inj₂ (inj₁ true)) tt ≡ P.ret (P.init W , nothing)
actual-disabled-ack = refl
