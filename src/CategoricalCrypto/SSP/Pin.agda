{-# OPTIONS --safe --without-K #-}

-- Computed pins for the SSP readout: a distinguisher composed with a game
-- evaluates — `graft`/`serve`, `reindex` and `evalC` included — to its verdict
-- masses by `refl`, through `runᵖ` and through the setup's `observe`.  Both
-- verdicts are pinned, since only the `false` mass tells answering `false`
-- from aborting.

open import Data.Bool.Base
open import Data.Product.Base using (_,_)
open import Data.Rational using (0ℚ; 1ℚ; ½)
open import Data.Sum.Base
open import Data.Unit.Base
open import Function.Base using (const)
open import Relation.Binary.PropositionalEquality

open import ProbabilisticLogic.Distribution.RationalDist.Expectation using (Prᵇ⊥)
open import ProbabilisticLogic.Distribution.Uniform using (uniform-Bool)

open import CategoricalCrypto.SSP.Iface
open import CategoricalCrypto.SSP.Observation
open import CategoricalCrypto.SSP.Protocol
open import CategoricalCrypto.UC.Core

module CategoricalCrypto.SSP.Pin where

open Evaluation evaluationᵖ using (observe)

-- One oracle answering a bit.
Bitᴵ : Iface
Bitᴵ = record { Ch = ⊤ ; Q = const ⊤ ; R = const Bool }

flip nay stuck : Protocol unitᴵ Bitᴵ
flip  = record { St = ⊤ ; init = tt ; step = λ _ _ _ → coin uniform-Bool λ b → ret (tt , b) }
nay   = record { St = ⊤ ; init = tt ; step = λ _ _ _ → ret (tt , false) }
stuck = record { St = ⊤ ; init = tt ; step = λ _ _ _ → dead }

-- Answers `true`, `false`, `true`, …: its state crosses activations.
alt : Protocol unitᴵ Bitᴵ
alt = record { St = Bool ; init = true ; step = λ s _ _ → ret (not s , s) }

-- Ask once and report the answer.
echo : Protocol Bitᴵ Ωᴵ
echo = record { St = ⊤ ; init = tt ; step = λ _ _ _ → call tt tt λ b → ret (tt , b) }

-- Ask twice and report whether the answers agree.
same : Protocol Bitᴵ Ωᴵ
same = record
  { St = ⊤ ; init = tt
  ; step = λ _ _ _ → call tt tt λ b → call tt tt λ b′ → ret (tt , not (b xor b′)) }

echo-flip : Prᵇ⊥ true (runᵖ (echo ∘ᵖ flip)) ≡ ½
echo-flip = refl

echo-flip-false : Prᵇ⊥ false (runᵖ (echo ∘ᵖ flip)) ≡ ½
echo-flip-false = refl

-- `nay` and `stuck` agree on the `true` mass and are a unit apart on `false`.
echo-nay : Prᵇ⊥ true (runᵖ (echo ∘ᵖ nay)) ≡ Prᵇ⊥ true (runᵖ (echo ∘ᵖ stuck))
echo-nay = refl

echo-nay-false : Prᵇ⊥ false (runᵖ (echo ∘ᵖ nay)) ≡ 1ℚ
echo-nay-false = refl

echo-stuck-false : Prᵇ⊥ false (runᵖ (echo ∘ᵖ stuck)) ≡ 0ℚ
echo-stuck-false = refl

same-flip : Prᵇ⊥ true (runᵖ (same ∘ᵖ flip)) ≡ ½
same-flip = refl

same-alt : Prᵇ⊥ false (runᵖ (same ∘ᵖ alt)) ≡ 1ℚ
same-alt = refl

-- A tensor of games sharing the empty import (brzuska2018 Def. 6), asked on
-- each channel once.
both : Protocol (Bitᴵ ⊗ᴵ Bitᴵ) Ωᴵ
both = record
  { St = ⊤ ; init = tt
  ; step = λ _ _ _ → call (inj₁ tt) tt λ b → call (inj₂ tt) tt λ b′ → ret (tt , not (b xor b′)) }

both-flip-nay : Prᵇ⊥ true (runᵖ (both ∘ᵖ ((flip ⊗ᵖ nay) ∘ᵖ ⌜ ∇ ⌝))) ≡ ½
both-flip-nay = refl

-- The same composite read through the setup's evaluation.
observe-echo-flip : Prᵇ⊥ true (observe echo flip) ≡ ½
observe-echo-flip = refl
