{-# OPTIONS --safe --without-K --guardedness #-}

-- Computed pins for the semantics functor: layer 1's verdict probability and
-- the machine image's cumulative mass are the same rational, by `refl`.  The
-- whole pipeline evaluates — `graft`/`serve`, `drive`, `coinₚ` and the delay
-- monad's `cum`; `agree` is `Protocol.Machine.Agree.prAgree`'s conclusion at a
-- computed witness.
--
-- The same pin for `𝒢`'s own composition is out of reach: `cum n` expands `2ⁿ`
-- branches, while a point-free composite in `𝒢` spends one delay junction per
-- structural morphism of `α`, `γ`, two `∘ᴹ` towers and the trace's `iter` —
-- several dozen.  At `n = 16` (16 s) the mass has not reached a value at all,
-- so `Protocol.Machine.Compose.morphismCompose` is proved rather than computed.

open import Data.Bool.Base
open import Data.Product.Base
open import Data.Rational
open import Data.Rational.Properties using (≤-refl)
open import Data.Unit.Base
open import Relation.Binary.PropositionalEquality

open import ProbabilisticLogic.Distribution.Uniform
open import ProbabilisticLogic.Dp
open import ProbabilisticLogic.Dp.Advantage
open import ProbabilisticLogic.Dp.Settle

open import CategoricalCrypto.Iface
open import CategoricalCrypto.Protocol
open import CategoricalCrypto.Protocol.Machine
open import CategoricalCrypto.Protocol.Machine.Agree
open import CategoricalCrypto.Protocol.Observe
open import CategoricalCrypto.Strategy

module CategoricalCrypto.Protocol.Machine.Pin where

-- Ask once, answer with a fair coin.
Coin : Iface
Coin = Bool ⇿ ⊤

flip : Protocol unitᴵ Coin
flip = record
  { St   = ⊤
  ; init = tt
  ; step = λ _ _ → coin uniform-Bool λ b → ret (tt , b)
  }

-- Ask once and report the answer.
echo : Strat ⊤ Bool
echo = ask tt out

layer₁ : Pr flip echo ≡ ½
layer₁ = refl

layer₁-false : Prᵇ flip false echo ≡ ½
layer₁-false = refl

-- `prAgree`'s conclusion at a computed witness: from five steps on (the coin's
-- branch, and the `>>=ₚ` junctions the point, the machine's step and the
-- strategy's resumption each spend) the mass IS the verdict probability, at
-- every larger budget.
agree : Attains (runᴹ (morphism flip) echo) bool→ℚ (Pr flip echo)
agree = 5 , λ _ → refl

-- …and at the other verdict, which is the reading `prAgree` is stated at:
-- `indᵇ true` IS `bool→ℚ`, so `agree` above is its `b = true` instance and only
-- this one exercises `indᵇ false`.
agree-false : Attains (runᴹ (morphism flip) echo) (indᵇ false) (Prᵇ flip false echo)
agree-false = 5 , λ _ → refl

-- Divergence: `drive dead` is `botₚ`, whose mass `cum` never counts, and layer
-- 1's `evalC dead` parks the same mass on `nothing`.
stuck : Protocol unitᴵ Coin
stuck = record { St = ⊤ ; init = tt ; step = λ _ _ → dead }

layer₁-dead : Pr stuck echo ≡ 0ℚ
layer₁-dead = refl

machine-dead : Upper (runᴹ (morphism stuck) echo) 0ℚ
machine-dead = upper-run stuck echo ≤-refl

-- …and what observing the SECOND verdict buys, at that instance: `nay` answers
-- `false` where `stuck` diverges, so the two agree on the `true`-mass and are a
-- whole unit apart on the `false`-mass.  A one-sided observation identifies
-- them (`Dp.Advantage`'s header).
nay : Protocol unitᴵ Coin
nay = record { St = ⊤ ; init = tt ; step = λ _ _ → ret (tt , false) }

nay-true : Pr nay echo ≡ Pr stuck echo
nay-true = refl

nay-false : cum 8 (runᴹ (morphism nay) echo) (indᵇ false) ≡ 1ℚ
nay-false = refl

stuck-false : Attains (runᴹ (morphism stuck) echo) (indᵇ false) 0ℚ
stuck-false = prAgree false stuck echo

------------------------------------------------------------------------
-- Through a composite

-- `wireᵖ` relays the coin, so composing costs one call node and one grafting.
relayed : Protocol unitᴵ Coin
relayed = wireᵖ ∘ᵖ flip

layer₁-∘ : Pr relayed echo ≡ ½
layer₁-∘ = refl

-- `prAgree` at a layer-1 composite: `graft`/`serve` evaluated on both sides.
-- `𝒢`'s own composition is not reached (see the header).
agree-∘ : Attains (runᴹ (morphism relayed) echo) bool→ℚ (Pr relayed echo)
agree-∘ = 8 , λ _ → refl
