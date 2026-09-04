{-# OPTIONS --safe --without-K --guardedness #-}

-- Computed pins for the semantics functor: layer 1's verdict probability and
-- the machine image's cumulative mass are the same rational, by `refl`.  The
-- whole pipeline evaluates — `graft`/`serve`, `drive`, `coinₚ` and the delay
-- monad's `cum`.  `agree` is `PrAgree` at one instance.
--
-- The same pin for `𝒢`'s own composition is out of reach, and that is measured
-- rather than guessed: `cum n` expands `2ⁿ` branches, while a point-free
-- composite in `𝒢` spends one delay junction per structural morphism of `α`,
-- `γ`, two `∘ᴹ` towers and the trace's `iter` — several dozen.  At `n = 16`
-- (16 s) the mass has not reached a value at all, so `Morphism-∘` has to be
-- proved rather than computed.

open import Data.Bool.Base
open import Data.Integer.Base using (+_)
open import Data.Product.Base
open import Data.Rational
open import Data.Unit.Base
open import Relation.Binary.PropositionalEquality

open import ProbabilisticLogic.Distribution.Uniform
open import ProbabilisticLogic.Dp

open import CategoricalCrypto.Iface
open import CategoricalCrypto.Protocol
open import CategoricalCrypto.Protocol.Machine
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

half : ℚ
half = + 1 / 2

layer₁ : Pr flip echo ≡ half
layer₁ = refl

-- Five steps: the coin's branch, and the `>>=ₚ` junctions the point, the
-- machine's step and the strategy's resumption each spend.
machine : cum 5 (runᴹ (morphism flip) echo) bool→ℚ ≡ half
machine = refl

agree : cum 6 (runᴹ (morphism flip) echo) bool→ℚ ≡ Pr flip echo
agree = refl

------------------------------------------------------------------------
-- Through a composite

-- `wireᵖ` relays the coin, so composing costs one call node and one grafting.
relayed : Protocol unitᴵ Coin
relayed = wireᵖ ∘ᵖ flip

layer₁-∘ : Pr relayed echo ≡ half
layer₁-∘ = refl

machine-∘ : cum 8 (runᴹ (morphism relayed) echo) bool→ℚ ≡ half
machine-∘ = refl
