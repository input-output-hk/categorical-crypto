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

-- `PrAgree` asserts the mass STAYS at the verdict probability past its witness,
-- so one budget is a point sample: these pin the next two.
agree₊₁ : cum 7 (runᴹ (morphism flip) echo) bool→ℚ ≡ Pr flip echo
agree₊₁ = refl

agree₊₂ : cum 8 (runᴹ (morphism flip) echo) bool→ℚ ≡ Pr flip echo
agree₊₂ = refl

-- Divergence: `drive dead` is `botₚ`, whose mass `cum` never counts, and layer
-- 1's `evalC dead` parks the same mass on `nothing`.  Both branches of the
-- header's claim about `dead`, at one instance.
stuck : Protocol unitᴵ Coin
stuck = record { St = ⊤ ; init = tt ; step = λ _ _ → dead }

layer₁-dead : Pr stuck echo ≡ 0ℚ
layer₁-dead = refl

machine-dead : cum 8 (runᴹ (morphism stuck) echo) bool→ℚ ≡ 0ℚ
machine-dead = refl

-- …and what observing the SECOND verdict buys, at that instance: `nay` answers
-- `false` where `stuck` diverges, so the two agree on the `true`-mass and are a
-- whole unit apart on the `false`-mass.  A one-sided observation identified
-- them (proposal §1, `docs/kb/frontier/15-probabilistic-uc-model.typ`).
nay : Protocol unitᴵ Coin
nay = record { St = ⊤ ; init = tt ; step = λ _ _ → ret (tt , false) }

nay-true : Pr nay echo ≡ Pr stuck echo
nay-true = refl

nay-false : cum 8 (runᴹ (morphism nay) echo) (indᵇ false) ≡ 1ℚ
nay-false = refl

stuck-false : cum 8 (runᴹ (morphism stuck) echo) (indᵇ false) ≡ 0ℚ
stuck-false = refl

------------------------------------------------------------------------
-- Through a composite

-- `wireᵖ` relays the coin, so composing costs one call node and one grafting.
relayed : Protocol unitᴵ Coin
relayed = wireᵖ ∘ᵖ flip

layer₁-∘ : Pr relayed echo ≡ half
layer₁-∘ = refl

machine-∘ : cum 8 (runᴹ (morphism relayed) echo) bool→ℚ ≡ half
machine-∘ = refl

-- The composite half of `PrAgree`, which is the pin that would break if
-- `_∘ᵖ_`'s `graft`/`serve` and `𝒢`'s trace-composition ever disagreed.
agree-∘ : cum 8 (runᴹ (morphism relayed) echo) bool→ℚ ≡ Pr relayed echo
agree-∘ = refl
