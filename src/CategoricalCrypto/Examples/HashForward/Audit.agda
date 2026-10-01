{-# OPTIONS --safe --without-K --guardedness #-}

-- The toy's emulation as an event bound at the machine: the simulator is absorbed
-- into the adversary (`UC.Machine.EventBounds.bounded-absorb`), and its
-- two queries per `peekᴬ` (`Examples.HashForward.UC.simQB`) double the adversary's
-- rate.  `real-factors` is an exact machine equality, so any bound on the ideal
-- run carries to the real one with no slack.

open import Categories.Category

open import Data.Nat.Base as ℕ
open import Data.Rational using (ℚ)

open import ProbabilisticLogic.Dp
open import ProbabilisticLogic.Dp.Advantage

open import CategoricalCrypto.Iface
open import CategoricalCrypto.Protocol.Machine
open import CategoricalCrypto.Strategy
open import CategoricalCrypto.UC.Machine
open import CategoricalCrypto.UC.Machine.Dictionary
open import CategoricalCrypto.UC.Machine.EventBounds
open import CategoricalCrypto.UC.Machine.Run

module CategoricalCrypto.Examples.HashForward.Audit (Msg Dig : Set) where

open import CategoricalCrypto.Examples.HashForward Msg Dig
open import CategoricalCrypto.Examples.HashForward.UC Msg Dig

private
  module 𝒫 = Category 𝒫ᴵ
  open 𝒫.HomReasoning

  variable
    k q : ℕ
    r : ℚ

hf-bounded : AdvBoundedAt (k ℕ.* 2) q r ideal → AdvBoundedAt k q r real
hf-bounded = bounded-absorb real-factors simQB

hf-exact : (d : Strat (Neg Honᴵ) (Pos Honᴵ)) (a : Proc Advᴵ 𝟭ᴵ) (w : Proc unitᴵ Resᴵ)
         → runᴹ ((plugᴹ a 𝒫.∘ real) 𝒫.∘ w) d ≈ₚ runᴹ ((plugᴹ (a 𝒫.∘ simulator) 𝒫.∘ ideal) 𝒫.∘ w) d
hf-exact d a w = runᴹ-resp-≈ᴹ ((𝒫.∘-resp-≈ʳ real-factors ○ plug-absorb a simulator ideal) ⟩∘⟨refl) d

hf-pr-bound : (d : Strat (Neg Honᴵ) (Pos Honᴵ)) (a : Proc Advᴵ 𝟭ᴵ) (w : Proc unitᴵ Resᴵ)
            → Upper (runᴹ ((plugᴹ (a 𝒫.∘ simulator) 𝒫.∘ ideal) 𝒫.∘ w) d) r
            → Upper (runᴹ ((plugᴹ a 𝒫.∘ real) 𝒫.∘ w) d) r
hf-pr-bound d a w = upper-≈ (hf-exact d a w)
