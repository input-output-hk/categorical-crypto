{-# OPTIONS --safe --without-K #-}

open import Data.Maybe.Base
open import Data.Product.Base

open import ProbabilisticLogic.Distribution.RationalDist

open import CategoricalCrypto.GamePlaying.Partial
open import CategoricalCrypto.Iface
open import CategoricalCrypto.Protocol
open import CategoricalCrypto.Protocol.Observe

module CategoricalCrypto.Protocol.Reachability {B : Iface} (P : Protocol unitᴵ B) where

-- Only successful outcomes yield states; the divergence sink is not a transition.
data Reachable : St P → Set where
  start : Reachable (init P)
  advance : ∀ {s t q response} → Reachable s
          → InSupport (just (t , response)) (kernel P s q) → Reachable t

reachable-invariant : {I : St P → Set} → Preserved⊥ I (kernel P) → I (init P)
                    → ∀ {s} → Reachable s → I s
reachable-invariant pres inv₀ start = inv₀
reachable-invariant pres inv₀ (advance {s = s} {q = q} reach edge) =
  OnSupport-InSupport {μ = kernel P s q} (pres s q (reachable-invariant pres inv₀ reach)) edge
