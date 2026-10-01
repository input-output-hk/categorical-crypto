{-# OPTIONS --safe --without-K --guardedness #-}

open import Data.Bool.Base
open import Data.Maybe.Base
open import Data.Product.Base
open import Data.Sum.Base
open import Data.Unit.Base
open import Level using (0ℓ)
open import Relation.Binary.PropositionalEquality

open import ProbabilisticLogic.Dp

open import CategoricalCrypto.Iface
open import CategoricalCrypto.Machines.Base
open import CategoricalCrypto.UC.Machine.Monitor

import CategoricalCrypto.Machines.Core as Core

module CategoricalCrypto.UC.Machine.MonitorTests
  {B : Iface} (report : Neg B → Pos B → Bool) (acc : Bool) where

private module MC = Core (𝒱ₚ 0ℓ)

monitor-query : (p : Maybe (Neg B)) (q : Neg B)
              → MC.step (monitorᴹ report) ((acc , p) , inj₂ (inj₁ q))
                ≡ returnₚ ((acc , just q) , inj₁ q)
monitor-query _ _ = refl

monitor-answer : (q : Neg B) (a : Pos B)
               → MC.step (monitorᴹ report) ((acc , just q) , inj₁ a)
                 ≡ returnₚ ((acc ∨ report q a , nothing) , inj₂ (inj₁ a))
monitor-answer _ _ = refl

monitor-flag-ask : (p : Maybe (Neg B))
             → MC.step (monitorᴹ report) ((acc , p) , inj₂ (inj₂ tt))
               ≡ returnₚ ((acc , p) , inj₂ (inj₂ acc))
monitor-flag-ask _ = refl
