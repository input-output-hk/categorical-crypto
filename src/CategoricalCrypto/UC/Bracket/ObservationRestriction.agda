{-# OPTIONS --safe --without-K --guardedness #-}

-- Restriction from full PM observations to well-bracketed observations on
-- the same machines. The verdict interface has one channel, so a test needs
-- no monitor: every output following a legal input is already a legal move.

open import Data.Product.Base
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Unit.Polymorphic.Base
open import Level

open import ProbabilisticLogic.Dp

open import CategoricalCrypto.Machines.Base
open import CategoricalCrypto.SSP.Iface
open import CategoricalCrypto.UC.Bracket
open import CategoricalCrypto.UC.Machine hiding (Ωᴵ)

import Data.Unit.Base as Unit
import CategoricalCrypto.Machines.Core as Core

module CategoricalCrypto.UC.Bracket.ObservationRestriction where

private
  module MC = Core (𝒱ₚ 0ℓ)

private variable
  A : Iface

verdict-W : (t : Proc (flat A) (flat Ωᴵ)) → W {A} {Ωᴵ} t
verdict-W {A} t = record
  { I = I
  ; I-init = λ n → Supp-all _ (λ _ → tt) n _
  ; I-step = step-W
  }
  where
  I : MC.St t → Phase A Ωᴵ → Set
  I _ _ = ⊤

  legal : {b : Ch Ωᴵ} → (y : MC.St t × (Σ (Ch A) (Q A) ⊎ Σ (Ch Ωᴵ) (R Ωᴵ))) → Legal I (serving b) y
  legal {Unit.tt} (_ , inj₁ (a , q)) = calling Unit.tt a , call , tt
  legal {Unit.tt} (_ , inj₂ (Unit.tt , r)) = idle , answer , tt

  step-W : ∀ {s φ x φ′} → I s φ → Opp φ x φ′ → ∀ n
         → Supp n (MC.step t (s , x)) (Legal I φ′)
  step-W _ query n = Supp-all _ legal n _
  step-W _ return n = Supp-all _ legal n _
