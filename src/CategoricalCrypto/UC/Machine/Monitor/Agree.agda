{-# OPTIONS --safe --without-K --guardedness #-}

-- Monitor agreement at embedded strategies: `docs/event-bounds-in-setup.md`
-- §2 obligation 4.
--
-- `flag-agree` runs the accumulator's flag wire (`UC.Machine.Monitor.accᴹ`) at
-- `flagStrat d`: it IS the run of the process under the watch, as `_≈ₚ_`,
-- because the flag equals the accumulator along the run.

open import Categories.Category

open import Data.Bool.Base
open import Data.Bool.Properties.Ext
open import Data.Maybe.Base
open import Data.Product.Base
open import Data.Sum.Base as Sum
open import Data.Unit.Base
open import Data.Unit.Polymorphic.Base using () renaming (tt to ttᵛ)
open import Function.Base
open import Level
open import Relation.Binary.PropositionalEquality using (_≡_; cong; refl; subst; trans)

open import ProbabilisticLogic.Dp
open import ProbabilisticLogic.Dp.Reasoning

open import CategoricalCrypto.Iface
open import CategoricalCrypto.Machines.Base
open import CategoricalCrypto.Machines.Pointwise
open import CategoricalCrypto.Protocol.Machine
open import CategoricalCrypto.Protocol.Machine.Run
open import CategoricalCrypto.Strategy
open import CategoricalCrypto.UC.Machine
open import CategoricalCrypto.UC.Machine.Monitor
open import CategoricalCrypto.UC.Machine.StateEvent
open import CategoricalCrypto.UC.Machine.StateEvent.Read

import CategoricalCrypto.Machines.Core as Core
import CategoricalCrypto.Machines.Sim as Sim

module CategoricalCrypto.UC.Machine.Monitor.Agree where

open Core (𝒱ₚ 0ℓ)
open Sim (𝒱ₚ 0ℓ) (𝒫ₚ 0ℓ)

private module 𝒫 = Category 𝒫ᴵ

------------------------------------------------------------------------
-- Agreement

module _ {B : Iface} (report : Neg B → Pos B → Bool) (u : Proc unitᴵ B) where

  private
    w = accᴹ report u ▷ reported report u

    run-flag : (s : MC.St u) (a : Bool) (p : Maybe (Neg B)) (f : Bool) → f ≡ a
             → (d : Strat (Neg B) (Pos B))
             → runᴹFrom w ((s , (a , p)) , f) (flagStrat d) ≈ₚ runᴹFrom u s (watchFrom report a d)
    run-flag s a p f refl (out _)    = >>=ₚ-identityˡ _ _
    run-flag s a p f eq   (coin μ k) = bindᶠ λ c → run-flag s a p f eq (k c)
    run-flag s a p f eq   (ask q k)  =
          bind-map (MC.step u (s , inj₂ q) >>=ₚ settle report u (a , just q)) _ _
      ⟨≈⟩ >>=ₚ-assoc (MC.step u (s , inj₂ q)) _ _
      ⟨≈⟩ bindᶠ λ where
            (_  , inj₁ ())
            (s′ , inj₂ b) →
                  >>=ₚ-identityˡ _ _
              ⟨≈⟩ run-flag s′ (a ∨ report q b) nothing _
                    (trans (cong (_∨ (a ∨ report q b)) eq) (∨-idemˡ a (report q b)))
                    (k b)

  flag-agree : (d : Strat (Neg B) (Pos B))
             → runᴹ (accᴹ report u ▷ reported report u) (flagStrat d) ≈ₚ runᴹ u (watchFrom report false d)
  flag-agree d = bind-map (mapₚ _ (MC.point (MC.state u) ttᵛ)) _ _
             ⟨≈⟩ bind-map (MC.point (MC.state u) ttᵛ) _ _
             ⟨≈⟩ bindᶠ (λ s → run-flag s false nothing false refl d)
