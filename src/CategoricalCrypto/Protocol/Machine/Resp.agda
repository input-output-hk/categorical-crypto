{-# OPTIONS --safe --without-K --guardedness #-}

-- The semantics functor respects the protocol equality: `morphism` sends
-- `Protocol.Sim._≈ᵖ_` to the hom equality of `𝒢ₚ`.
--
-- The state map `idle s ↦ idle (θ s)` is NOT a machine simulation.  A `wait`
-- state stores the continuation, and where `P′` waits on `k′` the image of `P`'s
-- `wait k` waits on `(_>>=ᶜ ret ∘ map₁ θ) ∘ k`, equal to `k′` only pointwise up
-- to `≈ᶜ`; `≈ₚ` tests the states themselves, so without funext the step square
-- does not close.  As in `Protocol.Machine.Compose`, both legs are simulations
-- out of a third machine, `machineʳ`, whose state pairs the two configurations
-- with the `≈ᶜ` proof relating them and steps them in lockstep along it.

open import Categories.Category

open import Data.Product.Base
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Function.Base
open import Level
open import Relation.Binary.PropositionalEquality
import Relation.Binary.Construct.Closure.Equivalence as EqC

open import ProbabilisticLogic.Dp
open import ProbabilisticLogic.Dp.Coin
open import ProbabilisticLogic.Dp.Reasoning

open import CategoricalCrypto.Iface
open import CategoricalCrypto.Machines.Base
open import CategoricalCrypto.Protocol
open import CategoricalCrypto.Protocol.Machine
open import CategoricalCrypto.Protocol.Sim

import CategoricalCrypto.Machines.Core as Core
import CategoricalCrypto.Machines.Pointwise as Pw
import CategoricalCrypto.Machines.Sim as Sim

module CategoricalCrypto.Protocol.Machine.Resp where

private
  module MC = Core (𝒱ₚ 0ℓ)
  module S  = Sim (𝒱ₚ 0ℓ) (𝒫ₚ 0ℓ)

private variable A B : Iface

module _ {P P′ : Protocol A B} (σ : P ≲ᵖ P′) where

  ------------------------------------------------------------------------
  -- The related-configuration machine

  data RSt : Set where
    idleʳ : St P → RSt
    waitʳ : (k : Pos A → Calls A (St P × Pos B)) (k′ : Pos A → Calls A (St P′ × Pos B))
          → (∀ a⁺ → k a⁺ >>=ᶜ (ret ∘ map₁ (θ σ)) ≈ᶜ k′ a⁺) → RSt

  driveʳ : (t : Calls A (St P × Pos B)) {t′ : Calls A (St P′ × Pos B)}
         → t >>=ᶜ (ret ∘ map₁ (θ σ)) ≈ᶜ t′ → Dₚ (RSt × (Neg A ⊎ Pos B))
  driveʳ (ret (s , b⁺)) (ret refl) = returnₚ (idleʳ s , inj₂ b⁺)
  driveʳ (call a k)     (call h)   = returnₚ (waitʳ k _ h , inj₁ a)
  driveʳ (coin μ k)     (coin h)   = coinₚ μ >>=ₚ λ b → driveʳ (k b) (h b)
  driveʳ dead           dead       = botₚ

  stepʳ : RSt × (Pos A ⊎ Neg B) → Dₚ (RSt × (Neg A ⊎ Pos B))
  stepʳ (idleʳ s , inj₂ b⁻)     = driveʳ (step P s b⁻) (θ-step σ s b⁻)
  stepʳ (waitʳ k _ h , inj₁ a⁺) = driveʳ (k a⁺) (h a⁺)
  stepʳ (idleʳ _ , inj₁ _)      = botₚ
  stepʳ (waitʳ _ _ _ , inj₂ _)  = botₚ

  machineʳ : MC.Machine (Pos A ⊎ Neg B) (Neg A ⊎ Pos B)
  machineʳ = MC.mk record { obj = RSt ; point = λ _ → returnₚ (idleʳ (init P)) } stepʳ

  ------------------------------------------------------------------------
  -- Its two projections

  private
    π : RSt → MSt P
    π (idleʳ s)     = idle s
    π (waitʳ k _ _) = wait k

    π′ : RSt → MSt P′
    π′ (idleʳ s)      = idle (θ σ s)
    π′ (waitʳ _ k′ _) = wait k′

    π-drive : (t : Calls A (St P × Pos B)) {t′ : Calls A (St P′ × Pos B)}
              (e : t >>=ᶜ (ret ∘ map₁ (θ σ)) ≈ᶜ t′)
            → (driveʳ t e >>=ₚ Pw.padϕ π) ≈ₚ drive P t
    π-drive (ret (s , b⁺)) (ret refl) = >>=ₚ-identityˡ (idleʳ s , inj₂ b⁺) (Pw.padϕ π)
    π-drive (call a k)     (call h)   = >>=ₚ-identityˡ (waitʳ k _ h , inj₁ a) (Pw.padϕ π)
    π-drive (coin μ k)     (coin h)   = >>=ₚ-assoc (coinₚ μ) _ _ ⟨≈⟩ bindᶠ (λ b → π-drive (k b) (h b))
    π-drive dead           dead       = bot-bind-≈ₚ (Pw.padϕ π)

    π′-drive : (t : Calls A (St P × Pos B)) {t′ : Calls A (St P′ × Pos B)}
               (e : t >>=ᶜ (ret ∘ map₁ (θ σ)) ≈ᶜ t′)
             → (driveʳ t e >>=ₚ Pw.padϕ π′) ≈ₚ drive P′ t′
    π′-drive (ret (s , b⁺)) (ret refl) = >>=ₚ-identityˡ (idleʳ s , inj₂ b⁺) (Pw.padϕ π′)
    π′-drive (call a k)     (call h)   = >>=ₚ-identityˡ (waitʳ k _ h , inj₁ a) (Pw.padϕ π′)
    π′-drive (coin μ k)     (coin h)   = >>=ₚ-assoc (coinₚ μ) _ _ ⟨≈⟩ bindᶠ (λ b → π′-drive (k b) (h b))
    π′-drive dead           dead       = bot-bind-≈ₚ (Pw.padϕ π′)

  π-sim : machineʳ S.≲ morphism P
  π-sim = Pw.simFn π (λ _ → >>=ₚ-identityˡ (idleʳ (init P)) _) λ where
    (idleʳ s , inj₂ b⁻)     → π-drive (step P s b⁻) (θ-step σ s b⁻)
    (waitʳ k _ h , inj₁ a⁺) → π-drive (k a⁺) (h a⁺)
    (idleʳ _ , inj₁ _)      → bot-bind-≈ₚ (Pw.padϕ π)
    (waitʳ _ _ _ , inj₂ _)  → bot-bind-≈ₚ (Pw.padϕ π)

  π′-sim : machineʳ S.≲ morphism P′
  π′-sim = Pw.simFn π′ (λ _ → >>=ₚ-identityˡ (idleʳ (init P)) _ ⟨≈⟩ ret≡ (cong idle (θ-init σ))) λ where
    (idleʳ s , inj₂ b⁻)     → π′-drive (step P s b⁻) (θ-step σ s b⁻)
    (waitʳ k _ h , inj₁ a⁺) → π′-drive (k a⁺) (h a⁺)
    (idleʳ _ , inj₁ _)      → bot-bind-≈ₚ (Pw.padϕ π′)
    (waitʳ _ _ _ , inj₂ _)  → bot-bind-≈ₚ (Pw.padϕ π′)

------------------------------------------------------------------------
-- Respect

morphism-sim : {P P′ : Protocol A B} → P ≲ᵖ P′ → 𝒢ₚ 0ℓ [ morphism P ≈ morphism P′ ]
morphism-sim σ = S.≲⇒≈ᴹ˘ (π-sim σ) S.○ᴹ S.≲⇒≈ᴹ (π′-sim σ)

morphism-resp : {P P′ : Protocol A B} → P ≈ᵖ P′ → 𝒢ₚ 0ℓ [ morphism P ≈ morphism P′ ]
morphism-resp = EqC.gfold S.≈ᴹ-isEquivalence morphism morphism-sim
