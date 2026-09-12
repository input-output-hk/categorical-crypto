{-# OPTIONS --safe --without-K --guardedness #-}

-- Acceptance instance for the composed statement: the attack the composition
-- is about, and the ceiling it runs into.
--
-- `bias` is a corrupted committer that waits for the honest share and then
-- opens to a DIFFERENT bit — it commits to `H(true ∷ r)` and opens at the
-- share `s`, which forces P2's output to `s xor s`, i.e. constantly `false`.
-- In the ideal-`F_com` world that opening is refused whenever `s ≢ true`, so
-- the whole of the attack's advantage sits inside the commitment's own
-- extraction bound, and `Compose.composed-ε` says the composition carries that
-- bound UNRESCALED: `(q² + 2q)·2⁻ᵏ`, evaluated below at `k = q = 3`.
--
-- `bias-round` is the witness that the word the trace statement quantifies
-- over is inhabited by a live run — `Examples.HashForward.UC.sim-round`'s role
-- here, and the same chain.

open import Data.Bool.Base using (Bool; true)
open import Data.List.Base using (List; []; _∷_)
open import Data.Nat.Base using (ℕ)
open import Data.Product.Base using (_×_; _,_)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Unit.Base using (⊤; tt)
open import Data.Unit.Polymorphic.Base using () renaming (tt to ttᵛ)
open import Data.Empty using (⊥)
open import Data.Vec.Base using (Vec) renaming (_∷_ to _∷ᵛ_)
open import Function.Base using (case_of_)
open import Level using (0ℓ)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Data.Rational using (ℚ) renaming (_*_ to _*ℚ_)
open import ProbabilisticLogic.Distribution.Uniform using (fromℕ; inv-pow-2)
open import ProbabilisticLogic.Dp
open import ProbabilisticLogic.Dp.Reasoning

open import CategoricalCrypto.Iface
open import CategoricalCrypto.Machines.Base using (𝒱ₚ; 𝒫ₚ)
open import CategoricalCrypto.UC.Machine using (Proc)
open import CategoricalCrypto.UC.QueryBound using (behᵍ; traceᵍ)

import CategoricalCrypto.Machines.Core as Core
import CategoricalCrypto.Machines.Sim as Sim

module CategoricalCrypto.Examples.CoinToss.Test where

open import CategoricalCrypto.Examples.CoinToss 3
open import CategoricalCrypto.Examples.CoinToss.Compose using (composed-ε; εᶜᵗ)
open import CategoricalCrypto.Examples.ROCommitment 3
open import CategoricalCrypto.Examples.ROCommitment.Asymptotic using (εᶜ)
open import CategoricalCrypto.Examples.ROCommitment.Extraction 3 using (Dig; Pt)

open Core (𝒱ₚ 0ℓ)
open Sim (𝒱ₚ 0ℓ) (𝒫ₚ 0ℓ)

------------------------------------------------------------------------
-- The ceiling

-- `(3² + 2·3)·2⁻³`, and it is the COMMITMENT's schedule at the same allowance:
-- the coin-toss stage costs the test one activation and no more.
attack-bound : εᶜᵗ εᶜ 3 3 ≡ fromℕ 15 *ℚ inv-pow-2 3
attack-bound = composed-ε 3 3

------------------------------------------------------------------------
-- The attack

-- A corrupted committer has to be woken by something: it hears the
-- commitment's answers and the honest share on its own two ports and speaks
-- first, so its codomain carries exactly one letter and no answer.
Startᴵ : Iface
Startᴵ = ⊥ ⇿ ⊤

data BSt : Set where
  asleepᵇ : BSt
  askedᵇ  : BSt
  heldᵇ   : Dig → BSt
  doneᵇ   : BSt

module _ (r : Vec Bool 3) where

  biasStep : BSt × (Pos (Advᴵ ⊗ᴵ Advᴵᶜ) ⊎ Neg Startᴵ)
           → Dₚ (BSt × (Neg (Advᴵ ⊗ᴵ Advᴵᶜ) ⊎ Pos Startᴵ))
  biasStep (s , inj₂ tt)                     = case s of λ where
    asleepᵇ → returnₚ (askedᵇ , inj₁ (inj₁ (queryᴬ (true ∷ᵛ r))))
    _       → botₚ
  biasStep (s , inj₁ (inj₁ (ansᴬ d)))        = case s of λ where
    askedᵇ → returnₚ (heldᵇ d , inj₁ (inj₁ (commitᴬ d)))
    _      → botₚ
  biasStep (s , inj₁ (inj₂ (shareᴬ b₂)))     = case s of λ where
    (heldᵇ _) → returnₚ (doneᵇ , inj₁ (inj₁ (openᴬ b₂ r)))
    _         → botₚ

  stateᵇ : State
  stateᵇ = record { obj = BSt ; point = λ _ → returnₚ asleepᵇ ; discard = λ _ → returnₚ ttᵛ }

  bias : Proc (Advᴵ ⊗ᴵ Advᴵᶜ) Startᴵ
  bias = mk stateᵇ biasStep

  -- One live round: woken, it queries `true ∷ r`; answered `d`, it commits to
  -- `d`; told the share `b₂`, it opens at `b₂` — a bit it did not commit to
  -- unless `b₂ ≡ true`, which is exactly the extraction bound's bad event.
  round : Dig → Bool → List (Pos (Advᴵ ⊗ᴵ Advᴵᶜ) ⊎ Neg Startᴵ)
  round d b₂ = inj₂ tt ∷ inj₁ (inj₁ (ansᴬ d)) ∷ inj₁ (inj₂ (shareᴬ b₂)) ∷ []

  bias-round : (d : Dig) (b₂ : Bool)
             → behᵍ {Advᴵ ⊗ᴵ Advᴵᶜ} {Startᴵ} BSt (returnₚ asleepᵇ) biasStep (round d b₂)
               ≈ₚ returnₚ ( inj₁ (inj₁ (queryᴬ (true ∷ᵛ r)))
                          ∷ inj₁ (inj₁ (commitᴬ d))
                          ∷ inj₁ (inj₁ (openᴬ b₂ r)) ∷ [] )
  bias-round d b₂ =
      >>=ₚ-identityˡ asleepᵇ _
    ⟨≈⟩ >>=ₚ-identityˡ (askedᵇ , inj₁ (inj₁ (queryᴬ (true ∷ᵛ r)))) _
    ⟨≈⟩ map-arg _ afterAns
    ⟨≈⟩ >>=ₚ-identityˡ _ _
    where
    afterOpen : traceᵍ {Advᴵ ⊗ᴵ Advᴵᶜ} {Startᴵ} BSt (returnₚ asleepᵇ) biasStep (heldᵇ d)
                  (inj₁ (inj₂ (shareᴬ b₂)) ∷ [])
                ≈ₚ returnₚ (inj₁ (inj₁ (openᴬ b₂ r)) ∷ [])
    afterOpen = >>=ₚ-identityˡ (doneᵇ , inj₁ (inj₁ (openᴬ b₂ r))) _
              ⟨≈⟩ >>=ₚ-identityˡ [] _

    afterAns : traceᵍ {Advᴵ ⊗ᴵ Advᴵᶜ} {Startᴵ} BSt (returnₚ asleepᵇ) biasStep askedᵇ
                 (inj₁ (inj₁ (ansᴬ d)) ∷ inj₁ (inj₂ (shareᴬ b₂)) ∷ [])
               ≈ₚ returnₚ (inj₁ (inj₁ (commitᴬ d)) ∷ inj₁ (inj₁ (openᴬ b₂ r)) ∷ [])
    afterAns = >>=ₚ-identityˡ (heldᵇ d , inj₁ (inj₁ (commitᴬ d))) _
             ⟨≈⟩ map-arg _ afterOpen ⟨≈⟩ >>=ₚ-identityˡ _ _
