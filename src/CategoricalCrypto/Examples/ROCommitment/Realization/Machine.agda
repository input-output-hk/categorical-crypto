{-# OPTIONS --safe --without-K --guardedness #-}

-- The closed real commitment system `real 𝒫.∘ resource` as a kernel: it
-- settles, so its `Dₚ` run is a run of a `Dist⊥` kernel
-- (`Protocol.Machine.Trace.Compose`).
--
-- The composite's loop needs a rank: 1 on a resource query and 0 on an
-- answer, because the receiver never answers the resource with a further
-- query (`real-up`).  The resource's own activations never need inspecting:
-- whatever it answers is an exit or a loop point of rank 0.

open import Class.DecEq

open import Data.Empty
open import Data.List.Base
open import Data.Maybe.Base
open import Data.Nat.Base
open import Data.Product.Base
open import Data.Sum.Base
open import Data.Unit.Base
open import Data.Vec.Base using () renaming (_∷_ to _∷ᵛ_)
open import Function.Base
open import Level using (0ℓ)
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary.Decidable.Core

open import ProbabilisticLogic.Distribution.RationalDist
open import ProbabilisticLogic.Distribution.RationalDist.Partial
open import ProbabilisticLogic.Dp
open import ProbabilisticLogic.Dp.Settle

open import CategoricalCrypto.Iface
open import CategoricalCrypto.Machines.Base
open import CategoricalCrypto.Protocol.Machine.Raw
open import CategoricalCrypto.Protocol.Machine.Trace.Compose

import CategoricalCrypto.Machines.Collapse as Col
import CategoricalCrypto.Machines.Core as Core

module CategoricalCrypto.Examples.ROCommitment.Realization.Machine (k : ℕ) where

open import CategoricalCrypto.Examples.ROCommitment k
open import CategoricalCrypto.Examples.ROCommitment.Resource k
open import CategoricalCrypto.Examples.ROCommitment.Transport k

open Core (𝒱ₚ 0ℓ)

------------------------------------------------------------------------
-- The honest receiver's kernel

Kʳ : RSt → Pos Resᴵ ⊎ Neg (Advᴵ ⊗ᴵ Honᴵ)
   → Dist⊥ (RSt × (Neg Resᴵ ⊎ Pos (Advᴵ ⊗ᴵ Honᴵ)))
Kʳ s y = return-ℚ (realStepᵈ (s , y))

real-settles : (m : RSt) (y : Pos Resᴵ ⊎ Neg (Advᴵ ⊗ᴵ Honᴵ))
             → Σ[ i ∈ ℕ ] Settles i (step real (m , y)) (Kʳ m y)
real-settles m y = Settles-det (realStepᵈ (m , y))

real-up : (Φ : RSt × (Neg Resᴵ ⊎ Pos (Advᴵ ⊗ᴵ Honᴵ)) → Set)
        → ((s : RSt) (c : Pos (Advᴵ ⊗ᴵ Honᴵ)) → Φ (s , inj₂ c))
        → (s : RSt) (z : Pos Resᴵ) (i : ℕ) → Supp i (step real (s , inj₁ z)) Φ
real-up Φ h (waitᴿ _)    (digᴿ _) = Supp-bot Φ
real-up Φ h (relayᴿ _)   (digᴿ _) = Supp-return Φ _ (h _ _)
real-up Φ h (checkᴿ _ _) (digᴿ _) = Supp-return Φ _ (h _ _)
real-up Φ h _ rcptᴿ    = Supp-bot Φ
real-up Φ h _ (outᴿ _) = Supp-bot Φ
real-up Φ h _ rejᴿ     = Supp-bot Φ

------------------------------------------------------------------------
-- The resource's kernel, at the closed factor's alphabet

Kᵒ : RState → ⊥ ⊎ Neg Resᴵ → Dist⊥ (RState × (⊥ ⊎ Pos Resᴵ))
Kᵒ s (inj₂ q) = Dmap⊥ ansᴹ (resK s q)

res-settles : (m : RState) (z : ⊥ ⊎ Neg Resᴵ)
            → Σ[ i ∈ ℕ ] Settles i (step resource (m , z)) (Kᵒ m z)
res-settles m (inj₂ q) = resource-settles m q

------------------------------------------------------------------------
-- The round-trip bound at `real 𝒫.∘ resource`

rankᴿ : (RSt × RState) × (Neg Resᴵ ⊎ Pos Resᴵ) → ℕ
rankᴿ (_ , inj₁ _) = 1
rankᴿ (_ , inj₂ _) = 0

private
  Dropsᴿ : ℕ → (RSt × RState) × ((⊥ ⊎ Pos (Advᴵ ⊗ᴵ Honᴵ)) ⊎ (Neg Resᴵ ⊎ Pos Resᴵ)) → Set
  Dropsᴿ = Lp.Drops real resource Kʳ Kᵒ real-settles res-settles rankᴿ

  dispatchᴿ : (w : (RSt × RState) × (Neg Resᴵ ⊎ Pos Resᴵ)) (i : ℕ)
            → Supp i (Col.kᴳ real resource (proj₁ w , inj₂ (proj₂ w))) (Dropsᴿ (rankᴿ w))
  dispatchᴿ ((sg , sf) , inj₁ q) i =
    Supp-bind (Dropsᴿ 1) i _ _ (Supp-all _ (λ where (_ , inj₂ _) → Supp-return _ _ (s≤s z≤n)) i _)
  dispatchᴿ ((sg , sf) , inj₂ a) i =
    Supp-bind (Dropsᴿ 0) i _ _ (real-up _ (λ _ _ → Supp-return _ _ tt) sg a i)

rankedᴿ : Lp.Ranked real resource Kʳ Kᵒ real-settles res-settles rankᴿ
rankedᴿ = ranked-from-kᴳ real resource Kʳ Kᵒ real-settles res-settles rankᴿ dispatchᴿ

boundᴿ : (w : (RSt × RState) × (Neg Resᴵ ⊎ Pos Resᴵ)) → rankᴿ w < 2
boundᴿ (_ , inj₁ _) = s≤s (s≤s z≤n)
boundᴿ (_ , inj₂ _) = s≤s z≤n

Kᴿ : RSt × RState → Neg (Advᴵ ⊗ᴵ Honᴵ)
   → Dist⊥ ((RSt × RState) × Pos (Advᴵ ⊗ᴵ Honᴵ))
Kᴿ = Kᶜˡ real resource Kʳ Kᵒ real-settles res-settles rankᴿ rankedᴿ 2 boundᴿ
