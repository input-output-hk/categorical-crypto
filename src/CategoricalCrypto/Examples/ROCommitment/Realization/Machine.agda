{-# OPTIONS --safe --without-K --guardedness #-}

-- The real commitment system over the concrete resource, as a kernel: the
-- closed composite `real 𝒫.∘ resource` settles, so its `Dₚ` run is the run of
-- a `Dist⊥` kernel (`Protocol.Machine.Trace.Compose`).
--
-- The rank the loop needs is two-valued here and reads off `realStep`: a
-- resource query still owes its answer (1), an answer owes nothing (0),
-- because every clause of `realStep` on a `Pos Resᴵ` letter either emits
-- upward or diverges (`real-up`).  The resource's own activations are all
-- exits or loop points of smaller rank, so its side needs no inspection.

open import Class.DecEq

open import Data.Bool.Base using (Bool)
open import Data.Empty using (⊥)
open import Data.Maybe.Base using (just; nothing)
open import Data.Nat.Base using (ℕ; s≤s; z≤n; _+_; _<_)
open import Data.Product.Base using (Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Unit.Base using (⊤; tt)
open import Data.Vec.Base using () renaming (_∷_ to _∷ᵛ_)
open import Function.Base using (case_of_)
open import Level using (0ℓ)
open import Relation.Nullary.Decidable.Core using (⌊_⌋)

open import ProbabilisticLogic.Distribution.RationalDist
open import ProbabilisticLogic.Distribution.RationalDist.Partial
open import ProbabilisticLogic.Dp
open import ProbabilisticLogic.Dp.Settle
open import ProbabilisticLogic.Dp.Support

open import CategoricalCrypto.Iface
open import CategoricalCrypto.Machines.Base using (𝒱ₚ)
open import CategoricalCrypto.Protocol.Machine.Raw using (ansᴹ)
open import CategoricalCrypto.Protocol.Machine.Trace.Compose
open import CategoricalCrypto.UC.Machine using (Proc)

import CategoricalCrypto.Machines.Collapse as Col
import CategoricalCrypto.Machines.Core as Core

module CategoricalCrypto.Examples.ROCommitment.Realization.Machine (k : ℕ) where

open import CategoricalCrypto.Examples.ROCommitment k
open import CategoricalCrypto.Examples.ROCommitment.Extraction k
open import CategoricalCrypto.Examples.ROCommitment.Resource k
open import CategoricalCrypto.Examples.ROCommitment.Transport k using (resK; resource-settles)

open Core (𝒱ₚ 0ℓ)

------------------------------------------------------------------------
-- The honest receiver's kernel

-- `realStep` with its `returnₚ`s read as point masses and its `botₚ`s as the
-- sink; the clause structure is `realStep`'s, so both sides reduce together.
Kʳ : RSt → Pos Resᴵ ⊎ Neg (Advᴵ ⊗ᴵ Honᴵ)
   → Dist⊥ (RSt × (Neg Resᴵ ⊎ Pos (Advᴵ ⊗ᴵ Honᴵ)))
Kʳ s (inj₁ (digᴿ d))           = case s of λ where
  (relayᴿ m)   → return⊥ (waitᴿ m        , inj₂ (inj₁ (ansᴬ d)))
  (checkᴿ c b) → return⊥ (waitᴿ (just c) , inj₂ (inj₂ (verdict b ⌊ d ≟ c ⌋)))
  (waitᴿ _)    → return-ℚ nothing
Kʳ s (inj₁ rcptᴿ)              = return-ℚ nothing
Kʳ s (inj₁ (outᴿ _))           = return-ℚ nothing
Kʳ s (inj₁ rejᴿ)               = return-ℚ nothing
Kʳ s (inj₂ (inj₁ (queryᴬ x)))  = case s of λ where
  (waitᴿ m) → return⊥ (relayᴿ m , inj₁ (hashᴿ x))
  _         → return-ℚ nothing
Kʳ s (inj₂ (inj₁ (commitᴬ c))) = case s of λ where
  (waitᴿ nothing) → return⊥ (waitᴿ (just c) , inj₂ (inj₂ rcptᴴ))
  _               → return-ℚ nothing
Kʳ s (inj₂ (inj₁ (openᴬ b r))) = case s of λ where
  (waitᴿ (just c)) → return⊥ (checkᴿ c b , inj₁ (hashᴿ (b ∷ᵛ r)))
  _                → return-ℚ nothing
Kʳ s (inj₂ (inj₂ ()))

real-settles : (m : RSt) (y : Pos Resᴵ ⊎ Neg (Advᴵ ⊗ᴵ Honᴵ))
             → Σ[ i ∈ ℕ ] Settles i (step real (m , y)) (Kʳ m y)
real-settles (waitᴿ _)    (inj₁ (digᴿ _)) = 0 , Settles-bot
real-settles (relayᴿ _)   (inj₁ (digᴿ _)) = 1 , Settles-return _
real-settles (checkᴿ _ _) (inj₁ (digᴿ _)) = 1 , Settles-return _
real-settles _ (inj₁ rcptᴿ)    = 0 , Settles-bot
real-settles _ (inj₁ (outᴿ _)) = 0 , Settles-bot
real-settles _ (inj₁ rejᴿ)     = 0 , Settles-bot
real-settles (waitᴿ _)    (inj₂ (inj₁ (queryᴬ _))) = 1 , Settles-return _
real-settles (relayᴿ _)   (inj₂ (inj₁ (queryᴬ _))) = 0 , Settles-bot
real-settles (checkᴿ _ _) (inj₂ (inj₁ (queryᴬ _))) = 0 , Settles-bot
real-settles (waitᴿ nothing)  (inj₂ (inj₁ (commitᴬ _))) = 1 , Settles-return _
real-settles (waitᴿ (just _)) (inj₂ (inj₁ (commitᴬ _))) = 0 , Settles-bot
real-settles (relayᴿ _)       (inj₂ (inj₁ (commitᴬ _))) = 0 , Settles-bot
real-settles (checkᴿ _ _)     (inj₂ (inj₁ (commitᴬ _))) = 0 , Settles-bot
real-settles (waitᴿ (just _)) (inj₂ (inj₁ (openᴬ _ _))) = 1 , Settles-return _
real-settles (waitᴿ nothing)  (inj₂ (inj₁ (openᴬ _ _))) = 0 , Settles-bot
real-settles (relayᴿ _)       (inj₂ (inj₁ (openᴬ _ _))) = 0 , Settles-bot
real-settles (checkᴿ _ _)     (inj₂ (inj₁ (openᴬ _ _))) = 0 , Settles-bot
real-settles _ (inj₂ (inj₂ ()))

-- The receiver never answers the resource with another query: every clause of
-- `realStep` on a `Pos Resᴵ` letter emits upward or diverges.  This is the
-- whole content of the composite's rank.
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

  -- A resource answer is a loop point of rank 0; the receiver's reaction to it
  -- leaves the loop.
  dispatchᴿ : (w : (RSt × RState) × (Neg Resᴵ ⊎ Pos Resᴵ)) (i : ℕ)
            → Supp i (Col.kᴳ real resource (proj₁ w , inj₂ (proj₂ w))) (Dropsᴿ (rankᴿ w))
  dispatchᴿ ((sg , sf) , inj₁ q) i =
    Supp-bind (Dropsᴿ 1) i _ _ (Supp-all _ (λ where (_ , inj₂ _) → Supp-return _ _ (s≤s z≤n)) i _)
  dispatchᴿ ((sg , sf) , inj₂ a) i =
    Supp-bind (Dropsᴿ 0) i _ _ (real-up _ (λ _ _ → Supp-return _ _ tt) sg a i)

rankedᴿ : Lp.Ranked real resource Kʳ Kᵒ real-settles res-settles rankᴿ
rankedᴿ = ranked-from-kᴳ real resource Kʳ Kᵒ real-settles res-settles rankᴿ dispatchᴿ

fuelᴿ : ℕ
fuelᴿ = 2

boundᴿ : (w : (RSt × RState) × (Neg Resᴵ ⊎ Pos Resᴵ)) → rankᴿ w < fuelᴿ
boundᴿ (_ , inj₁ _) = s≤s (s≤s z≤n)
boundᴿ (_ , inj₂ _) = s≤s z≤n

-- The closed real system's kernel: one activation of the corrupted committer,
-- served to completion through the oracle.
Kᴿ : RSt × RState → Neg (Advᴵ ⊗ᴵ Honᴵ)
   → Dist⊥ ((RSt × RState) × Pos (Advᴵ ⊗ᴵ Honᴵ))
Kᴿ = Kᶜˡ real resource Kʳ Kᵒ real-settles res-settles rankᴿ rankedᴿ fuelᴿ boundᴿ
