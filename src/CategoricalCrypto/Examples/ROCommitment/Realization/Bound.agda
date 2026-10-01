{-# OPTIONS --safe --without-K --guardedness #-}

-- The closed real machine's verdict mass, and the game bound it inherits.
--
-- `real-run` is the machine half, `game-bound⊥` the game half at the pruned
-- kernels (`hop-boundᵇ⊥`, because pruning the coupling and pruning its
-- marginal are only `E⊥`-equal), `extraction-real` the two composed: the
-- extraction game's bound for the closed real machine.  The ideal
-- side stays a GAME: the machine leg is blocked by `Realization.Bisim`'s
-- `extract-relog`.

open import Data.Bool.Base
open import Data.List.Base
open import Data.Maybe.Base
open import Data.Nat.Base
open import Data.Product.Base
open import Data.Rational using (ℚ) renaming (_-_ to _-ℚ_; ∣_∣ to ∣_∣ℚ; _≤_ to _≤ℚ_)
open import Data.Rational.Properties
open import Data.Unit.Polymorphic.Base
open import Relation.Binary.PropositionalEquality

open import Categories.Category

open import ProbabilisticLogic.Distribution.RationalDist
open import ProbabilisticLogic.Distribution.RationalDist.Expectation
open import ProbabilisticLogic.Distribution.RationalDist.Partial
open import ProbabilisticLogic.Distribution.Uniform
open import ProbabilisticLogic.Dp
open import ProbabilisticLogic.Dp.Settle

open import CategoricalCrypto.GamePlaying
open import CategoricalCrypto.GamePlaying.Hop
open import CategoricalCrypto.GamePlaying.Partial
open import CategoricalCrypto.Iface
open import CategoricalCrypto.Interaction
open import CategoricalCrypto.Protocol.Machine
open import CategoricalCrypto.Protocol.Machine.Trace.Compose
open import CategoricalCrypto.Strategy
open import CategoricalCrypto.UC.Machine

import CategoricalCrypto.Machines.Collapse as Col
import CategoricalCrypto.Machines.Pointwise as Pw

module CategoricalCrypto.Examples.ROCommitment.Realization.Bound (k : ℕ) where

open import CategoricalCrypto.Examples.ROCommitment k
open import CategoricalCrypto.Examples.ROCommitment.Game k
open import CategoricalCrypto.Examples.ROCommitment.Realization.Bisim k
open import CategoricalCrypto.Examples.ROCommitment.Realization.Machine k
open import CategoricalCrypto.Examples.ROCommitment.Resource k

private module 𝒫 = Category 𝒫ᴵ

------------------------------------------------------------------------
-- The machine half

private
  m₀ : RSt × RState
  m₀ = waitᴿ nothing , [] , nothing

  σ₀ᴿ : Dist⊥ (RSt × RState)
  σ₀ᴿ = return⊥ m₀

  pointᴿ : Σ[ i ∈ ℕ ] Settles i (Pw.MC.point (Col.Sᴳ real resource) tt) σ₀ᴿ
  pointᴿ = Settles-ret⋆ (tt , tt) _ σ₀ᴿ
             (Settles-ret⋆ (waitᴿ nothing) _ σ₀ᴿ
               (Settles-ret⋆ ([] , nothing) _ σ₀ᴿ (1 , Settles-return m₀)))

  -- The machine half's three steps are named separately: inferring them inside
  -- one `where` forces the composite's step to normalize.
  composeᴿ : (d : Strat (Neg (Advᴵ ⊗ᴵ Honᴵ)) (Pos (Advᴵ ⊗ᴵ Honᴵ)))
           → Σ[ n ∈ ℕ ] ((i : ℕ)
               → cum (n + i) (runᴹ (𝒫._∘_ real resource) d)
                             (indᵇ true)
               ≡ E⊥ (σ₀ᴿ >>=⊥ λ m → runWith⊥ Kᴿ m d) (indᵇ true))
  composeᴿ = compose-pr real resource Kʳ Kᵒ real-settles res-settles rankᴿ rankedᴿ 2 boundᴿ
                        σ₀ᴿ (proj₁ pointᴿ) (proj₂ pointᴿ) true

  collapseᴿ : (d : Strat (Neg (Advᴵ ⊗ᴵ Honᴵ)) (Pos (Advᴵ ⊗ᴵ Honᴵ)))
            → E⊥ (σ₀ᴿ >>=⊥ λ m → runWith⊥ Kᴿ m d) (indᵇ true) ≡ Pr₁⊥ (runWith⊥ Kᴿ m₀ d)
  collapseᴿ d = >>=⊥-identityˡ m₀ (λ m → runWith⊥ Kᴿ m d) (maybeℚ (indᵇ true))

  gameᴿ : (d : Strat (Neg (Advᴵ ⊗ᴵ Honᴵ)) (Pos (Advᴵ ⊗ᴵ Honᴵ)))
        → Pr₁⊥ (runWith⊥ Kᴿ m₀ d) ≡ Pr₁⊥ (runWith⊥ respR⊥ sR₀ (mapStrat toQ fromR d))
  gameᴿ d = runWith⊥-bisimʳ toQ fromR Kᴿ respR⊥ _≋ᴿ_ bisimᴿ d m₀ sR₀ refl (indᵇ true)

real-run : (d : Strat (Neg (Advᴵ ⊗ᴵ Honᴵ)) (Pos (Advᴵ ⊗ᴵ Honᴵ)))
         → Σ[ n ∈ ℕ ] ((i : ℕ)
             → cum (n + i) (runᴹ (𝒫._∘_ real resource) d)
                           (indᵇ true)
             ≡ Pr₁⊥ (runWith⊥ respR⊥ sR₀ (mapStrat toQ fromR d)))
real-run d = proj₁ (composeᴿ d)
           , λ i → trans (proj₂ (composeᴿ d) i) (trans (collapseᴿ d) (gameᴿ d))

------------------------------------------------------------------------
-- The game half, at the same pruned activations

-- The coupling and the ideal game inherit the real game's dead set through
-- the two erasures, so the three `prune`s cut at the same places.
deadB : St → Q → Bool
deadB s = deadR (eraseR s)

deadI : StI → Q → Bool
deadI s = deadR (proj₁ s , digOf (proj₂ s))

respB⊥ : St → Q → Dist⊥ (St × (R × R))
respB⊥ = prune deadB respB

respI⊥ : StI → Q → Dist⊥ (StI × R)
respI⊥ = prune deadI respI

private
  module Cb = Coupling⊥ bad respB⊥

game-bound⊥ : (m : ℕ) (d : Strat Q R) → asks≤ m d
            → ∣ Pr₁⊥ (runWith⊥ respI⊥ sI₀ d) -ℚ Pr₁⊥ (runWith⊥ respR⊥ sR₀ d) ∣ℚ ≤ℚ ε m
game-bound⊥ =
  hop-boundᵇ⊥ bad respB⊥ respR⊥ respI⊥ s₀ sR₀ sI₀
    (λ d → runWith⊥-bisim Cb.realK respR⊥ _≋R_
             (λ s s′ r q F F′ pt → trans (prune-Dmap deadB respB C.fR s q F)
               (prune-bisim C.realK respR _≋R_ deadB deadR (λ { _ _ (refl , _) _ → refl }) stepR
                            s s′ r q F F′ pt))
             d s₀ sR₀ (refl , inv₀) (indᵇ true))
    (λ d → runWith⊥-bisim Cb.idealK respI⊥ _≋I_
             (λ s s′ r q F F′ pt → trans (prune-Dmap deadB respB C.fI s q F)
               (prune-bisim C.idealK respI _≋I_ deadB deadI (λ { _ _ (refl , _) _ → refl }) stepI
                            s s′ r q F F′ pt))
             d s₀ sI₀ (refl , inv₀) (indᵇ true))
    λ m d le → ≤-trans (≤-reflexive (badProb⊥-cong Cb.realK (prune deadB C.realK)
                                                   bad (prune-Dmap deadB respB C.fR) s₀ d))
                       (badProb⊥-bounded (prune-cert deadB cert) m d le)

------------------------------------------------------------------------
-- …and the two composed

-- Rewriting UNDER `∣_-_∣` is done at an abstract equation and nowhere else:
-- with the run's own reading substituted in, Agda unfolds the subtraction
-- into the entry list it is a fold over.
private
  transferᴿ : (m : ℕ) (d : Strat (Neg (Advᴵ ⊗ᴵ Honᴵ)) (Pos (Advᴵ ⊗ᴵ Honᴵ))) (n i : ℕ)
            → cum (n + i) (runᴹ (𝒫._∘_ real resource) d)
                          (indᵇ true)
              ≡ Pr₁⊥ (runWith⊥ respR⊥ sR₀ (mapStrat toQ fromR d))
            → asks≤ m d
            → ∣ Pr₁⊥ (runWith⊥ respI⊥ sI₀ (mapStrat toQ fromR d))
              -ℚ cum (n + i) (runᴹ (𝒫._∘_ real resource) d)
                             (indᵇ true) ∣ℚ
              ≤ℚ ε m
  transferᴿ m d n i eq le =
    ≤-trans (≤-reflexive (cong (λ z → ∣ Pr₁⊥ (runWith⊥ respI⊥ sI₀ (mapStrat toQ fromR d))
                                      -ℚ z ∣ℚ) eq))
            (game-bound⊥ m (mapStrat toQ fromR d) (asks≤-mapStrat toQ fromR d le))

extraction-real : (m : ℕ) (d : Strat (Neg (Advᴵ ⊗ᴵ Honᴵ)) (Pos (Advᴵ ⊗ᴵ Honᴵ))) → asks≤ m d
             → Σ[ n ∈ ℕ ] ((i : ℕ)
                 → ∣ Pr₁⊥ (runWith⊥ respI⊥ sI₀ (mapStrat toQ fromR d))
                   -ℚ cum (n + i) (runᴹ (𝒫._∘_ real resource) d)
                                  (indᵇ true) ∣ℚ
                   ≤ℚ ε m)
extraction-real m d le =
  proj₁ (real-run d)
  , λ i → transferᴿ m d (proj₁ (real-run d)) i (proj₂ (real-run d) i) le
