{-# OPTIONS --safe --without-K --guardedness #-}

-- The closed real system's verdict mass, and the game bound it inherits.
--
-- `real-run` is the machine half: the `Dₚ` run of `real 𝒫.∘ resource` reaches
-- exactly the `Dist⊥` run of the pruned real game, past a budget of its own.
-- `game-bound⊥` is the game half at the same pruned kernels — `Game.cert`
-- through `prune-cert`, and `hop-boundᵇ⊥` because pruning the COUPLING and
-- pruning its marginal are only `E⊥`-equal.  `binding-real` is the two
-- composed.
--
-- The ideal machine leg of `docs/rcom-icom-b1.md`'s B2-M4 is NOT here; the
-- obstruction is `Realization.Bisim`'s `extract-relog`, and until it is
-- resolved the ideal side of this bound stays a GAME.

open import Data.Bool.Base using (Bool; false; true)
open import Data.List.Base using ([]; _∷_)
open import Data.Maybe.Base using (just; nothing)
open import Data.Nat.Base using (ℕ; _+_)
open import Data.Product.Base using (Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Rational using (ℚ) renaming (_-_ to _-ℚ_; ∣_∣ to ∣_∣ℚ; _≤_ to _≤ℚ_)
open import Data.Rational.Properties using (≤-reflexive; ≤-trans)
open import Data.Unit.Polymorphic.Base using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; cong; refl; sym; trans)

open import Categories.Category using (Category)

open import ProbabilisticLogic.Distribution.RationalDist
open import ProbabilisticLogic.Distribution.RationalDist.Expectation
open import ProbabilisticLogic.Distribution.RationalDist.Partial
open import ProbabilisticLogic.Distribution.Uniform using (indᵇ)
open import ProbabilisticLogic.Dp
open import ProbabilisticLogic.Dp.Settle

open import CategoricalCrypto.GamePlaying.Partial
  using (StepBisim⊥; badProb⊥-bounded; badProb⊥-cong; hop-boundᵇ⊥; prune; prune-cert;
         runWith⊥-bisim; runWith⊥-bisimʳ; module Coupling⊥)
open import CategoricalCrypto.Iface
open import CategoricalCrypto.Interaction using (runWith⊥)
open import CategoricalCrypto.Protocol.Machine using (runᴹ)
open import CategoricalCrypto.Protocol.Machine.Trace.Compose
open import CategoricalCrypto.Strategy using (Strat; asks≤; asks≤-mapStrat; mapStrat)
open import CategoricalCrypto.UC.Machine using (𝒫ᴵ)

import CategoricalCrypto.Machines.Collapse as Col

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

  -- Both factors start with a point mass, and the pairing is three `returnₚ`s.
  pointᴿ : Σ[ i ∈ ℕ ] Settles i (Col.MC.point (Col.Sᴳ real resource) tt) σ₀ᴿ
  pointᴿ = Settles-ret⋆ (tt , tt) _ σ₀ᴿ
             (Settles-ret⋆ (waitᴿ nothing) _ σ₀ᴿ
               (Settles-ret⋆ ([] , nothing) _ σ₀ᴿ (1 , Settles-return m₀)))

  -- The three steps the machine half is: the transport, the initial-state
  -- junction, and the relabelled coupling.  Named, because inferring them
  -- inside one `where` forces the composite's step to normalize.
  composeᴿ : (d : Strat (Neg (Advᴵ ⊗ᴵ Honᴵ)) (Pos (Advᴵ ⊗ᴵ Honᴵ)))
           → Σ[ n ∈ ℕ ] ((i : ℕ)
               → cum (n + i) (runᴹ (𝒫._∘_ {unitᴵ} {Resᴵ} {Advᴵ ⊗ᴵ Honᴵ} real resource) d)
                             (indᵇ true)
               ≡ E⊥ (σ₀ᴿ >>=⊥ λ m → runWith⊥ Kᴿ m d) (indᵇ true))
  composeᴿ = compose-pr real resource Kʳ Kᵒ real-settles res-settles rankᴿ rankedᴿ 2 boundᴿ
                        σ₀ᴿ (proj₁ pointᴿ) (proj₂ pointᴿ) true

  collapseᴿ : (d : Strat (Neg (Advᴵ ⊗ᴵ Honᴵ)) (Pos (Advᴵ ⊗ᴵ Honᴵ)))
            → E⊥ (σ₀ᴿ >>=⊥ λ m → runWith⊥ Kᴿ m d) (indᵇ true) ≡ Pr₁⊥ (runWith⊥ Kᴿ m₀ d)
  collapseᴿ d = trans (E⊥-bind σ₀ᴿ (λ m → runWith⊥ Kᴿ m d) (indᵇ true))
                      (E⊥-return m₀ λ m → E⊥ (runWith⊥ Kᴿ m d) (indᵇ true))

  gameᴿ : (d : Strat (Neg (Advᴵ ⊗ᴵ Honᴵ)) (Pos (Advᴵ ⊗ᴵ Honᴵ)))
        → Pr₁⊥ (runWith⊥ Kᴿ m₀ d) ≡ Pr₁⊥ (runWith⊥ respR⊥ sR₀ (mapStrat toQ fromR d))
  gameᴿ d = runWith⊥-bisimʳ toQ fromR Kᴿ respR⊥ _≋ᴿ_ bisimᴿ d m₀ sR₀ refl

-- The closed real machine's `true`-mass IS the pruned real game's.
real-run : (d : Strat (Neg (Advᴵ ⊗ᴵ Honᴵ)) (Pos (Advᴵ ⊗ᴵ Honᴵ)))
         → Σ[ n ∈ ℕ ] ((i : ℕ)
             → cum (n + i) (runᴹ (𝒫._∘_ {unitᴵ} {Resᴵ} {Advᴵ ⊗ᴵ Honᴵ} real resource) d)
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

  -- A marginal of the pruned coupling, against the pruned marginal: the two
  -- differ by `Dmap` commuting past the cut, which `E⊥` does not see.
  marginalᴿ : (s : St) (q : Q) (G : St × R → ℚ)
            → E⊥ (Cb.realK s q) G ≡ E⊥ (prune deadB C.realK s q) G
  marginalᴿ s@(t , m , f) q G with deadR (t , digOf m) q
  ... | true  = trans (E⊥-map C.fR (return-ℚ nothing) G)
                      (trans (lookupᴰℚ-return nothing (maybeℚ λ w → G (C.fR w)))
                             (sym (lookupᴰℚ-return nothing (maybeℚ G))))
  ... | false = trans (E⊥-map C.fR (Dmap just (respB s q)) G)
                (trans (Eⱼ (respB s q) (λ w → G (C.fR w)))
                (trans (sym (lookupᴰℚ-Dmap C.fR (respB s q) G))
                       (sym (Eⱼ (C.realK s q) G))))

  -- `Game.stepR`/`stepI` at the pruned kernels: off the cut both sides are
  -- the embedded totals, and on it both score nothing.
  bisimᴿᵍ : StepBisim⊥ Cb.realK respR⊥ _≋R_
  bisimᴿᵍ s@(t , m , f) _ (refl , inv) q F F′ pt with deadR (t , digOf m) q
  ... | true  = trans (E⊥-map C.fR (return-ℚ nothing) F)
                      (trans (lookupᴰℚ-return nothing (maybeℚ λ w → F (C.fR w)))
                             (sym (lookupᴰℚ-return nothing (maybeℚ F′))))
  ... | false = trans (E⊥-map C.fR (Dmap just (respB s q)) F)
                (trans (Eⱼ (respB s q) (λ w → F (C.fR w)))
                (trans (sym (lookupᴰℚ-Dmap C.fR (respB s q) F))
                (trans (stepR s (eraseR s) (refl , inv) q F F′ pt)
                       (sym (Eⱼ (respR (eraseR s) q) F′)))))

  bisimᴵᵍ : StepBisim⊥ Cb.idealK respI⊥ _≋I_
  bisimᴵᵍ s@(t , m , f) _ (refl , inv) q F F′ pt with deadR (t , digOf m) q
  ... | true  = trans (E⊥-map C.fI (return-ℚ nothing) F)
                      (trans (lookupᴰℚ-return nothing (maybeℚ λ w → F (C.fI w)))
                             (sym (lookupᴰℚ-return nothing (maybeℚ F′))))
  ... | false = trans (E⊥-map C.fI (Dmap just (respB s q)) F)
                (trans (Eⱼ (respB s q) (λ w → F (C.fI w)))
                (trans (sym (lookupᴰℚ-Dmap C.fI (respB s q) F))
                (trans (stepI s (eraseI s) (refl , inv) q F F′ pt)
                       (sym (Eⱼ (respI (eraseI s) q) F′)))))

game-bound⊥ : (m : ℕ) (d : Strat Q R) → asks≤ m d
            → ∣ Pr₁⊥ (runWith⊥ respI⊥ sI₀ d) -ℚ Pr₁⊥ (runWith⊥ respR⊥ sR₀ d) ∣ℚ ≤ℚ ε m
game-bound⊥ =
  hop-boundᵇ⊥ bad respB⊥ respR⊥ respI⊥ s₀ sR₀ sI₀
    (λ d → runWith⊥-bisim Cb.realK respR⊥ _≋R_ bisimᴿᵍ d s₀ sR₀ (refl , inv₀))
    (λ d → runWith⊥-bisim Cb.idealK respI⊥ _≋I_ bisimᴵᵍ d s₀ sI₀ (refl , inv₀))
    λ m d le → ≤-trans (≤-reflexive (badProb⊥-cong Cb.realK (prune deadB C.realK)
                                                   bad marginalᴿ s₀ d))
                       (badProb⊥-bounded (prune-cert deadB cert) m d le)

------------------------------------------------------------------------
-- …and the two composed

-- At every distinguisher of at most `m` activations, the closed real MACHINE
-- differs from the pruned ideal GAME by at most `Game.ε m = (m² + 2m)·2⁻ᵏ`.
-- No premise here restates the emulation: the machine side is
-- `Protocol.Machine.Trace.Compose`'s transport at the concrete resource, the
-- game side is `Game.cert`, and the relabelling is a checked bijection.
------------------------------------------------------------------------
-- …and the two composed

-- Rewriting UNDER `∣_-_∣` is done at an abstract equation and nowhere else:
-- with the run's own reading substituted in, Agda unfolds the subtraction
-- into the entry list it is a fold over.
private
  transferᴿ : (m : ℕ) (d : Strat (Neg (Advᴵ ⊗ᴵ Honᴵ)) (Pos (Advᴵ ⊗ᴵ Honᴵ))) (n i : ℕ)
            → cum (n + i) (runᴹ (𝒫._∘_ {unitᴵ} {Resᴵ} {Advᴵ ⊗ᴵ Honᴵ} real resource) d)
                          (indᵇ true)
              ≡ Pr₁⊥ (runWith⊥ respR⊥ sR₀ (mapStrat toQ fromR d))
            → asks≤ m d
            → ∣ Pr₁⊥ (runWith⊥ respI⊥ sI₀ (mapStrat toQ fromR d))
              -ℚ cum (n + i) (runᴹ (𝒫._∘_ {unitᴵ} {Resᴵ} {Advᴵ ⊗ᴵ Honᴵ} real resource) d)
                             (indᵇ true) ∣ℚ
              ≤ℚ ε m
  transferᴿ m d n i eq le =
    ≤-trans (≤-reflexive (cong (λ z → ∣ Pr₁⊥ (runWith⊥ respI⊥ sI₀ (mapStrat toQ fromR d))
                                      -ℚ z ∣ℚ) eq))
            (game-bound⊥ m (mapStrat toQ fromR d) (asks≤-mapStrat toQ fromR d le))

-- At every distinguisher of at most `m` activations, the closed real MACHINE
-- differs from the pruned ideal GAME by at most `Game.ε m`.  No premise here
-- restates the emulation: the machine side is `Trace.Compose`'s transport at
-- the concrete resource, the game side is `Game.cert`, and the two alphabets
-- are related by a checked bijection.
binding-real : (m : ℕ) (d : Strat (Neg (Advᴵ ⊗ᴵ Honᴵ)) (Pos (Advᴵ ⊗ᴵ Honᴵ))) → asks≤ m d
             → Σ[ n ∈ ℕ ] ((i : ℕ)
                 → ∣ Pr₁⊥ (runWith⊥ respI⊥ sI₀ (mapStrat toQ fromR d))
                   -ℚ cum (n + i) (runᴹ (𝒫._∘_ {unitᴵ} {Resᴵ} {Advᴵ ⊗ᴵ Honᴵ} real resource) d)
                                  (indᵇ true) ∣ℚ
                   ≤ℚ ε m)
binding-real m d le =
  proj₁ (real-run d)
  , λ i → transferᴿ m d (proj₁ (real-run d)) i (proj₂ (real-run d) i) le
