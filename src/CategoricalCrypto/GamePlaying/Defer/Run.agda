{-# OPTIONS --safe --without-K --guardedness #-}

-- Deferred sampling at the MACHINE-RUN layer: a secret planted in the state
-- and the same secret drawn at the step that first reads it give the same
-- closed run.
--
-- `GamePlaying.Defer.runWith-avg` is this argument at the `Dist-ℚ` game layer.
-- Here the runs are `Protocol.Machine.runᴹ`, the comparison is `_≈ₚ_` rather
-- than `_≡_`, and the draw is a `Dₚ`, so the `coin` case is
-- `Dp.Commutative.>>=ₚ-swap` where the game layer's is `Expectation.E-swap`.
--
-- It is the one argument `Machines.Sim`'s equality cannot make: a `≲`'s state
-- map is a function, so it relates a point mass to a point mass, where moving
-- a draw across an activation relates a point mass to a mixture
-- (`docs/coin-toss.md` §5).  Hence a hop whose two sides sample at different
-- activations lands here and not at `≈ᴹ`.
--
-- The draw's affineness is a HYPOTHESIS and not a fact: `botₚ >>=ₚ _` is
-- `botₚ`, so only a terminating draw may be introduced where nothing reads it.
-- `ProbabilisticLogic.Dp.Coin.coinₚ-const` is the instance the layer has.

open import Data.Bool.Base using (Bool)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Unit.Polymorphic.Base using (tt)
open import Level using (0ℓ)
open import Relation.Binary.PropositionalEquality using (_≡_; cong)

open import ProbabilisticLogic.Dp
open import ProbabilisticLogic.Dp.Coin using (coinₚ)
open import ProbabilisticLogic.Dp.Commutative using (>>=ₚ-swap)
open import ProbabilisticLogic.Dp.Reasoning

open import CategoricalCrypto.Iface
open import CategoricalCrypto.Machines.Base using (𝒱ₚ)
open import CategoricalCrypto.Protocol.Machine using (resumeᴹ; runᴹ; runᴹFrom)
open import CategoricalCrypto.Strategy using (Strat; ask; coin; out)
open import CategoricalCrypto.UC.Machine.Run using (Closed)

import CategoricalCrypto.Machines.Core as Core

module CategoricalCrypto.GamePlaying.Defer.Run where

private module MC = Core (𝒱ₚ 0ℓ)

-- `f` is the PLANTED side, run at a family of states indexed by the secret;
-- `g` is the DEFERRING side, run at a single state.  The relation compares a
-- family with one state, which is what carries "the secret is fixed here and
-- not yet drawn there".
module _ {V : Set} (μ : Dₚ V) (μ-const : (e : Dₚ Bool) → (μ >>=ₚ (λ _ → e)) ≈ₚ e)
         {B : Iface} (f g : Closed B) (_≋_ : (V → MC.St f) → MC.St g → Set) where

  -- One activation, averaged.  A family of outcomes counts as related when its
  -- states are and its answer does not depend on the secret; at the step that
  -- DRAWS, the consumer reindexes the two draws against each other and then
  -- discharges this at a constant family, one matched pair at a time.
  DeferStep : Set
  DeferStep =
      (fs : V → MC.St f) (s : MC.St g) → fs ≋ s → (q : Neg B)
      (K : MC.St f × (⊥ ⊎ Pos B) → Dₚ Bool) (K′ : MC.St g × (⊥ ⊎ Pos B) → Dₚ Bool)
    → ( (gs : V → MC.St f × (⊥ ⊎ Pos B)) (t : MC.St g × (⊥ ⊎ Pos B))
        → (λ v → proj₁ (gs v)) ≋ proj₁ t → ((v : V) → proj₂ (gs v) ≡ proj₂ t)
        → (μ >>=ₚ λ v → K (gs v)) ≈ₚ K′ t )
    → (μ >>=ₚ λ v → MC.step f (fs v , inj₂ q) >>=ₚ K)
      ≈ₚ (MC.step g (s , inj₂ q) >>=ₚ K′)

  module _ (defer : DeferStep) where

    runFrom-defer : (fs : V → MC.St f) (s : MC.St g) → fs ≋ s
                  → (d : Strat (Neg B) (Pos B))
                  → (μ >>=ₚ λ v → runᴹFrom f (fs v) d) ≈ₚ runᴹFrom g s d
    runFrom-defer fs s rel (out b)    = μ-const (returnₚ b)
    runFrom-defer fs s rel (coin ν k) =
          >>=ₚ-swap μ (coinₚ ν) (λ v b → runᴹFrom f (fs v) (k b))
      ⟨≈⟩ bindᶠ (λ b → runFrom-defer fs s rel (k b))
    runFrom-defer fs s rel (ask q k)  =
      defer fs s rel q (resumeᴹ f contᶠ) (resumeᴹ g contᵍ) point
      where
      contᶠ : MC.St f → Pos B → Dₚ Bool
      contᶠ m r = runᴹFrom f m (k r)

      contᵍ : MC.St g → Pos B → Dₚ Bool
      contᵍ m r = runᴹFrom g m (k r)

      point : (gs : V → MC.St f × (⊥ ⊎ Pos B)) (t : MC.St g × (⊥ ⊎ Pos B))
            → (λ v → proj₁ (gs v)) ≋ proj₁ t → ((v : V) → proj₂ (gs v) ≡ proj₂ t)
            → (μ >>=ₚ λ v → resumeᴹ f contᶠ (gs v)) ≈ₚ resumeᴹ g contᵍ t
      point gs (_  , inj₁ a) rel′ eq = ⊥-elim a
      point gs (m′ , inj₂ r) rel′ eq =
            bindᶠ align
        ⟨≈⟩ runFrom-defer (λ v → proj₁ (gs v)) m′ rel′ (k r)
        where
        -- The answer is the secret-independent one, so the resumption reduces
        -- at every `v`.
        align : (v : V) → resumeᴹ f contᶠ (gs v) ≈ₚ contᶠ (proj₁ (gs v)) r
        align v = ≡⇒≈ₚ (cong (λ z → resumeᴹ f contᶠ (proj₁ (gs v) , z)) (eq v))

    -- …and the whole closed run, at a family that is constant before the first
    -- activation: neither machine has drawn anything yet.
    run-defer : (f₀ : MC.St f) (g₀ : MC.St g) → (λ _ → f₀) ≋ g₀
              → MC.point (MC.state f) tt ≈ₚ returnₚ f₀
              → MC.point (MC.state g) tt ≈ₚ returnₚ g₀
              → (d : Strat (Neg B) (Pos B)) → runᴹ f d ≈ₚ runᴹ g d
    run-defer f₀ g₀ rel pf pg d =
          bindˣ pf ⟨≈⟩ >>=ₚ-identityˡ f₀ (λ m → runᴹFrom f m d)
      ⟨≈⟩ ≈sym (μ-const (runᴹFrom f f₀ d))
      ⟨≈⟩ runFrom-defer (λ _ → f₀) g₀ rel d
      ⟨≈⟩ ≈sym (bindˣ pg ⟨≈⟩ >>=ₚ-identityˡ g₀ (λ m → runᴹFrom g m d))
