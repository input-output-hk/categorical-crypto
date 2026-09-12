{-# OPTIONS --safe --without-K --guardedness #-}

-- `prAgree`'s statement off protocol images: the closed run of a RAW machine in
-- `Dₚ` is the run of a step kernel in `Dist⊥`.
--
-- `Protocol.Machine.Agree` gets there by two nested `Stable` inductions, the
-- inner one on the inductive `Calls` tree a protocol activation drives.  A raw
-- machine has no such tree — its step is an arbitrary `Dₚ` computation, a
-- ⊕-trace at a composite — so the inner induction is replaced by a HYPOTHESIS,
-- `StepSettles`: each activation settles, at its own fuel, on a `Dist⊥` answer.
-- Everything else is the same induction on the strategy, with `Dp.Settle`'s
-- bind junction in place of `Dp.Stable`'s.
--
-- The fuel is per activation and never global: `Dp.Settle.Settles-bind⋆` maxes
-- the continuations' fuels over the finitely many values one junction reaches,
-- so a run of `d` asks and a run of `d` answers at whatever depth each needs.

open import Data.Bool.Base using (Bool)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Maybe.Base using (just)
open import Data.Nat.Base using (ℕ; _+_)
open import Data.Nat.Properties using (m≤m+n)
open import Data.Product.Base using (Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Unit.Polymorphic.Base using (tt)
open import Level using (0ℓ)
open import Relation.Binary.PropositionalEquality using (_≡_; trans)

open import ProbabilisticLogic.Distribution.RationalDist
open import ProbabilisticLogic.Distribution.RationalDist.Expectation
open import ProbabilisticLogic.Distribution.RationalDist.Partial
open import ProbabilisticLogic.Distribution.Uniform using (indᵇ)
open import ProbabilisticLogic.Dp
open import ProbabilisticLogic.Dp.Advantage using (indᵇ-nn)
open import ProbabilisticLogic.Dp.Coin
open import ProbabilisticLogic.Dp.Settle

open import CategoricalCrypto.Iface
open import CategoricalCrypto.Interaction using (runWith; runWith⊥; runWith⊥-emb)
open import CategoricalCrypto.Machines.Base using (𝒱ₚ)
open import CategoricalCrypto.Protocol.Machine using (resumeᴹ; runᴹ; runᴹFrom)
open import CategoricalCrypto.Strategy using (Strat; ask; coin; out)

import CategoricalCrypto.Machines.Core as Core

module CategoricalCrypto.Protocol.Machine.Raw where

private module MC = Core (𝒱ₚ 0ℓ)

-- A kernel's answer read in the machine's output alphabet: a closed machine's
-- domain summand is empty, so every output of its is one of these.  Stated at
-- the ANSWER type rather than at the interface, which `Pos` does not determine.
ansᴹ : {S R : Set} → S × R → S × (⊥ ⊎ R)
ansᴹ (m , r) = m , inj₂ r

module _ {B : Iface} (M : MC.Machine (⊥ ⊎ Neg B) (⊥ ⊎ Pos B))
         (K : MC.St M → Neg B → Dist⊥ (MC.St M × Pos B)) where

  -- What replaces the inner induction: every activation settles, at a fuel of
  -- its own, on the kernel's answer read in the machine's output alphabet.
  StepSettles : Set
  StepSettles = (m : MC.St M) (q : Neg B)
              → Σ[ n ∈ ℕ ] Settles n (MC.step M (m , inj₂ q)) (Dmap⊥ ansᴹ (K m q))

  module _ (ker : StepSettles) where

    rawAgree : (m : MC.St M) (d : Strat (Neg B) (Pos B))
             → Σ[ n ∈ ℕ ] Settles n (runᴹFrom M m d) (runWith⊥ K m d)
    rawAgree m (out b)    = 1 , Settles-return b
    rawAgree m (coin μ k) =
      branch (Settles-bind⋆ 2 (coinₚ μ) (λ c → runᴹFrom M m (k c)) (Dmap just μ) κ
                            (Settles-coin μ) λ c → rawAgree m (k c))
      where
      κ : Bool → Dist⊥ Bool
      κ c = runWith⊥ K m (k c)

      branch : Σ[ n ∈ ℕ ] Settles n (runᴹFrom M m (coin μ k)) (Dmap just μ >>=⊥ κ)
             → Σ[ n ∈ ℕ ] Settles n (runᴹFrom M m (coin μ k)) (runWith⊥ K m (coin μ k))
      branch (n , s) = n , Settles-resp (Dmap just μ >>=⊥ κ) (μ >>=ᴹ κ) (E⊥-coin μ κ) s
    rawAgree m (ask q k)  =
      junction (Settles-bind⋆ (proj₁ (ker m q)) (MC.step M (m , inj₂ q)) (resumeᴹ M cont)
                              (Dmap⊥ ansᴹ (K m q)) κ (proj₂ (ker m q)) w)
      where
      cont : MC.St M → Pos B → Dₚ Bool
      cont m′ r = runᴹFrom M m′ (k r)

      κ : MC.St M × (⊥ ⊎ Pos B) → Dist⊥ Bool
      κ (_  , inj₁ a) = ⊥-elim a
      κ (m′ , inj₂ r) = runWith⊥ K m′ (k r)

      w : (p : MC.St M × (⊥ ⊎ Pos B)) → Σ[ n ∈ ℕ ] Settles n (resumeᴹ M cont p) (κ p)
      w (_  , inj₁ a) = ⊥-elim a
      w (m′ , inj₂ r) = rawAgree m′ (k r)

      junction : Σ[ n ∈ ℕ ] Settles n (runᴹFrom M m (ask q k)) (Dmap⊥ ansᴹ (K m q) >>=⊥ κ)
               → Σ[ n ∈ ℕ ] Settles n (runᴹFrom M m (ask q k)) (runWith⊥ K m (ask q k))
      junction (n , s) =
        n , Settles-resp (Dmap⊥ ansᴹ (K m q) >>=⊥ κ) (K m q >>=⊥ λ sr → κ (ansᴹ sr))
                         (E⊥-map-bind ansᴹ (K m q) κ) s

    -- The initial state is itself effectful at a Kleisli base, so it settles
    -- like any other step and the closed run is one more junction.
    module _ (σ₀ : Dist⊥ (MC.St M)) (n₀ : ℕ)
             (pt : Settles n₀ (MC.point (MC.state M) tt) σ₀) where

      rawRun : (d : Strat (Neg B) (Pos B))
             → Σ[ n ∈ ℕ ] Settles n (runᴹ M d) (σ₀ >>=⊥ λ m → runWith⊥ K m d)
      rawRun d = Settles-bind⋆ n₀ (MC.point (MC.state M) tt) (λ m → runᴹFrom M m d) σ₀
                              (λ m → runWith⊥ K m d) pt λ m → rawAgree m d

      -- `Protocol.Machine.PrAgree`'s shape at a raw machine, at either verdict.
      rawPr : (b : Bool) (d : Strat (Neg B) (Pos B))
            → Σ[ n ∈ ℕ ] ((i : ℕ) → cum (n + i) (runᴹ M d) (indᵇ b)
                                   ≡ E⊥ (σ₀ >>=⊥ λ m → runWith⊥ K m d) (indᵇ b))
      rawPr b d = proj₁ (rawRun d)
                , λ i → Settles-cum (proj₂ (rawRun d)) (indᵇ-nn b) _ (m≤m+n _ i)

  -- …and at a TOTAL kernel given in `Dist-ℚ` along a state embedding, which is
  -- the form a closed game states its bound at.  The embedding is what lets the
  -- machine carry state the game does not (`Interaction.runWith⊥-emb`).
  module _ {S : Set} (resp : S → Neg B → Dist-ℚ (S × Pos B)) (emb : S → MC.St M)
           (agree : (s : S) (q : Neg B) → K (emb s) q
                  ≈Mℚ (resp s q >>=ᴹ λ sr → return⊥ (emb (proj₁ sr) , proj₂ sr)))
    where

    rawKernel : StepSettles → (b : Bool) (s : S) (d : Strat (Neg B) (Pos B))
              → Σ[ n ∈ ℕ ] ((i : ℕ) → cum (n + i) (runᴹFrom M (emb s) d) (indᵇ b)
                                     ≡ E (runWith resp s d) (indᵇ b))
    rawKernel ker b s d =
      proj₁ (rawAgree ker (emb s) d)
      , λ i → trans (Settles-cum (proj₂ (rawAgree ker (emb s) d)) (indᵇ-nn b) _ (m≤m+n _ i))
              (trans (runWith⊥-emb resp K emb agree s d (maybeℚ (indᵇ b)))
                     (lookupᴰℚ-Dmap just (runWith resp s d) (maybeℚ (indᵇ b))))
