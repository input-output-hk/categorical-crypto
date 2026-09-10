{-# OPTIONS --safe --without-K #-}

-- The reactive interaction model: an ADAPTIVE distinguisher probing a stateful
-- system, and the distinguishing advantage read off the verdict bit.  This is
-- the semantics every concrete-security statement in the library is phrased in
-- — `run⊥ f d` is the interaction of the distinguisher `d` with the partial
-- probabilistic system `f`, and `adv f g d` its advantage.
--
-- `TraceDeterminesRun` is the one thing about it that is assumed rather than
-- proven; see its declaration below.

open import categorical-crypto.Prelude hiding (_>>=_)

open import Data.Rational using (ℚ) renaming (_-_ to _-ℚ_; ∣_∣ to ∣_∣ℚ)
import Relation.Binary.Reasoning.Setoid as RS

open import CategoricalCrypto.SFunM
open import CategoricalCrypto.SFunPartial
open import CategoricalCrypto.Strategy
open import ProbabilisticLogic.Distribution.RationalDist
open import ProbabilisticLogic.Distribution.RationalDist.Expectation
open import ProbabilisticLogic.Distribution.RationalDist.Partial
open import ProbabilisticLogic.Distribution.RationalDist.Setoid

module CategoricalCrypto.Interaction where

private variable Q R St : Type

-- The adaptive distinguisher is `Strategy.Strat`: at each node output a guess,
-- flip a rational coin, or query and branch on the response.  A deterministic
-- tree class is provably too weak here — an environment that samples which
-- question to ask beats every single tree (`docs/md-relocation-plan.md` §D.1,
-- the refutation of the applied `Reflects`) — so the coin is native.

------------------------------------------------------------------------
-- Running a distinguisher, totally and partially

-- Against a bare response kernel, returning the output bit.
runWith : (St → Q → Dist-ℚ (St × R)) → St → Strat Q R → Dist-ℚ Bool
runWith resp s (out b)    = return-ℚ b
runWith resp s (ask q k)  = resp s q >>=ᴹ λ sr → runWith resp (proj₁ sr) (k (proj₂ sr))
runWith resp s (coin μ k) = μ >>=ᴹ λ b → runWith resp s (k b)

-- Against a stateful system, from its initial state.
run : SFunᵉ {M = Dist-ℚ} Q R → Strat Q R → Dist-ℚ Bool
run f = runWith (λ s q → SFunᵉ.fun f (s , q)) (SFunᵉ.init f)

runWith⊥ : (St → Q → Dist⊥ (St × R)) → St → Strat Q R → Dist⊥ Bool
runWith⊥ resp s (out b)    = return⊥ b
runWith⊥ resp s (ask q k)  = resp s q >>=⊥ λ sr → runWith⊥ resp (proj₁ sr) (k (proj₂ sr))
runWith⊥ resp s (coin μ k) = μ >>=ᴹ λ b → runWith⊥ resp s (k b)

run⊥ : SFun⊥ Q R → Strat Q R → Dist⊥ Bool
run⊥ f = runWith⊥ (λ s q → SFunᵉ.fun f (s , q)) (SFunᵉ.init f)

-- The distinguishing advantage of `d` between two systems.
adv : SFun⊥ Q R → SFun⊥ Q R → Strat Q R → ℚ
adv f g d = ∣ Pr₁⊥ (run⊥ f d) -ℚ Pr₁⊥ (run⊥ g d) ∣ℚ

------------------------------------------------------------------------
-- The partial run of an embedded total system is the embedded total run

run⊥-embed-gen : (resp : St → Q → Dist-ℚ (St × R)) (s : St) (d : Strat Q R)
               → runWith⊥ (λ s q → Dmap just (resp s q)) s d ≈Mℚ Dmap just (runWith resp s d)
run⊥-embed-gen resp s (out b) = begin
  return⊥ b                                  ≈˘⟨ >>=ᴹ-identityˡ b (return-ℚ ∘ just) ⟩
  Dmap just (return-ℚ b)                      ∎
  where open RS (Mℚ-setoid _)
run⊥-embed-gen resp s (ask q k) = begin
  (Dmap just (resp s q) >>=⊥ K⊥)
    ≈⟨ >>=⊥-embed (resp s q) K⊥ ⟩
  (resp s q >>=ᴹ K⊥)
    ≈⟨ >>=ᴹ-cong {μ = resp s q} {resp s q} {K⊥} {λ sr → Dmap just (G sr)}
         (λ P → refl) (λ sr → run⊥-embed-gen resp (proj₁ sr) (k (proj₂ sr))) ⟩
  (resp s q >>=ᴹ (λ sr → Dmap just (G sr)))
    ≈˘⟨ >>=ᴹ-assoc (resp s q) G (return-ℚ ∘ just) ⟩
  Dmap just (resp s q >>=ᴹ G)
    ∎
  where
    G  = λ sr → runWith resp (proj₁ sr) (k (proj₂ sr))
    K⊥ = λ sr → runWith⊥ (λ s q → Dmap just (resp s q)) (proj₁ sr) (k (proj₂ sr))
    open RS (Mℚ-setoid _)
run⊥-embed-gen resp s (coin μ k) = begin
  (μ >>=ᴹ λ b → runWith⊥ (λ s q → Dmap just (resp s q)) s (k b))
    ≈⟨ >>=ᴹ-cong {μ = μ} {μ} {λ b → runWith⊥ (λ s q → Dmap just (resp s q)) s (k b)}
         {λ b → Dmap just (G b)} (λ P → refl) (λ b → run⊥-embed-gen resp s (k b)) ⟩
  (μ >>=ᴹ λ b → Dmap just (G b))
    ≈˘⟨ >>=ᴹ-assoc μ G (return-ℚ ∘ just) ⟩
  Dmap just (μ >>=ᴹ G)
    ∎
  where
    G = λ b → runWith resp s (k b)
    open RS (Mℚ-setoid _)

run⊥-embed : (h : SFunᵉ {M = Dist-ℚ} Q R) (d : Strat Q R) → run⊥ (embed⊥ h) d ≈Mℚ Dmap just (run h d)
run⊥-embed h d = run⊥-embed-gen (λ s q → SFunᵉ.fun h (s , q)) (SFunᵉ.init h) d

------------------------------------------------------------------------
-- The one assumption of this layer
--
-- A fixed-list (trace) equivalence determines ADAPTIVE behaviour of stateful
-- kernels: transcript probabilities decompose prefix-wise into functionals of
-- fixed-list joint distributions (finite support + decidable equality of the
-- outputs make this formalizable).  Standard mathematics, crypto-free.

TraceDeterminesRun : Type₁
TraceDeterminesRun = {Q R : Type} {f g : SFun⊥ Q R}
                   → (_≈ᵉ_ {M = Dist⊥}) f g → ∀ d → run⊥ f d ≈Mℚ run⊥ g d
