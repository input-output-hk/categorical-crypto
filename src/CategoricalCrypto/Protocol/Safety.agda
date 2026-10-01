{-# OPTIONS --safe --without-K #-}

-- The supermartingale bound for `BoundedHit`: what a concrete protocol owes a
-- safety bound, once the adaptivity is taken care of generically.
--
-- A potential `φ`, indexed by the REMAINING query budget, with a
-- support-preserved invariant `Inv`, at least 1 on bad states and
-- non-increasing in expectation per query, bounds the probability that ANY
-- adaptive strategy of that budget reaches a bad state.  So a concrete system
-- owes only a NON-adaptive per-step certificate (`HitCert`).
--
-- This is `GamePlaying.Partial.badProb⊥-super` at `kernel P`, read through
-- `hit≤badProb⊥`: the protocol layer's own observable, the trajectory reading
-- `hitRun`, is dominated by the reactive model's bad-event probability.
-- Divergence is not a violation: the `nothing` sink is vacuously
-- invariant-preserving and scores 0 in `E⊥`.
--
-- `PrHit` is the COMPLETED-RUN event, `badProb⊥` the PREFIX-REACHABILITY one
-- (it stops at the first bad state); they differ only on runs that hit and
-- then diverge (`docs/state-event-contract.md` §1, row 11).

open import Data.Bool.Base using (Bool; true; false)
open import Data.Maybe.Base using (just)
open import Data.Nat.Base using (ℕ)
open import Data.Product.Base using (_×_; _,_)
open import Data.Rational using (ℚ) renaming (_≤_ to _≤ℚ_)
open import Data.Rational.Properties using (≤-reflexive; ≤-trans)
open import Relation.Binary.PropositionalEquality

open import ProbabilisticLogic.Distribution.RationalDist
open import ProbabilisticLogic.Distribution.RationalDist.Expectation
open import ProbabilisticLogic.Distribution.RationalDist.Partial
open import ProbabilisticLogic.Distribution.Uniform

open import CategoricalCrypto.GamePlaying.Partial
open import CategoricalCrypto.Iface
open import CategoricalCrypto.Protocol
open import CategoricalCrypto.Protocol.Observe
open import CategoricalCrypto.Strategy

module CategoricalCrypto.Protocol.Safety where

module _ {B : Iface} (P : Protocol unitᴵ B) (Bad : St P → Bool) where

  -- What a concrete system owes: a non-adaptive per-step certificate, with the
  -- initial potential dominated by the claimed bound — `GamePlaying.Partial`'s
  -- at `kernel P`.
  HitCert : (ℕ → ℚ) → Set₁
  HitCert = SuperCert⊥ (kernel P) Bad (init P)

  -- The trajectory reading is dominated by the bad-event probability at
  -- `kernel P`: equal until a bad state, where the latter is 1 and the former
  -- only the mass that still reaches a verdict.
  hit≤badProb⊥ : ∀ d s → Pr₁⊥ (hitFrom P Bad (Bad s) s d) ≤ℚ badProb⊥ (kernel P) Bad s d
  hit≤badProb⊥ (out b) s = ≤-reflexive (lookupᴰℚ-return (just (Bad s)) mb)
  hit≤badProb⊥ (ask q k) s with Bad s in eqb
  ... | true  = Pr₁⊥≤1 (hitFrom P Bad true s (ask q k))
  ... | false = ≤-trans (≤-reflexive (E⊥-bind (kernel P s q) Hk bool→ℚ))
                        (E⊥-mono (kernel P s q) _ _ λ (s′ , r) → hit≤badProb⊥ (k r) s′)
    where
    Hk : St P × Pos B → Dist⊥ Bool
    Hk (s′ , r) = hitFrom P Bad (Bad s′) s′ (k r)
  hit≤badProb⊥ (coin μ k) s with Bad s in eqb
  ... | true  = Pr₁⊥≤1 (hitFrom P Bad true s (coin μ k))
  ... | false = ≤-trans (≤-reflexive (E-bind μ (λ b → hitFrom P Bad false s (k b)) mb))
      (E-mono μ _ _ λ b →
        subst (λ z → Pr₁⊥ (hitFrom P Bad z s (k b)) ≤ℚ badProb⊥ (kernel P) Bad s (k b)) eqb
              (hit≤badProb⊥ (k b) s))

  module _ {ε : ℕ → ℚ} (cert : HitCert ε) where

    open SuperCert⊥ cert

    -- The accumulator is exactly `Bad` at the state the run is at, which is
    -- what `hitRun` starts from, so no separate initialization step is owed.
    super : ∀ m d s → asks≤ m d → Inv s → Pr₁⊥ (hitFrom P Bad (Bad s) s d) ≤ℚ φ m s
    super m d s le inv = ≤-trans (hit≤badProb⊥ d s)
      (badProb⊥-super (kernel P) Bad Inv φ pres φ-nn φ-bad φ-step m d s le inv)

    hit-bounded : BoundedHit P Bad ε
    hit-bounded m d le = ≤-trans (super m d (init P) le inv₀) (φ-init m)
