{-# OPTIONS --safe --without-K #-}

-- The supermartingale bound for `BoundedHit`: a non-adaptive per-step
-- certificate (`HitCert`, `GamePlaying.Partial.SuperCert⊥` at `kernel P`)
-- bounds every adaptive strategy of the budget, through `hit≤badProb⊥`.
-- Divergence is not a violation: the `nothing` sink scores 0 in `E⊥`.
--
-- `PrHit` is the COMPLETED-RUN event, `badProb⊥` the PREFIX-REACHABILITY one
-- (it stops at the first bad state); they differ only on runs that hit and
-- then diverge (`docs/state-event-contract.md` §1, row 11).

open import Data.Bool.Base
open import Data.Maybe.Base
open import Data.Nat.Base
open import Data.Product.Base
open import Data.Rational renaming (_≤_ to _≤ℚ_)
open import Data.Rational.Properties
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

  hit-bounded : {ε : ℕ → ℚ} → HitCert ε → BoundedHit P Bad ε
  hit-bounded cert m d le = ≤-trans (hit≤badProb⊥ d (init P)) (badProb⊥-bounded cert m d le)
