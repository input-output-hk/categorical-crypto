{-# OPTIONS --safe --without-K #-}

-- The two adaptive-robust bridges every concrete-security proof over the
-- reactive interaction model runs on, both PROVEN:
--
--   • `badProb-bounded` — the SUPERMARTINGALE bound.  A potential `φ` (indexed by
--     the remaining query budget) with a support-preserved invariant `Inv`, at
--     least 1 on bad states and non-increasing in expectation per query, bounds
--     the bad-probability of ANY adaptive distinguisher by the initial
--     potential.  This carries the whole adaptivity argument, so what a concrete
--     system still owes is a NON-adaptive per-step certificate (`SuperCert`).
--   • `Hop.FLGP` over `Coupling` — the Fundamental Lemma of Game-Playing in COUPLED form:
--     one kernel emits the shared state and BOTH answers, the ideal projection
--     copying the real answer while the POST-state is good.  "Identical until
--     bad" then holds by construction, so the lemma has NO side conditions.
--
-- Both are `GamePlaying.Partial`'s at the embedded kernel `embedᵏ`, read back
-- through `total⇒⊥`.

open import categorical-crypto.Prelude hiding (_>>=_)

open import Data.List.Relation.Unary.All as ListAll using ()
open import Data.Rational
  renaming (_+_ to _+ℚ_; _-_ to _-ℚ_; ∣_∣ to ∣_∣ℚ; _≤_ to _≤ℚ_)
open import Data.Rational.Properties

open import CategoricalCrypto.GamePlaying.Partial
open import CategoricalCrypto.Interaction
open import CategoricalCrypto.Strategy
open import ProbabilisticLogic.Distribution.RationalDist
open import ProbabilisticLogic.Distribution.RationalDist.Expectation
open import ProbabilisticLogic.Distribution.RationalDist.Partial
open import ProbabilisticLogic.Distribution.Uniform

module CategoricalCrypto.GamePlaying where

private variable Q R St : Type

------------------------------------------------------------------------
-- The bad event

-- The probability that `bad` fires at some visited state during the run of `d`
-- against `resp` from `s` (1 immediately at a bad state — no monotonicity
-- needed): `GamePlaying.Partial`'s at the embedded kernel.
badProb : (St → Q → Dist-ℚ (St × R)) → (St → Bool) → St → Strat Q R → ℚ
badProb resp = badProb⊥ (embedᵏ resp)

------------------------------------------------------------------------
-- What a concrete system owes: a non-adaptive per-step certificate

Preserved : (St → Type) → (St → Q → Dist-ℚ (St × R)) → Type
Preserved Inv resp = ∀ s q → Inv s → OnSupport (λ sr → Inv (proj₁ sr)) (resp s q)

-- A supermartingale at a total kernel (`badProb⊥-super`'s hypotheses), with
-- the initial potential dominated by the claimed bound.
record SuperCert (resp : St → Q → Dist-ℚ (St × R)) (bad : St → Bool)
                 (s₀ : St) (ε : ℕ → ℚ) : Type₁ where
  field
    Inv    : St → Type
    φ      : ℕ → St → ℚ
    inv₀   : Inv s₀
    pres   : Preserved Inv resp
    φ-nn   : ∀ m s → Inv s → 0ℚ ≤ℚ φ m s
    φ-bad  : ∀ m s → Inv s → bad s ≡ true → 1ℚ ≤ℚ φ m s
    φ-step : ∀ m s q → Inv s → E (resp s q) (λ sr → φ m (proj₁ sr)) ≤ℚ φ (suc m) s
    φ-init : ∀ m → φ m s₀ ≤ℚ ε m

-- A supermartingale survives cutting the kernel down to the activations a
-- machine serves: the dead branch scores 0, which `φ-nn` already dominates.
prune-cert : {Q R St : Type} {K : St → Q → Dist-ℚ (St × R)} {bad : St → Bool}
             {s₀ : St} {ε : ℕ → ℚ} (dead : St → Q → Bool)
           → SuperCert K bad s₀ ε → SuperCert⊥ (prune dead K) bad s₀ ε
prune-cert {R = R} {St = St} {K = K} dead c = record
  { Inv = C.Inv ; φ = C.φ ; inv₀ = C.inv₀ ; φ-nn = C.φ-nn ; φ-bad = C.φ-bad
  ; φ-init = C.φ-init ; pres = pres⊥ ; φ-step = step⊥ }
  where
  module C = SuperCert c

  Φ : ℕ → St × R → ℚ
  Φ m sr = C.φ m (proj₁ sr)

  pres⊥ : Preserved⊥ C.Inv (prune dead K)
  pres⊥ s q inv with dead s q
  ... | true  = OnSupport-return tt
  ... | false = OnSupport-Dmap just (K s q) (C.pres s q inv)

  step⊥ : ∀ m s q → C.Inv s
        → E⊥ (prune dead K s q) (λ sr → C.φ m (proj₁ sr)) ≤ℚ C.φ (suc m) s
  step⊥ m s q inv with dead s q
  ... | true  = ≤-trans (≤-reflexive (lookupᴰℚ-return nothing (maybeℚ (Φ m))))
                        (C.φ-nn (suc m) s inv)
  ... | false = ≤-trans (≤-reflexive (Eⱼ (K s q) (Φ m))) (C.φ-step m s q inv)

-- The supermartingale bound: at `dead = λ _ _ → false`, `prune` is `embedᵏ`.
badProb-bounded : {resp : St → Q → Dist-ℚ (St × R)} {bad : St → Bool} {s₀ : St} {ε : ℕ → ℚ}
                → SuperCert resp bad s₀ ε
                → ∀ m d → asks≤ m d → badProb resp bad s₀ d ≤ℚ ε m
badProb-bounded c = badProb⊥-bounded (prune-cert (λ _ _ → false) c)

------------------------------------------------------------------------
-- The coupling the Fundamental Lemma (`Hop.FLGP`) is stated at

module Coupling (bad : St → Bool)
                (respB : St → Q → Dist-ℚ (St × (R × R))) where

  fR fI : St × (R × R) → St × R
  fR t = proj₁ t , proj₁ (proj₂ t)
  fI t = proj₁ t , cond (bad (proj₁ t)) (proj₂ (proj₂ t)) (proj₁ (proj₂ t))

  realK idealK : St → Q → Dist-ℚ (St × R)
  realK  s q = Dmap fR (respB s q)
  idealK s q = Dmap fI (respB s q)
