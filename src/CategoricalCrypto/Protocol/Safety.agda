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
-- This is `GamePlaying.badProb-super` for the protocol layer's own observable:
-- the trajectory reading `hitRun` rather than the reactive model's `badProb`,
-- over `Dist⊥` rather than `Dist-ℚ` — divergence is not a violation, so the
-- `nothing` sink is vacuously invariant-preserving and scores 0 in `E⊥`.

open import Data.Bool.Base using (Bool; true; false)
open import Data.List.Relation.Unary.All as ListAll using ()
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)
open import Data.Rational using (ℚ; 0ℚ; 1ℚ) renaming (_≤_ to _≤ℚ_)
open import Data.Rational.Properties using (≤-refl; ≤-reflexive; ≤-trans)
open import Relation.Binary.PropositionalEquality

open import ProbabilisticLogic.Prelude
open import ProbabilisticLogic.Distribution.RationalDist using (OnSupport; lookupᴰℚ-return)
open import ProbabilisticLogic.Distribution.RationalDist.Expectation using
  (E⊥; E-bind; E-const; E-mono; E-mono-on; E⊥-bind; maybeℚ; Pr₁⊥≤1)
open import ProbabilisticLogic.Distribution.Uniform using (bool→ℚ)

open import CategoricalCrypto.Iface
open import CategoricalCrypto.Protocol
open import CategoricalCrypto.Protocol.Observe
open import CategoricalCrypto.Strategy

module CategoricalCrypto.Protocol.Safety where

module _ {B : Iface} (P : Protocol unitᴵ B) (Bad : St P → Bool) where

  -- One activation of a closed protocol, read as a partial distribution on
  -- (post-state, answer).
  kernel : St P → Neg B → Dist⊥ (St P × Pos B)
  kernel s q = evalC (step P s q)

  private
    verdict : (acc : Bool) (st : St P) (b : Bool)
            → Pr₁⊥ (hitFrom P Bad acc st (out b)) ≡ bool→ℚ acc
    verdict acc st b = lookupᴰℚ-return (just acc) mb

  -- What a concrete system owes: a non-adaptive per-step certificate, with the
  -- initial potential dominated by the claimed bound.
  record HitCert (ε : ℕ → ℚ) : Set₁ where
    field
      Inv    : St P → Set
      φ      : ℕ → St P → ℚ
      inv₀   : Inv (init P)
      pres   : ∀ s q → Inv s → OnSupport (Reached (λ sr → Inv (proj₁ sr))) (kernel s q)
      φ-nn   : ∀ m s → Inv s → 0ℚ ≤ℚ φ m s
      φ-bad  : ∀ m s → Inv s → Bad s ≡ true → 1ℚ ≤ℚ φ m s
      φ-step : ∀ m s q → Inv s → E⊥ (kernel s q) (λ sr → φ m (proj₁ sr)) ≤ℚ φ (suc m) s
      φ-init : ∀ m → φ m (init P) ≤ℚ ε m

  module _ {ε : ℕ → ℚ} (cert : HitCert ε) where

    open HitCert cert

    -- The accumulator is exactly `Bad` at the state the run is at, which is
    -- what `hitRun` starts from, so no separate initialization step is owed.
    super : ∀ m d s → asks≤ m d → Inv s
          → Pr₁⊥ (hitFrom P Bad (Bad s) s d) ≤ℚ φ m s
    super m (out b) s le inv with Bad s in eqb
    ... | true  = ≤-trans (≤-reflexive (verdict true  s b)) (φ-bad m s inv eqb)
    ... | false = ≤-trans (≤-reflexive (verdict false s b)) (φ-nn  m s inv)
    super zero    (ask q k) s ()  inv
    super (suc m) (ask q k) s le inv with Bad s in eqb
    ... | true  = ≤-trans (Pr₁⊥≤1 (hitFrom P Bad true s (ask q k)))
                          (φ-bad (suc m) s inv eqb)
    ... | false = ≤-trans (≤-reflexive (E⊥-bind (kernel s q) Hk bool→ℚ))
                  (≤-trans (E-mono-on (kernel s q) (maybeℚ Ph) (maybeℚ Pφ) ptw)
                           (φ-step m s q inv))
      where
      Hk : St P × Pos B → Dist⊥ Bool
      Hk (s′ , r) = hitFrom P Bad (Bad s′) s′ (k r)

      Ph Pφ : St P × Pos B → ℚ
      Ph sr = Pr₁⊥ (Hk sr)
      Pφ sr = φ m (proj₁ sr)

      onReach : (x : Maybe (St P × Pos B)) → Reached (λ sr → Inv (proj₁ sr)) x
              → maybeℚ Ph x ≤ℚ maybeℚ Pφ x
      onReach (just (s′ , r)) inv′ = super m (k r) s′ (le r) inv′
      onReach nothing         _    = ≤-refl

      ptw : OnSupport (λ x → maybeℚ Ph x ≤ℚ maybeℚ Pφ x) (kernel s q)
      ptw = ListAll.map (λ {e} → onReach (proj₂ e)) (pres s q inv)
    super m (coin μ k) s le inv with Bad s in eqb
    ... | true  = ≤-trans (Pr₁⊥≤1 (hitFrom P Bad true s (coin μ k)))
                          (φ-bad m s inv eqb)
    ... | false = ≤-trans (≤-reflexive (E-bind μ Kb mb))
                  (≤-trans (E-mono μ (λ b → Pr₁⊥ (Kb b)) (λ _ → φ m s) ptw)
                           (≤-reflexive (E-const μ (φ m s))))
      where
      Kb : Bool → Dist⊥ Bool
      Kb b = hitFrom P Bad false s (k b)

      ptw : ∀ b → Pr₁⊥ (Kb b) ≤ℚ φ m s
      ptw b = subst (λ z → Pr₁⊥ (hitFrom P Bad z s (k b)) ≤ℚ φ m s) eqb
                    (super m (k b) s (le b) inv)

    hit-bounded : BoundedHit P Bad ε
    hit-bounded m d le = ≤-trans (super m d (init P) le inv₀) (φ-init m)
