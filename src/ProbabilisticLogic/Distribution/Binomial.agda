{-# OPTIONS --safe --without-K #-}

open import categorical-crypto.Prelude as P hiding (pure; _>>=_; _⊎_; _*_; _/_; _⊗_; isEquivalence; trans)

open import Relation.Binary using (Setoid)
open import Relation.Unary using (U; _≐_; _∩_)
import Relation.Binary.Reasoning.Setoid as ≈-Reasoning

import Data.List.NonEmpty as NE
open import Data.Nat using (_≤_)
open import Data.List.Relation.Unary.Any using (here)
import Data.List.Relation.Unary.All as All
open import Data.List.Relation.Unary.AllPairs using (AllPairs; []; _∷_)
open import Data.Rational as ℚ using (ℚ; _/_)
open import Data.Integer using (+_)

open import ProbabilisticLogic.Abstract
open import ProbabilisticLogic.Reasoning

module ProbabilisticLogic.Distribution.Binomial c ℓ (a : Abstract c ℓ) where

open Abstract a
open import ProbabilisticLogic.Distribution.Bernoulli c ℓ a
open import ProbabilisticLogic.Expectation c ℓ a

private module Eq = Setoid setoid

------------------------------------------------------------------------
-- The Binomial distribution as a product of Bernoullis.

-- The k-fold trial space: a nested product of `Bool`.
Bool^ : ℕ → Type
Bool^ zero    = ⊤
Bool^ (suc k) = Bool × Bool^ k

-- The Binomial distribution: k independent Bernoulli(m / (m + n)) trials,
-- assembled as the product distribution `bernoulli ⊗ bernoulli ⊗ ⋯ ⊗ bernoulli`.
-- A point of the sample space records the outcome of every trial.
binomial : (k m n : ℕ) ⦃ _ : NonZero (m +ℕ n) ⦄ → ProbDistr (Bool^ k)
binomial zero    m n = empirical (tt NE.∷ [])
binomial (suc k) m n = bernoulli m n ⊗ binomial k m n

------------------------------------------------------------------------
-- Predicates on outcomes.

-- Number of trials that landed `true`.
count : ∀ {k} → Bool^ k → ℕ
count {zero}  _              = 0
count {suc k} (false , bs)   = count bs
count {suc k} (true  , bs)   = suc (count bs)

-- Exactly i trials are true.
exactly : ∀ {k} → ℕ → Bool^ k → Type
exactly i bs = count bs ≡ i

-- At least i trials are true.
at-least : ∀ {k} → ℕ → Bool^ k → Type
at-least i bs = i ≤ count bs

-- At most i trials are true.
at-most : ∀ {k} → ℕ → Bool^ k → Type
at-most i bs = count bs ≤ i

-- Every trial landed `true`.  Coincides with `exactly k` and `at-least k`
-- on a `Bool^ k` outcome.
all-true : ∀ {k} → Bool^ k → Type
all-true {zero}  _        = ⊤
all-true {suc k} (b , bs) = (↑ id) b × all-true bs

-- Every trial landed `false`.  Coincides with `exactly 0` and `at-most 0`.
all-false : ∀ {k} → Bool^ k → Type
all-false {zero}  _        = ⊤
all-false {suc k} (b , bs) = (↑ not) b × all-false bs

------------------------------------------------------------------------
-- Iterated multiplication on `Probability` and on `ℚ`.

pow : Probability → ℕ → Probability
pow _ zero    = 1#
pow p (suc k) = p * pow p k

pow-ℚ : ℚ → ℕ → ℚ
pow-ℚ _ zero    = + 1 / 1
pow-ℚ p (suc k) = p ℚ.* pow-ℚ p k

private
  pow-cong : ∀ k {x y} → x ≈ y → pow x k ≈ pow y k
  pow-cong zero    _   = Eq.refl
  pow-cong (suc k) x≈y = *-cong x≈y (pow-cong k x≈y)

  -- The Probability-level k-fold product of `fromℚ p` is the image of
  -- the ℚ-level k-fold product, by induction using `fromℚ-1` and
  -- `fromℚ-homomorphism`.
  pow-fromℚ : ∀ p k → pow (fromℚ p) k ≈ fromℚ (pow-ℚ p k)
  pow-fromℚ p zero    = Eq.sym fromℚ-1
  pow-fromℚ p (suc k) = begin
    fromℚ p * pow (fromℚ p) k       ≈⟨ *-congˡ (pow-fromℚ p k) ⟩
    fromℚ p * fromℚ (pow-ℚ p k)     ≈⟨ fromℚ-homomorphism ⟩
    fromℚ (p ℚ.* pow-ℚ p k)         ∎
    where open ≈-Reasoning setoid

------------------------------------------------------------------------
-- Probability that all trials succeed / all fail, in `pow` form.

-- Probability that all k trials succeed equals the k-th power of the
-- single-trial success probability.  Pure consequence of `⊗-rect`.
P-all-true : ∀ k m n ⦃ _ : NonZero (m +ℕ n) ⦄
           → binomial k m n ∙ all-true ≈ pow (bernoulli m n ∙ (↑ id)) k
P-all-true zero    m n = PU≈1
P-all-true (suc k) m n = begin
  binomial (suc k) m n ∙ all-true
    ≈⟨ ⊗-rect ⟩
  bernoulli m n ∙ (↑ id) * binomial k m n ∙ all-true
    ≈⟨ *-congˡ (P-all-true k m n) ⟩
  bernoulli m n ∙ (↑ id) * pow (bernoulli m n ∙ (↑ id)) k ∎
  where open ≈-Reasoning setoid

-- Probability that all k trials fail equals the k-th power of the
-- single-trial failure probability.  Symmetric to `P-all-true`.
P-all-false : ∀ k m n ⦃ _ : NonZero (m +ℕ n) ⦄
            → binomial k m n ∙ all-false ≈ pow (bernoulli m n ∙ (↑ not)) k
P-all-false zero    m n = PU≈1
P-all-false (suc k) m n = begin
  binomial (suc k) m n ∙ all-false
    ≈⟨ ⊗-rect ⟩
  bernoulli m n ∙ (↑ not) * binomial k m n ∙ all-false
    ≈⟨ *-congˡ (P-all-false k m n) ⟩
  bernoulli m n ∙ (↑ not) * pow (bernoulli m n ∙ (↑ not)) k ∎
  where open ≈-Reasoning setoid

------------------------------------------------------------------------
-- Probabilities expressed directly as `fromℚ` of a rational power.

-- Probability that all k trials succeed = (m / (m + n))^k as a rational.
P-all-true-ℚ : ∀ k m n ⦃ _ : NonZero (m +ℕ n) ⦄
             → binomial k m n ∙ all-true ≈ fromℚ (pow-ℚ (+ m / (m +ℕ n)) k)
P-all-true-ℚ k m n = begin
  binomial k m n ∙ all-true                  ≈⟨ P-all-true k m n ⟩
  pow (bernoulli m n ∙ (↑ id)) k             ≈⟨ pow-cong k (P-bernoulli-true m n) ⟩
  pow (fromℚ (+ m / (m +ℕ n))) k             ≈⟨ pow-fromℚ (+ m / (m +ℕ n)) k ⟩
  fromℚ (pow-ℚ (+ m / (m +ℕ n)) k)           ∎
  where open ≈-Reasoning setoid

-- Probability that all k trials fail = (n / (m + n))^k as a rational.
P-all-false-ℚ : ∀ k m n ⦃ _ : NonZero (m +ℕ n) ⦄
              → binomial k m n ∙ all-false ≈ fromℚ (pow-ℚ (+ n / (m +ℕ n)) k)
P-all-false-ℚ k m n = begin
  binomial k m n ∙ all-false                 ≈⟨ P-all-false k m n ⟩
  pow (bernoulli m n ∙ (↑ not)) k            ≈⟨ pow-cong k (P-bernoulli-false m n) ⟩
  pow (fromℚ (+ n / (m +ℕ n))) k             ≈⟨ pow-fromℚ (+ n / (m +ℕ n)) k ⟩
  fromℚ (pow-ℚ (+ n / (m +ℕ n)) k)           ∎
  where open ≈-Reasoning setoid

------------------------------------------------------------------------
-- Recursive enumeration of `Bool^ k` and its support properties.

instance
  DecEq-Bool^ : ∀ {k} → DecEq (Bool^ k)
  DecEq-Bool^ {zero}  = DecEq-⊤
  DecEq-Bool^ {suc k} = DecEq-× ⦃ DecEq-Bool ⦄ ⦃ DecEq-Bool^ ⦄

binomial-support : (k : ℕ) → List (Bool^ k)
binomial-support zero    = tt ∷ []
binomial-support (suc k) = (true ∷ false ∷ []) ×ᴸ binomial-support k

private
  -- ⊤ is exhausted by [tt]; the singleton support has full mass under
  -- the binomial-0 distribution (= pure tt).
  ⊤-cover : (_∈ˡ (tt ∷ [])) ≐ U
  proj₁ ⊤-cover _ = tt
  proj₂ ⊤-cover {tt} _ = here P.refl

  binomial-0-full : ∀ m n ⦃ _ : NonZero (m +ℕ n) ⦄
                  → binomial 0 m n ∙ (_∈ˡ (tt ∷ [])) ≈ 1#
  binomial-0-full m n = Eq.trans (∙-cong ⊤-cover) PU≈1

binomial-support-distinct : (k : ℕ) → AllPairs _≢_ (binomial-support k)
binomial-support-distinct zero    = All.[] ∷ []
binomial-support-distinct (suc k) =
  AllPairs-×ᴸ bool-distinct (binomial-support-distinct k)

binomial-full : ∀ k m n ⦃ _ : NonZero (m +ℕ n) ⦄
              → binomial k m n ∙ (_∈ˡ binomial-support k) ≈ 1#
binomial-full zero    m n = binomial-0-full m n
binomial-full (suc k) m n =
  ⊗-full (true ∷ false ∷ []) (bernoulli-full m n)
         (binomial-support k)  (binomial-full k m n)

------------------------------------------------------------------------
-- Expected value of a (one-trial) Binomial random variable.
--
-- For binomial 1 m n = bernoulli m n ⊗ pure tt over Bool × ⊤, the
-- indicator of "first trial is true" has expected value m / (m + n).
-- This reduces to the Bernoulli case via `⊗-marg₁`.

E-binomial-1-first-true : ∀ m n ⦃ _ : NonZero (m +ℕ n) ⦄
                        → E[ binomial 1 m n , 1[ ↑ id P.∘ proj₁ ] ]≈ fromℚ (+ m / (m +ℕ n))
E-binomial-1-first-true m n = E-resp-≈ first-true-prob
  (E-indicator ⦃ deceq-Ω = DecEq-Bool^ ⦄
    (E-of-support (binomial-support 1) (binomial-support-distinct 1)
                  (binomial-full 1 m n) (λ _ → 0#))
    (↑ id P.∘ proj₁))
  where
    open ≈-Reasoning setoid
    first-true-prob : binomial 1 m n ∙ (↑ id P.∘ proj₁) ≈ fromℚ (+ m / (m +ℕ n))
    first-true-prob = begin
      binomial 1 m n ∙ (↑ id P.∘ proj₁)
        ≈⟨ ⊗-marg₁ ⟩
      bernoulli m n ∙ (↑ id)
        ≈⟨ P-bernoulli-true m n ⟩
      fromℚ (+ m / (m +ℕ n)) ∎

------------------------------------------------------------------------
-- Expected count of a Binomial random variable: k * m / (m + n).

-- ℕ-scaling on the additive monoid (`Algebra.Properties.Monoid.Mult`),
-- aliased here as `_·ℕ_` to avoid clashing with `Data.Product._×_`:
-- `k ·ℕ x = x + (k - 1) ·ℕ x = x + … + x`.
import Algebra.Properties.Monoid.Mult as Mult
private module +-Mult = Mult +-monoid

infixr 8 _·ℕ_
_·ℕ_ : ℕ → Probability → Probability
_·ℕ_ = +-Mult._×_

-- The count function (number of successes) lifted to Probability.
count-as-prob : ∀ {k} → Bool^ k → Probability
count-as-prob {zero}  _        = 0#
count-as-prob {suc k} (b , bs) = 1[ ↑ id ] b + count-as-prob bs

-- The weight-sum of count-as-prob over the binomial-support equals
-- `k × m/(m+n)`.  This is the heart of E-binomial-count, separated out
-- because `E-binomial-count k m n .support` doesn't reduce for symbolic k.
ws-count-eq :
  ∀ k m n ⦃ _ : NonZero (m +ℕ n) ⦄
  → weight-sum (binomial k m n) count-as-prob (binomial-support k)
  ≈ k ·ℕ (fromℚ (+ m / (m +ℕ n)))
ws-count-eq zero    m n = weight-sum-0 (tt ∷ [])
ws-count-eq (suc k) m n = begin
  weight-sum (binomial (suc k) m n) count-as-prob sup
    ≈⟨ weight-sum-+ 1[ ↑ id P.∘ proj₁ ] (count-as-prob P.∘ proj₂) sup ⟩
  weight-sum (binomial (suc k) m n) 1[ ↑ id P.∘ proj₁ ] sup
    + weight-sum (binomial (suc k) m n) (count-as-prob P.∘ proj₂) sup
    ≈⟨ +-cong first-eq second-eq ⟩
  fromℚ (+ m / (m +ℕ n)) + k ·ℕ (fromℚ (+ m / (m +ℕ n))) ∎
  where
    open ≈-Reasoning setoid

    sup = binomial-support (suc k)

    -- Indicator rule + ⊗-marg₁ + Bernoulli's mean.
    first-eq : weight-sum (binomial (suc k) m n) 1[ ↑ id P.∘ proj₁ ] sup
             ≈ fromℚ (+ m / (m +ℕ n))
    first-eq = begin
      weight-sum (binomial (suc k) m n) 1[ ↑ id P.∘ proj₁ ] sup
        ≈⟨ weight-sum-1[X] (↑ id P.∘ proj₁) sup (binomial-support-distinct (suc k)) ⟩
      binomial (suc k) m n ∙ ((↑ id P.∘ proj₁) ∩ (_∈ˡ sup))
        ≈⟨ Eq.sym (mass-restrict ⦃ ∈ˡ-? ⦃ DecEq-Bool^ ⦄ ⦄ (binomial-full (suc k) m n)) ⟩
      binomial (suc k) m n ∙ (↑ id P.∘ proj₁)
        ≈⟨ ⊗-marg₁ ⟩
      bernoulli m n ∙ (↑ id)
        ≈⟨ P-bernoulli-true m n ⟩
      fromℚ (+ m / (m +ℕ n)) ∎

    -- Fubini for proj₂ + the inductive hypothesis.
    second-eq : weight-sum (binomial (suc k) m n) (count-as-prob P.∘ proj₂) sup
              ≈ k ·ℕ (fromℚ (+ m / (m +ℕ n)))
    second-eq = Eq.trans
      (weight-sum-proj₂ (true ∷ false ∷ []) bool-distinct (bernoulli-full m n)
                        (binomial-support k) count-as-prob)
      (ws-count-eq k m n)

-- The expected count under Binomial(k, m/(m+n)) equals k × m/(m+n) — that is,
-- m/(m+n) added to itself k times.
E-binomial-count : ∀ k m n ⦃ _ : NonZero (m +ℕ n) ⦄
                 → E[ binomial k m n , count-as-prob ]≈ (k ·ℕ fromℚ (+ m / (m +ℕ n)))
E-binomial-count k m n = record
  { support  = binomial-support k
  ; distinct = binomial-support-distinct k
  ; full     = binomial-full k m n
  ; value    = Eq.sym (ws-count-eq k m n)
  }
