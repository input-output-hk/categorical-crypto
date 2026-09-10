{-# OPTIONS --safe --without-K #-}

-- The two adaptive-robust bridges every concrete-security proof over the
-- reactive interaction model runs on, both PROVEN:
--
--   • `badProb-super` — the SUPERMARTINGALE bound.  A potential `φ` (indexed by
--     the remaining query budget) with a support-preserved invariant `Inv`, at
--     least 1 on bad states and non-increasing in expectation per query, bounds
--     the bad-probability of ANY adaptive distinguisher by the initial
--     potential.  This carries the whole adaptivity argument, so what a concrete
--     system still owes is a NON-adaptive per-step certificate (`SuperCert`).
--   • `Coupling.FLGP` — the Fundamental Lemma of Game-Playing in COUPLED form:
--     one kernel emits the shared state and BOTH answers, the ideal projection
--     copying the real answer while the POST-state is good.  "Identical until
--     bad" then holds by construction, so the lemma has NO side conditions.
--
-- Both rest on expectation monotonicity, and nothing else.

open import categorical-crypto.Prelude hiding (_>>=_)

open import Data.List.Relation.Unary.All as ListAll using ()
open import Data.Rational using (ℚ; 0ℚ; 1ℚ)
  renaming (_+_ to _+ℚ_; _-_ to _-ℚ_; ∣_∣ to ∣_∣ℚ; _≤_ to _≤ℚ_)
open import Data.Rational.Properties using (≤-refl; ≤-reflexive; ≤-trans; +-inverseʳ; 0≤p⇒∣p∣≡p)

open import CategoricalCrypto.Interaction
open import CategoricalCrypto.Strategy
open import ProbabilisticLogic.Distribution.RationalDist
open import ProbabilisticLogic.Distribution.RationalDist.Expectation
open import ProbabilisticLogic.Distribution.Uniform using (bool→ℚ)

module CategoricalCrypto.GamePlaying where

private variable Q R St : Type

-- Case combinator (the prelude hides `if_then_else_`).
cond : {A : Type} → Bool → A → A → A
cond true  x _ = x
cond false _ y = y

cond-diag : {A : Type} (b : Bool) (x : A) → cond b x x ≡ x
cond-diag true  x = refl
cond-diag false x = refl

------------------------------------------------------------------------
-- The bad event

-- The probability that `bad` fires at some visited state during the run of `d`
-- against `resp` from `s` (1 immediately at a bad state — no monotonicity
-- needed).
badProb : (St → Q → Dist-ℚ (St × R)) → (St → Bool) → St → Strat Q R → ℚ
badProb resp bad s (out _)    = bool→ℚ (bad s)
badProb resp bad s (ask q k)  with bad s
... | true  = 1ℚ
... | false = E (resp s q) (λ sr → badProb resp bad (proj₁ sr) (k (proj₂ sr)))
badProb resp bad s (coin μ k) with bad s
... | true  = 1ℚ
... | false = E μ (λ b → badProb resp bad s (k b))

-- At a state where `bad` already holds, the bad-probability is 1.
badProb-bad : (resp : St → Q → Dist-ℚ (St × R)) (bad : St → Bool)
            → ∀ s (d : Strat Q R) → bad s ≡ true → badProb resp bad s d ≡ 1ℚ
badProb-bad resp bad s (out _)    eq rewrite eq = refl
badProb-bad resp bad s (ask q k)  eq rewrite eq = refl
badProb-bad resp bad s (coin μ k) eq rewrite eq = refl

------------------------------------------------------------------------
-- What a concrete system owes: a non-adaptive per-step certificate

-- `Inv` holds at every state the kernel can actually reach in one step.
Preserved : (St → Type) → (St → Q → Dist-ℚ (St × R)) → Type
Preserved Inv resp = ∀ s q → Inv s → OnSupport (λ sr → Inv (proj₁ sr)) (resp s q)

-- A birthday-style certificate for a kernel: everything `badProb-super` needs,
-- with the initial potential dominated by the claimed bound.
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

------------------------------------------------------------------------
-- The two bridges

badProb-super :
  (resp : St → Q → Dist-ℚ (St × R)) (bad : St → Bool)
  (Inv : St → Type) (φ : ℕ → St → ℚ)
  → Preserved Inv resp
  → (∀ m s → Inv s → 0ℚ ≤ℚ φ m s)
  → (∀ m s → Inv s → bad s ≡ true → 1ℚ ≤ℚ φ m s)
  → (∀ m s q → Inv s → E (resp s q) (λ sr → φ m (proj₁ sr)) ≤ℚ φ (suc m) s)
  → ∀ m d s → asks≤ m d → Inv s → badProb resp bad s d ≤ℚ φ m s
badProb-super resp bad Inv φ pres nn lb step m (out b) s le inv with bad s in eqb
... | true  = lb m s inv eqb
... | false = nn m s inv
badProb-super resp bad Inv φ pres nn lb step zero (ask q kd) s () inv
badProb-super resp bad Inv φ pres nn lb step (suc m) (ask q kd) s le inv
  with bad s in eqb
... | true  = lb (suc m) s inv eqb
... | false = ≤-trans
    (E-mono-on (resp s q)
      (λ sr → badProb resp bad (proj₁ sr) (kd (proj₂ sr)))
      (λ sr → φ m (proj₁ sr))
      (ListAll.map
        (λ {e} inv' → badProb-super resp bad Inv φ pres nn lb step m
                        (kd (proj₂ (proj₂ e))) (proj₁ (proj₂ e))
                        (le (proj₂ (proj₂ e))) inv')
        (pres s q inv)))
    (step m s q inv)
badProb-super resp bad Inv φ pres nn lb step m (coin μ kd) s le inv with bad s in eqb
... | true  = lb m s inv eqb
... | false = ≤-trans
    (E-mono μ (λ b → badProb resp bad s (kd b)) (λ _ → φ m s)
      (λ b → badProb-super resp bad Inv φ pres nn lb step m (kd b) s (le b) inv))
    (≤-reflexive (E-const μ (φ m s)))

badProb-bounded :
  {resp : St → Q → Dist-ℚ (St × R)} {bad : St → Bool} {s₀ : St} {ε : ℕ → ℚ}
  → SuperCert resp bad s₀ ε
  → ∀ m d → asks≤ m d → badProb resp bad s₀ d ≤ℚ ε m
badProb-bounded {resp = resp} {bad} {s₀} c m d le = ≤-trans
  (badProb-super resp bad (SuperCert.Inv c) (SuperCert.φ c) (SuperCert.pres c)
    (SuperCert.φ-nn c) (SuperCert.φ-bad c) (SuperCert.φ-step c)
    m d s₀ le (SuperCert.inv₀ c))
  (SuperCert.φ-init c m)

------------------------------------------------------------------------
-- The coupled Fundamental Lemma of Game-Playing

module Coupling (bad : St → Bool)
                (respB : St → Q → Dist-ℚ (St × (R × R))) where

  fR fI : St × (R × R) → St × R
  fR t = proj₁ t , proj₁ (proj₂ t)
  fI t = proj₁ t , cond (bad (proj₁ t)) (proj₂ (proj₂ t)) (proj₁ (proj₂ t))

  realK idealK : St → Q → Dist-ℚ (St × R)
  realK  s q = Dmap fR (respB s q)
  idealK s q = Dmap fI (respB s q)

  FLGP : ∀ s₀ d → ∣ Pr₁ (runWith idealK s₀ d) -ℚ Pr₁ (runWith realK s₀ d) ∣ℚ
                ≤ℚ badProb realK bad s₀ d
  FLGP s (out b) = subst (_≤ℚ bool→ℚ (bad s)) (sym lhs≡0) (0≤bool (bad s))
    where lhs≡0 : ∣ Pr₁ (return-ℚ b) -ℚ Pr₁ (return-ℚ b) ∣ℚ ≡ 0ℚ
          lhs≡0 = trans (cong ∣_∣ℚ (+-inverseʳ (Pr₁ (return-ℚ b))))
                        (0≤p⇒∣p∣≡p ≤-refl)
  FLGP s (ask q k) with bad s in eqbad
  ... | true  = ∣Pr-Pr∣≤1 (runWith idealK s (ask q k)) (runWith realK s (ask q k))
  ... | false =
      ≤-trans (≤-reflexive (cong₂ (λ x y → ∣ x -ℚ y ∣ℚ) eqI eqR))
     (≤-trans (E-abs-diff (respB s q) AI AR)
     (≤-trans (E-mono (respB s q) (λ t → ∣ AI t -ℚ AR t ∣ℚ) BB pointwise)
              (≤-reflexive (sym eqB))))
    where
      KI KR : St × R → Dist-ℚ Bool
      KI sr = runWith idealK (proj₁ sr) (k (proj₂ sr))
      KR sr = runWith realK  (proj₁ sr) (k (proj₂ sr))

      AI AR BB : St × (R × R) → ℚ
      AI t = Pr₁ (KI (fI t))
      AR t = Pr₁ (KR (fR t))
      BB t = badProb realK bad (proj₁ t) (k (proj₁ (proj₂ t)))

      eqI : Pr₁ (runWith idealK s (ask q k)) ≡ E (respB s q) AI
      eqI = trans (Pr₁-bind (idealK s q) KI)
                  (lookupᴰℚ-Dmap fI (respB s q) (λ sr → Pr₁ (KI sr)))

      eqR : Pr₁ (runWith realK s (ask q k)) ≡ E (respB s q) AR
      eqR = trans (Pr₁-bind (realK s q) KR)
                  (lookupᴰℚ-Dmap fR (respB s q) (λ sr → Pr₁ (KR sr)))

      eqB : E (realK s q) (λ sr → badProb realK bad (proj₁ sr) (k (proj₂ sr)))
          ≡ E (respB s q) BB
      eqB = lookupᴰℚ-Dmap fR (respB s q)
              (λ sr → badProb realK bad (proj₁ sr) (k (proj₂ sr)))

      pointwise : ∀ t → ∣ AI t -ℚ AR t ∣ℚ ≤ℚ BB t
      pointwise t with bad (proj₁ t) in eqt
      ... | false = FLGP (proj₁ t) (k (proj₁ (proj₂ t)))
      ... | true  =
        subst (λ z → ∣ Pr₁ (KI (proj₁ t , proj₂ (proj₂ t))) -ℚ AR t ∣ℚ ≤ℚ z)
              (sym (badProb-bad realK bad (proj₁ t) (k (proj₁ (proj₂ t))) eqt))
              (∣Pr-Pr∣≤1 (KI (proj₁ t , proj₂ (proj₂ t))) (KR (fR t)))
  -- A coin is a convex combination of the branches: neither world's state
  -- moves, so the advantage averages and the bad-probability averages with it.
  FLGP s (coin μ k) with bad s
  ... | true  = ∣Pr-Pr∣≤1 (runWith idealK s (coin μ k)) (runWith realK s (coin μ k))
  ... | false =
      ≤-trans (≤-reflexive (cong₂ (λ x y → ∣ x -ℚ y ∣ℚ)
                             (Pr₁-bind μ (λ b → runWith idealK s (k b)))
                             (Pr₁-bind μ (λ b → runWith realK s (k b)))))
     (≤-trans (E-abs-diff μ AI AR)
              (E-mono μ (λ b → ∣ AI b -ℚ AR b ∣ℚ) BB (λ b → FLGP s (k b))))
    where
      AI AR BB : Bool → ℚ
      AI b = Pr₁ (runWith idealK s (k b))
      AR b = Pr₁ (runWith realK  s (k b))
      BB b = badProb realK bad s (k b)
