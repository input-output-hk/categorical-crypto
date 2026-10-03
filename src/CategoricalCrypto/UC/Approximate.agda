{-# OPTIONS --safe --without-K #-}

-- The bounds graded by a decay class of rational sequences (`_→0`,
-- `Negligible`: `ProbabilisticLogic.Distribution.Uniform.Decay`).  The error
-- algebra these bounds are measured in is `Approx.Error`.

open import Data.Nat.Base as ℕ using (ℕ)
open import Data.Nat.Poly
open import Data.Nat.Positive
open import Data.Product.Base
open import Data.Rational as ℚ
open import Level using (Level)

open import ProbabilisticLogic.Distribution.Uniform.Decay

module CategoricalCrypto.UC.Approximate where

-- The grade a slack or an error is held to — a decay class, unrelated to the
-- UC grade an adversary interface is.  The two bound disciplines below are one
-- shape at two grades, and a consumer that works for either states itself over
-- `Grade` and takes the closure it spends as an argument.
Grade : Set₁
Grade = (ℕ → ℚ) → Set

GradedBound : Grade → (ℕ → ℕ → ℚ) → Set
GradedBound G ε = (p : ℕ → ℕ) → Poly p → G (λ n → ε n (p n))

-- The shape a concrete security bound has: an error vanishing in the security
-- parameter at every polynomial budget.  This is what the asymptotic layer
-- closes over (`UC.Family.absorb`).
VanishingBound : (ℕ → ℕ → ℚ) → Set
VanishingBound = GradedBound _→0

-- The discipline asked of a concrete two-argument bound: it is
-- admitted when `ε(n, p n)` is NEGLIGIBLE at every polynomial allowance `p`,
-- which is what the model's own allowance supplies (`UC.Family`'s `Poly⁺`
-- admissibility).  It yields no single slack uniform over arbitrary, possibly
-- exponential, `q`.
NegligibleBound : (ℕ → ℕ → ℚ) → Set
NegligibleBound = GradedBound Negligible

-- One negligible slack per polynomial cap, chosen before the security
-- parameter.
Saturated : {ℓ : Level} → (ℕ → ℕ → ℚ → Set ℓ) → (ℕ → ℕ → ℚ) → Set ℓ
Saturated X ε = (p : ℕ → ℕ) → Poly p
              → Σ[ ν ∈ (ℕ → ℚ) ] Negligible ν × ((n : ℕ) → X n (p n) (ε n (p n) ℚ.+ ν n))

saturated-map : {ℓ ℓ′ : Level} {X : ℕ → ℕ → ℚ → Set ℓ} {Y : ℕ → ℕ → ℚ → Set ℓ′} {ε : ℕ → ℕ → ℚ}
              → ((n q : ℕ) {r : ℚ} → X n q r → Y n q r) → Saturated X ε → Saturated Y ε
saturated-map g h p Pp = let ν , neg , b = h p Pp in ν , neg , λ n → g n (p n) (b n)

------------------------------------------------------------------------
-- Closure

-- What a transfer spends.  Moving a bound along a system that differs by `δ`
-- adds `δ`, read at the allowance, to the slack, so the moved statement has
-- the same grade exactly when the grade is closed under sums — and reading a
-- `GradedBound` at the allowance is already that grade, by definition.  Both
-- grades close, `Negligible`'s case being the vanishing one under the
-- magnifying polynomial.

-- …and the two-argument discipline inherits it: reading a sum at the allowance
-- is the sum of the two readings, so the grade's own closure is all it costs.
-- Both grades qualify, `→0-+` and `Negligible-+` being the two arguments.
-- The two bounds are EXPLICIT: a `GradedBound` reads its bound at an
-- allowance, so no value of one determines it by unification.
GradedBound-+[_] : (G : Grade)
                 → ({s t : ℕ → ℚ} → G s → G t → G (λ n → s n ℚ.+ t n))
                 → (ε δ : ℕ → ℕ → ℚ) → GradedBound G ε → GradedBound G δ
                 → GradedBound G (λ n q → ε n q ℚ.+ δ n q)
GradedBound-+[ G ] G-+ ε δ bε bδ p Pp = G-+ (bε p Pp) (bδ p Pp)

-- …and closure under REINDEXING the allowance.  A composition that moves a
-- morphism into a context rescales the allowance the moved-into leg affords
-- (`Data.Nat.Positive.scale`), so the bound it concludes with is the old one
-- read at `r n q` rather than at `q`.  That is a bound of the same grade exactly when
-- `r` preserves polynomials, which is the only thing a `GradedBound` ever asks
-- of its argument — nothing here assumes `ε` is monotone in the allowance.
GradedBound-reindex : (G : Grade) (r : ℕ → ℕ → ℕ)
                    → ((p : ℕ → ℕ) → Poly p → Poly (λ n → r n (p n)))
                    → (ε : ℕ → ℕ → ℚ) → GradedBound G ε
                    → GradedBound G (λ n q → ε n (r n q))
GradedBound-reindex _ r pres _ b p Pp = b (λ n → r n (p n)) (pres p Pp)

-- …at `Negligible` along `scale _ r`, which is polynomial in its allowance
-- whenever `r` is.
NegligibleBound-scale : (r : ℕ → ℕ⁺) → Poly⁺ r → (ε : ℕ → ℕ → ℚ)
                      → NegligibleBound ε → NegligibleBound (λ n q → ε n (scale q (r n)))
NegligibleBound-scale r Pr =
  GradedBound-reindex Negligible (λ n q → scale q (r n)) (λ p Pp → poly-scale {p} {r} Pp Pr)
