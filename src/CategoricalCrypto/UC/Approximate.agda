{-# OPTIONS --safe --without-K #-}

-- The two-argument bounds held to `Negligible`
-- (`ProbabilisticLogic.Distribution.Uniform.Decay`).  The error algebra these
-- bounds are measured in is `Approx.Error`.

open import Data.Nat.Base as ℕ using (ℕ)
open import Data.Nat.Poly
open import Data.Nat.Positive
open import Data.Product.Base
open import Data.Rational as ℚ
open import Level using (Level)

open import ProbabilisticLogic.Distribution.Uniform.Decay

module CategoricalCrypto.UC.Approximate where

-- The discipline asked of a concrete two-argument bound: it is
-- admitted when `ε(n, p n)` is NEGLIGIBLE at every polynomial allowance `p`,
-- which is what the model's own allowance supplies (`UC.Family`'s `Poly⁺`
-- admissibility).  It yields no single slack uniform over arbitrary, possibly
-- exponential, `q`.
NegligibleBound : (ℕ → ℕ → ℚ) → Set
NegligibleBound ε = (p : ℕ → ℕ) → Poly p → Negligible (λ n → ε n (p n))

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
-- adds `δ`, read at the allowance, to the slack, so the moved statement is
-- negligible exactly because `Negligible` is closed under sums
-- (`Negligible-+`) and reading a sum at the allowance is the sum of the two
-- readings.  The two bounds are EXPLICIT: a `NegligibleBound` reads its
-- bound at an allowance, so no value of one determines it by unification.
NegligibleBound-+ : (ε δ : ℕ → ℕ → ℚ) → NegligibleBound ε → NegligibleBound δ
                  → NegligibleBound (λ n q → ε n q ℚ.+ δ n q)
NegligibleBound-+ ε δ bε bδ p Pp = Negligible-+ (bε p Pp) (bδ p Pp)

-- …and closure under rescaling the allowance.  A composition that moves a
-- morphism into a context rescales the allowance the moved-into leg affords
-- (`Data.Nat.Positive.scale`), so the bound it concludes with is the old one
-- read at `scale q (r n)` rather than at `q`: still negligible, since that is
-- polynomial in its allowance whenever `r` is — nothing here assumes `ε` is
-- monotone in the allowance.
NegligibleBound-scale : (r : ℕ → ℕ⁺) → Poly⁺ r → (ε : ℕ → ℕ → ℚ)
                      → NegligibleBound ε → NegligibleBound (λ n q → ε n (scale q (r n)))
NegligibleBound-scale r Pr _ b p Pp = b (λ n → scale (p n) (r n)) (poly-scale {p} {r} Pp Pr)
