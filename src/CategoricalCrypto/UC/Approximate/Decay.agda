{-# OPTIONS --safe --without-K #-}

-- Negligibility of an exponentially decaying bound: a polynomial numerator
-- against `2^-sch(n)`, at a schedule keeping up with the security parameter.
--
-- `Uniform.Decay` proves the vanishing half generically.  `Negligible` is
-- vanishing after a polynomial MAGNIFICATION (`UC.Approximate`), so the two
-- meet by feeding the magnifier into the numerator, which is polynomial again;
-- `fromℕ` is the semiring map that lets it in.  Nothing here is specific to a
-- birthday bound — `t` is any level-indexed numerator polynomial in the
-- allowance — and `negligibleBound-inv-pow-2` is the shape a concrete
-- `NegligibleBound` obligation has.

open import Data.Integer.Base using (+_)
open import Data.Nat.Base as ℕ using (ℕ)
open import Data.Nat.Poly using (Poly; poly-*; poly-const)
open import Data.Rational as ℚ using (ℚ; 0ℚ; 1ℚ; nonNegative)
open import Data.Rational.Properties
  using (*-assoc; *-identityˡ; *-monoˡ-≤-nonNeg; positive⁻¹)
open import Data.Rational.Properties.Ext using (0<½*)
open import Relation.Binary.PropositionalEquality using (_≡_; cong; subst; trans)

open import ProbabilisticLogic.Distribution.Uniform
  using (fromℕ; inv-pow-2; fromℕ-*; fromℕ-/; 0≤fromℕ)
open import ProbabilisticLogic.Distribution.Uniform.Decay
  using (poly-inv-pow-2-→0; →0-≤)

open import CategoricalCrypto.UC.Approximate
  using (Negligible; NegligibleBound; →0-cong)

module CategoricalCrypto.UC.Approximate.Decay where

private variable p r sch : ℕ → ℕ
                 s u : ℕ → ℚ
                 t : ℕ → ℕ → ℕ

------------------------------------------------------------------------
-- Closure

Negligible-cong : ((n : ℕ) → s n ≡ u n) → Negligible s → Negligible u
Negligible-cong eq neg r Pr = →0-cong (λ n → cong ((+ r n ℚ./ 1) ℚ.*_) (eq n)) (neg r Pr)

-- Negligibility is a BOUND, so it passes to anything dominated pointwise: the
-- magnified copies are dominated too, the magnifier being nonnegative.
Negligible-≤ : ((n : ℕ) → s n ℚ.≤ u n) → Negligible u → Negligible s
Negligible-≤ {s} {u} s≤u neg r Pr = →0-≤ mono (neg r Pr)
  where
  mono : (n : ℕ) → (+ r n ℚ./ 1) ℚ.* s n ℚ.≤ (+ r n ℚ./ 1) ℚ.* u n
  mono n = subst (λ z → z ℚ.* s n ℚ.≤ z ℚ.* u n) (fromℕ-/ (r n))
             (*-monoˡ-≤-nonNeg (fromℕ (r n)) ⦃ nonNegative (0≤fromℕ (r n)) ⦄ (s≤u n))

------------------------------------------------------------------------
-- The exponential schedule

-- `2^-sch(j)` at a polynomial numerator, magnified by one more polynomial: the
-- product of the two numerators is the polynomial `Uniform.Decay` wants.
negligible-inv-pow-2 : Poly p → ((j : ℕ) → j ℕ.≤ sch j)
                     → Negligible (λ j → fromℕ (p j) ℚ.* inv-pow-2 (sch j))
negligible-inv-pow-2 {p} {sch} Pp j≤sch r Pr =
  →0-cong scale (poly-inv-pow-2-→0 (poly-* Pr Pp) j≤sch)
  where
  scale : (j : ℕ) → fromℕ (r j ℕ.* p j) ℚ.* inv-pow-2 (sch j)
                  ≡ (+ r j ℚ./ 1) ℚ.* (fromℕ (p j) ℚ.* inv-pow-2 (sch j))
  scale j = trans (cong (ℚ._* inv-pow-2 (sch j)) (fromℕ-* (r j) (p j)))
              (trans (*-assoc (fromℕ (r j)) (fromℕ (p j)) (inv-pow-2 (sch j)))
                     (cong (ℚ._* (fromℕ (p j) ℚ.* inv-pow-2 (sch j))) (fromℕ-/ (r j))))

-- …and the two-argument discipline: a numerator polynomial in the allowance at
-- each level is a `NegligibleBound`.
negligibleBound-inv-pow-2 : ((q : ℕ → ℕ) → Poly q → Poly (λ j → t j (q j)))
                          → ((j : ℕ) → j ℕ.≤ sch j)
                          → NegligibleBound (λ j q → fromℕ (t j q) ℚ.* inv-pow-2 (sch j))
negligibleBound-inv-pow-2 Pt j≤sch q Pq = negligible-inv-pow-2 (Pt q Pq) j≤sch

-- The slack a carry spends: negligible, and POSITIVE at every level — an
-- ε-quantified agreement has no zero instance to give, so a carry that turns
-- one into a bound must name a positive slack per level.
negligible-slack : ((j : ℕ) → j ℕ.≤ sch j) → Negligible (λ j → inv-pow-2 (sch j))
negligible-slack {sch} j≤sch =
  Negligible-cong (λ j → *-identityˡ (inv-pow-2 (sch j)))
                  (negligible-inv-pow-2 (poly-const 1) j≤sch)

0<inv-pow-2 : (k : ℕ) → 0ℚ ℚ.< inv-pow-2 k
0<inv-pow-2 ℕ.zero    = positive⁻¹ 1ℚ
0<inv-pow-2 (ℕ.suc k) = 0<½* (0<inv-pow-2 k)
