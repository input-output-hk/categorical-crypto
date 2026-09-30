{-# OPTIONS --safe --without-K #-}

-- Decay classes of rational sequences, and the bounds graded by them.
--
-- `Negligible` sits beside `_→0` because a cryptographic bound has to beat
-- every inverse polynomial and mere convergence does not — `1/n` is `_→0`
-- (proposal §3, `docs/kb/frontier/15-probabilistic-uc-model.typ`).  The error
-- algebra these bounds are measured in is `Approx.Error`.

open import Data.Integer.Base using (+_)
open import Data.Nat.Base as ℕ using (ℕ)
open import Data.Nat.Poly using (Poly; poly-const)
open import Data.Nat.Properties using (m≤m⊔n; m≤n⊔m; ≤-trans)
open import Data.Product.Base using (_,_)
open import Data.Rational as ℚ using (ℚ; 0ℚ; ½; _/_)
open import Data.Rational.Properties using (*-distribˡ-+; *-identityˡ; *-zeroʳ; +-mono-≤; <⇒≤)
open import Data.Rational.Properties.Ext using (0<½*; ½*+½*)
open import Relation.Binary.PropositionalEquality using (_≡_; subst; sym)

open import ProbabilisticLogic.Distribution.Uniform.Decay using (_→0)

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

-- Negligible: eventually below every inverse polynomial, which is strictly more
-- than `_→0` (`1/n` vanishes and is not negligible).  Stated by MAGNIFICATION —
-- every polynomially magnified copy still vanishes — rather than as
-- `s n ≤ 1/p n`: the same condition, reusing `Poly` and `_→0` instead of a
-- second ε-quantifier, and with no nonzero-denominator side condition in the
-- statement.
Negligible : (ℕ → ℚ) → Set
Negligible s = (p : ℕ → ℕ) → Poly p → (λ n → (+ p n / 1) ℚ.* s n) →0

Negligible⇒→0 : {s : ℕ → ℚ} → Negligible s → s →0
Negligible⇒→0 {s} neg ε ε>0 =
  let N , bnd = neg (λ _ → 1) (poly-const 1) ε ε>0
  in N , λ n le → subst (ℚ._≤ ε) (*-identityˡ (s n)) (bnd n le)

-- The discipline the proposal asks of a concrete two-argument bound (§3): it is
-- admitted when `ε(n, p n)` is NEGLIGIBLE at every polynomial allowance `p`,
-- which is what the model's own allowance supplies (`UC.Family`'s `Poly⁺`
-- admissibility).  It yields no single slack uniform over arbitrary, possibly
-- exponential, `q`.
NegligibleBound : (ℕ → ℕ → ℚ) → Set
NegligibleBound = GradedBound Negligible

NegligibleBound⇒VanishingBound : {ε : ℕ → ℕ → ℚ} → NegligibleBound ε → VanishingBound ε
NegligibleBound⇒VanishingBound neg p Pp = Negligible⇒→0 (neg p Pp)

------------------------------------------------------------------------
-- Closure

-- What a transfer spends.  Moving a bound along a system that differs by `δ`
-- adds `δ`, read at the allowance, to the slack, so the moved statement has
-- the same grade exactly when the grade is closed under sums — and reading a
-- `GradedBound` at the allowance is already that grade, by definition.  Both
-- grades close, `Negligible`'s case being the vanishing one under the
-- magnifying polynomial.

→0-cong : {s t : ℕ → ℚ} → ((n : ℕ) → s n ≡ t n) → s →0 → t →0
→0-cong eq s→0 ε ε>0 =
  let N , bnd = s→0 ε ε>0 in N , λ n le → subst (ℚ._≤ ε) (eq n) (bnd n le)

→0-0 : (λ (_ : ℕ) → 0ℚ) →0
→0-0 _ ε>0 = 0 , λ _ _ → <⇒≤ ε>0

→0-+ : {s t : ℕ → ℚ} → s →0 → t →0 → (λ n → s n ℚ.+ t n) →0
→0-+ {s} {t} s→0 t→0 ε ε>0 =
  let Ns , bs = s→0 (½ ℚ.* ε) (0<½* ε>0)
      Nt , bt = t→0 (½ ℚ.* ε) (0<½* ε>0)
  in Ns ℕ.⊔ Nt , λ n le → subst (s n ℚ.+ t n ℚ.≤_) (½*+½* ε)
       (+-mono-≤ (bs n (≤-trans (m≤m⊔n Ns Nt) le)) (bt n (≤-trans (m≤n⊔m Ns Nt) le)))

Negligible-0 : Negligible (λ _ → 0ℚ)
Negligible-0 p _ = →0-cong (λ n → sym (*-zeroʳ (+ p n / 1))) →0-0

Negligible-+ : {s t : ℕ → ℚ} → Negligible s → Negligible t → Negligible (λ n → s n ℚ.+ t n)
Negligible-+ {s} {t} ns nt p Pp =
  →0-cong (λ n → sym (*-distribˡ-+ (+ p n / 1) (s n) (t n))) (→0-+ (ns p Pp) (nt p Pp))

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
