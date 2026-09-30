{-# OPTIONS --safe --without-K #-}

-- The quantitative side of a readout: closeness at a measurable error, and
-- what that costs.
--
-- `Approximation` is closeness itself, over an error signature and nothing
-- more.  `_∼ᵃ_`, closeness at EVERY positive error, is the qualitative
-- equivalence it collapses to; that collapse is the only consumer of
-- positivity, so it takes a `Refinement` of the errors separately, and the
-- ε/2 argument for its transitivity is proved once, here, against it.
-- Packaging it against a category — a quantitative readout, and the two
-- qualitative readouts it induces — is `Approx.Evaluation`; the intended `Dₚ`
-- model and the asymptotic family (`UC.Machine`, `UC.Family`) both arrive
-- there.
--
-- `Negligible` sits beside `_→0` because a cryptographic bound has to beat
-- every inverse polynomial and mere convergence does not — `1/n` is `_→0`
-- (proposal §3, `docs/kb/frontier/15-probabilistic-uc-model.typ`).

open import Data.Integer.Base using (+_)
open import Data.Nat.Base as ℕ using (ℕ)
open import Data.Nat.Poly using (Poly; poly-const)
open import Data.Nat.Properties using (m≤m⊔n; m≤n⊔m; ≤-trans)
open import Data.Product.Base using (Σ-syntax; _×_; _,_)
open import Data.Rational as ℚ using (ℚ; 0ℚ; ½; _/_)
open import Data.Rational.Properties
  using ( *-distribˡ-+; *-distribʳ-+; *-identityˡ; *-monoʳ-<-pos; *-zeroʳ; +-mono-≤
        ; <⇒≤; ≤-reflexive )
open import Level using (Level; 0ℓ; _⊔_; suc)
open import Relation.Binary.PropositionalEquality using (_≡_; subst; sym; trans)
open import Relation.Binary.Structures using (IsEquivalence)

module CategoricalCrypto.UC.Approximate where

private variable os es ℓe ℓa : Level

------------------------------------------------------------------------
-- Errors

-- What an approximate observation measures its slack in.
record ErrorAlgebra (es ℓe : Level) : Set (suc (es ⊔ ℓe)) where
  infixl 6 _⊕_
  infix 4 _⊑_

  field
    Error : Set es
    ε₀    : Error
    _⊕_   : Error → Error → Error
    _⊑_   : Error → Error → Set ℓe

-- Tolerances small enough to collapse at: each positive one lies above zero and
-- splits into two positive ones whose sum is below it.  That split is the
-- whole ε/2 argument; `halving` is the usual way to supply it.
record Refinement {es ℓe : Level} (E : ErrorAlgebra es ℓe) : Set (es ⊔ suc ℓe) where
  open ErrorAlgebra E

  field
    Positive : Error → Set ℓe
    ε₀-least : {ε : Error} → Positive ε → ε₀ ⊑ ε
    refine   : {ε : Error} → Positive ε
             → Σ[ δ ∈ Error ] Σ[ δ′ ∈ Error ] Positive δ × Positive δ′ × δ ⊕ δ′ ⊑ ε

module _ {E : ErrorAlgebra es ℓe} where
  open ErrorAlgebra E

  halving : (Positive : Error → Set ℓe) → ({ε : Error} → Positive ε → ε₀ ⊑ ε)
          → (half : Error → Error) → ({ε : Error} → Positive ε → Positive (half ε))
          → ((ε : Error) → half ε ⊕ half ε ⊑ ε) → Refinement E
  halving Positive ε₀-least half half-pos half-sum = record
    { Positive = Positive
    ; ε₀-least = ε₀-least
    ; refine   = λ {ε} pos → half ε , half ε , half-pos pos , half-pos pos , half-sum ε
    }

private
  half-positive : {ε : ℚ} → 0ℚ ℚ.< ε → 0ℚ ℚ.< ½ ℚ.* ε
  half-positive {ε} ε>0 = subst (ℚ._< ½ ℚ.* ε) (*-zeroʳ ½) (*-monoʳ-<-pos ½ ε>0)

  half+half : (ε : ℚ) → ½ ℚ.* ε ℚ.+ ½ ℚ.* ε ≡ ε
  half+half ε = trans (sym (*-distribʳ-+ ε ½ ½)) (*-identityˡ ε)

ℚ-errors : ErrorAlgebra 0ℓ 0ℓ
ℚ-errors = record { Error = ℚ ; ε₀ = 0ℚ ; _⊕_ = ℚ._+_ ; _⊑_ = ℚ._≤_ }

ℚ-refinement : Refinement ℚ-errors
ℚ-refinement =
  halving (0ℚ ℚ.<_) <⇒≤ (½ ℚ.*_) half-positive (λ ε → ≤-reflexive (half+half ε))

-- Vanishing, and the shape a concrete security bound has: an error vanishing in
-- the security parameter at every polynomial budget.  This is what the
-- asymptotic layer closes over (`UC.Family.absorb`).
infix 4 _→0

_→0 : (ℕ → ℚ) → Set
s →0 = (ε : ℚ) → 0ℚ ℚ.< ε → Σ[ N ∈ ℕ ] ((n : ℕ) → N ℕ.≤ n → s n ℚ.≤ ε)

-- The grade a slack or an error is held to — a decay class, unrelated to the
-- UC grade an adversary interface is.  The two bound disciplines below are one
-- shape at two grades, and a consumer that works for either states itself over
-- `Grade` and takes the closure it spends as an argument.
Grade : Set₁
Grade = (ℕ → ℚ) → Set

GradedBound : Grade → (ℕ → ℕ → ℚ) → Set
GradedBound G ε = (p : ℕ → ℕ) → Poly p → G (λ n → ε n (p n))

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
  let Ns , bs = s→0 (½ ℚ.* ε) (half-positive ε>0)
      Nt , bt = t→0 (½ ℚ.* ε) (half-positive ε>0)
  in Ns ℕ.⊔ Nt , λ n le → subst (s n ℚ.+ t n ℚ.≤_) (half+half ε)
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

------------------------------------------------------------------------
-- Approximate closeness

record Approximation (Obs : Set os) (E : ErrorAlgebra es ℓe) (ℓa : Level)
                   : Set (os ⊔ es ⊔ ℓe ⊔ suc ℓa) where
  open ErrorAlgebra E public

  infix 4 _≈[_]_

  field
    _≈[_]_    : Obs → Error → Obs → Set ℓa
    ≈[]-refl  : {x : Obs} → x ≈[ ε₀ ] x
    ≈[]-sym   : {x y : Obs} {ε : Error} → x ≈[ ε ] y → y ≈[ ε ] x
    ≈[]-trans : {x y z : Obs} {ε δ : Error} → x ≈[ ε ] y → y ≈[ δ ] z → x ≈[ ε ⊕ δ ] z
    ≈[]-mono  : {x y : Obs} {ε δ : Error} → ε ⊑ δ → x ≈[ ε ] y → x ≈[ δ ] y

-- No positive error separates the two.  This is the relation a qualitative
-- observation exposes; at the asymptotic instance it is vanishing advantage.
module AllPositive {E : ErrorAlgebra es ℓe} (R : Refinement E)
                   {Obs : Set os} (A : Approximation Obs E ℓa) where
  open Refinement R
  open Approximation A

  infix 4 _∼ᵃ_

  _∼ᵃ_ : Obs → Obs → Set (es ⊔ ℓe ⊔ ℓa)
  x ∼ᵃ y = (ε : Error) → Positive ε → x ≈[ ε ] y

  ∼ᵃ-isEquivalence : IsEquivalence _∼ᵃ_
  ∼ᵃ-isEquivalence = record
    { refl  = λ _ pos → ≈[]-mono (ε₀-least pos) ≈[]-refl
    ; sym   = λ h ε pos → ≈[]-sym (h ε pos)
    ; trans = λ h k ε pos →
        let δ , δ′ , pδ , pδ′ , le = refine pos in ≈[]-mono le (≈[]-trans (h δ pδ) (k δ′ pδ′))
    }

  zero⇒positive : {x y : Obs} → x ≈[ ε₀ ] y → x ∼ᵃ y
  zero⇒positive h _ pos = ≈[]-mono (ε₀-least pos) h
