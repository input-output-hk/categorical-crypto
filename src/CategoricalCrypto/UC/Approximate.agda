{-# OPTIONS --safe --without-K #-}

-- The quantitative enrichment of a qualitative observation.
--
-- `UC.Core.Observation` compares two closed runs by an equivalence and says
-- nothing numerical.  A model may know more: that two runs are close to within
-- a measurable error, and that an error small enough is no difference at all.
-- Those two are `Approximation` and `induces`, and together they run the arrow
--
--     quantitative closeness at every positive error
--                      │  induces
--                      ▼
--            qualitative observational equivalence
--
-- in both readings.  `ApproximateObservation` enriches an observation that
-- already exists, with `induces` as the field connecting the two;
-- `Induced.observation` goes the other way and CONSTRUCTS an observation out of
-- an approximation — its `_∼_` is closeness at every positive error, and the
-- ε/2 argument for transitivity is proved once, here, over an abstract error
-- algebra.  The intended `Dₚ` model and the asymptotic family (`UC.Machine`,
-- `UC.Family`) both arrive by the second route.
--
-- The error object is NOT fixed by the interface: `ErrorAlgebra` is what the
-- ε/2 argument needs of it and no more (a zero, an addition, an order, a
-- positivity predicate and a halving).  `ℚ-errors` is the rational instance
-- both current models use; another model may measure error differently, or
-- offer no quantitative enrichment at all.
--
-- `Negligible` sits beside `_→0` because a cryptographic bound has to beat
-- every inverse polynomial and mere convergence does not — `1/n` is `_→0`
-- (proposal §3, `docs/kb/frontier/15-probabilistic-uc-model.typ`).

open import Categories.Category using (Category; _[_,_]; _[_≈_])

open import Data.Integer.Base using (+_)
open import Data.Nat.Base as ℕ using (ℕ)
open import Data.Nat.Poly using (Poly; poly-const)
open import Data.Nat.Properties using (m≤m⊔n; m≤n⊔m; ≤-trans)
open import Data.Product.Base using (Σ-syntax; _,_)
open import Data.Rational as ℚ using (ℚ; 0ℚ; ½; _/_)
open import Data.Rational.Properties
  using ( *-distribˡ-+; *-distribʳ-+; *-identityˡ; *-monoʳ-<-pos; *-zeroʳ; +-mono-≤
        ; <⇒≤; ≤-reflexive )
open import Level using (Level; 0ℓ; _⊔_; suc)
open import Relation.Binary.PropositionalEquality using (_≡_; subst; sym; trans)
open import Relation.Binary.Structures using (IsEquivalence)

open import CategoricalCrypto.UC.Core using (Observation)

module CategoricalCrypto.UC.Approximate where

private variable os ℓs es ℓe ℓa : Level

------------------------------------------------------------------------
-- Errors

-- What an approximate observation measures its slack in: exactly the structure
-- the ε/2 argument spends.
record ErrorAlgebra (es ℓe : Level) : Set (suc (es ⊔ ℓe)) where
  infixl 6 _⊕_
  infix 4 _⊑_

  field
    Error    : Set es
    ε₀       : Error
    _⊕_      : Error → Error → Error
    _⊑_      : Error → Error → Set ℓe
    Positive : Error → Set ℓe
    half     : Error → Error

    ε₀-least : {ε : Error} → Positive ε → ε₀ ⊑ ε
    half-pos : {ε : Error} → Positive ε → Positive (half ε)
    half-sum : (ε : Error) → half ε ⊕ half ε ⊑ ε

private
  half-positive : {ε : ℚ} → 0ℚ ℚ.< ε → 0ℚ ℚ.< ½ ℚ.* ε
  half-positive {ε} ε>0 = subst (ℚ._< ½ ℚ.* ε) (*-zeroʳ ½) (*-monoʳ-<-pos ½ ε>0)

  half+half : (ε : ℚ) → ½ ℚ.* ε ℚ.+ ½ ℚ.* ε ≡ ε
  half+half ε = trans (sym (*-distribʳ-+ ε ½ ½)) (*-identityˡ ε)

ℚ-errors : ErrorAlgebra 0ℓ 0ℓ
ℚ-errors = record
  { Error    = ℚ
  ; ε₀       = 0ℚ
  ; _⊕_      = ℚ._+_
  ; _⊑_      = ℚ._≤_
  ; Positive = 0ℚ ℚ.<_
  ; half     = ½ ℚ.*_
  ; ε₀-least = <⇒≤
  ; half-pos = half-positive
  ; half-sum = λ ε → ≤-reflexive (half+half ε)
  }

-- Vanishing, and the shape a concrete security bound has: an error vanishing in
-- the security parameter at every polynomial budget.  This is what the
-- asymptotic layer closes over (`UC.Family.absorb`).
infix 4 _→0

_→0 : (ℕ → ℚ) → Set
s →0 = (ε : ℚ) → 0ℚ ℚ.< ε → Σ[ N ∈ ℕ ] ((n : ℕ) → N ℕ.≤ n → s n ℚ.≤ ε)

-- The grade a slack or an error is held to — a decay class, unrelated to
-- `UC.Core.Grading`.  The two bound disciplines below are one shape at two
-- grades, and a consumer that works for either states itself over `Grade` and
-- takes the closure it spends as an argument (`UC.Saturated`).
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
-- which is what the model's own allowance supplies (`UC.Family.PolyQB`).  It
-- yields no single slack uniform over arbitrary, possibly exponential, `q`.
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
-- The two bounds are EXPLICIT, as they are in `UC.Saturated`'s statements and
-- for the same reason: a `GradedBound` reads its bound at an allowance, so no
-- value of one determines it by unification.
GradedBound-+[_] : (G : Grade)
                 → ({s t : ℕ → ℚ} → G s → G t → G (λ n → s n ℚ.+ t n))
                 → (ε δ : ℕ → ℕ → ℚ) → GradedBound G ε → GradedBound G δ
                 → GradedBound G (λ n q → ε n q ℚ.+ δ n q)
GradedBound-+[ G ] G-+ ε δ bε bδ p Pp = G-+ (bε p Pp) (bδ p Pp)

-- …and closure under REINDEXING the allowance.  A composition that moves a
-- morphism into a context rescales the allowance the moved-into leg affords
-- (`UC.Budget.simCost`), so the bound it concludes with is the old one read at
-- `r n q` rather than at `q`.  That is a bound of the same grade exactly when
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

  infix 4 _≈[_]_ _∼ᵃ_

  field
    _≈[_]_    : Obs → Error → Obs → Set ℓa
    ≈[]-refl  : {x : Obs} → x ≈[ ε₀ ] x
    ≈[]-sym   : {x y : Obs} {ε : Error} → x ≈[ ε ] y → y ≈[ ε ] x
    ≈[]-trans : {x y z : Obs} {ε δ : Error} → x ≈[ ε ] y → y ≈[ δ ] z → x ≈[ ε ⊕ δ ] z
    ≈[]-mono  : {x y : Obs} {ε δ : Error} → ε ⊑ δ → x ≈[ ε ] y → x ≈[ δ ] y

  -- No positive error separates the two.  This is the relation a qualitative
  -- observation exposes; at the asymptotic instance it is vanishing advantage.
  _∼ᵃ_ : Obs → Obs → Set (es ⊔ ℓe ⊔ ℓa)
  x ∼ᵃ y = (ε : Error) → Positive ε → x ≈[ ε ] y

  ∼ᵃ-isEquivalence : IsEquivalence _∼ᵃ_
  ∼ᵃ-isEquivalence = record
    { refl  = λ _ pos → ≈[]-mono (ε₀-least pos) ≈[]-refl
    ; sym   = λ h ε pos → ≈[]-sym (h ε pos)
    ; trans = λ h k ε pos → ≈[]-mono (half-sum ε)
        (≈[]-trans (h (half ε) (half-pos pos)) (k (half ε) (half-pos pos)))
    }

-- The enrichment: an observation that already exists, refined by a measurable
-- error whose vanishing implies its equivalence.
record ApproximateObservation {o ℓ e} {𝒞 : Category o ℓ e} (O : Observation 𝒞 os ℓs)
                              (E : ErrorAlgebra es ℓe) (ℓa : Level)
                            : Set (ℓ ⊔ e ⊔ os ⊔ ℓs ⊔ es ⊔ ℓe ⊔ suc ℓa) where
  open Category 𝒞
  open Observation O
  field approx : Approximation Obs E ℓa
  open Approximation approx public

  field
    induces : {x y : Obs} → x ∼ᵃ y → x ∼ y
    -- The ambient hom equality is observed EXACTLY, where `⟦⟧-resp-≈` only
    -- says it is observed up to every positive error.  The asymptotic
    -- construction spends this: an error that vanishes has to start at zero
    -- for a hom equality (`UC.Family.Approximation^ω`).
    ⟦⟧-resp-≈₀ : {u v : 𝟙 ⇒ Ω} → u ≈ v → ⟦ u ⟧ ≈[ ε₀ ] ⟦ v ⟧

-- …and the constructor: an approximation of what closed runs show, plus the
-- runs themselves, IS a qualitative observation, enriched by construction.
module Induced {o ℓ e os es ℓe ℓa} (𝒞 : Category o ℓ e) {Obs : Set os}
               {E : ErrorAlgebra es ℓe} (A : Approximation Obs E ℓa)
               (𝟙 Ω : Category.Obj 𝒞) (⟦_⟧ : 𝒞 [ 𝟙 , Ω ] → Obs)
               (resp : {u v : 𝒞 [ 𝟙 , Ω ]} → 𝒞 [ u ≈ v ]
                     → Approximation._≈[_]_ A ⟦ u ⟧ (Approximation.ε₀ A) ⟦ v ⟧) where
  open Approximation A

  observation : Observation 𝒞 os (es ⊔ ℓe ⊔ ℓa)
  observation = record
    { 𝟙 = 𝟙 ; Ω = Ω ; Obs = Obs ; ⟦_⟧ = ⟦_⟧
    ; _∼_ = _∼ᵃ_
    ; ∼-isEquivalence = ∼ᵃ-isEquivalence
    ; ⟦⟧-resp-≈ = λ eq _ pos → ≈[]-mono (ε₀-least pos) (resp eq)
    }

  approximate : ApproximateObservation observation E ℓa
  approximate = record { approx = A ; induces = λ h → h ; ⟦⟧-resp-≈₀ = resp }

------------------------------------------------------------------------
-- A one-sided reading

-- `Observation` deliberately compares observations without valuing one, which
-- is what keeps it inhabited at `Dₚ` (whose termination mass is a supremum the
-- layer never forms).  A BOUND on a single observation — what an audit-form
-- security statement is — needs exactly this much more and no more: a budgeted
-- value, and that an agreement dominates it up to any positive slack.  At the
-- intended instance `at` is `Pr≤` and `dominate` is the left half of `_≈ₚ[_]_`
-- (`UC.Seam.Audit.massᴹ`), so nothing new is assumed.
record Mass {o ℓ e} {𝒞 : Category o ℓ e} (O : Observation 𝒞 os ℓs)
          : Set (os ⊔ ℓs) where
  open Observation O

  field
    at       : ℕ → Obs → ℚ
    dominate : {x y : Obs} → x ∼ y → (δ : ℚ) → 0ℚ ℚ.< δ
             → (n : ℕ) → Σ[ m ∈ ℕ ] at n x ℚ.≤ at m y ℚ.+ δ
