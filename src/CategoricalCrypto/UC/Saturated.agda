{-# OPTIONS --safe --without-K #-}

-- The saturated form of a concrete safety bound.
--
-- What the UC core carries is what its observational equivalence cannot see, so
-- the shape a concrete statement should have is one INVARIANT under that
-- equivalence.  The exact bound is not: a system that differs from `P` by the
-- allowed error can exceed `ε q` by that error, so `Bounded P bad ε` holds
-- while `Bounded Q bad ε` fails, for a `Q` the layer above declares equal to
-- `P`.  The cure is an existentially quantified slack, `ε q + ν n` for SOME
-- small `ν`, which absorbs the difference while still forbidding a constant
-- loss.  That is the notes' `POV-modulo-negligible`.
--
-- Two quantifiers decide what the form actually says, and both are corrected
-- here against `docs/protocol-implementation-review.md` §2-3.
--
--   The ALLOWANCE comes first.  A slack uniform over all query counts does not
--   follow from control at polynomial allowances only: a system answering
--   truthfully until query `2^n` is vanishingly far from one that never does,
--   yet a watch reading `2^n` queries sees probability one.  So the allowance
--   `p` is quantified before `ν`, and `ν` may depend on it — the discipline
--   `UC.Approximate`'s `GradedBound` already records.
--
--   The GRADE is a parameter.  `_→0` is what the observational layer supplies,
--   `Negligible` what a cryptographic bound must satisfy, and the two differ:
--   an inverse-linear excess vanishes and is not negligible.  Both forms and
--   their invariance are stated once over `Grade` and instantiated twice, so
--   the tiers differ in exactly the two places they should — the grade of the
--   slack, and the grade of the error carried across.
--
-- The two observables behave differently on purpose:
--
--   `SaturatedBounded` reads the system's own ANSWERS (`Pr`, an
--   interface-observable event), and it is invariant: `saturated-respects`.
--
--   `SaturatedHit` reads the STATE TRAJECTORY (`PrHit`), which no environment
--   sees, so it is saturated in the slack but NOT invariant: a simulator's
--   state is not the ideal system's.  That asymmetry is why the ledger example
--   states the trajectory bound and carries the audit bound, the two tied by
--   its own `TrajectoryFromAudit` — the concrete face of
--   `UC.Audit.audit-carry`'s interface-observability restriction.

open import Data.Bool.Base using (Bool)
open import Data.Nat.Base using (ℕ)
open import Data.Nat.Poly using (Poly)
open import Data.Product.Base using (Σ-syntax; _×_; _,_)
open import Data.Rational as ℚ using (ℚ; 0ℚ)
open import Data.Rational.Properties using (+-assoc; +-mono-≤; ≤-reflexive; ≤-trans)
open import Relation.Binary.PropositionalEquality using (subst)

open import ProbabilisticLogic.Distribution.RationalDist.Advantage
  using (advᵇ⊥-refl; advᵇ⊥-sym; advᵇ⊥-triangle)

open import CategoricalCrypto.Iface
open import CategoricalCrypto.Protocol using (Protocol; St)
open import CategoricalCrypto.Protocol.Observe
  using (Pr; PrHit; _≈adv[_]_; run; transfer-at)
open import CategoricalCrypto.Strategy using (Strat; asks≤)
open import CategoricalCrypto.UC.Approximate
  using ( Grade; GradedBound; Negligible; Negligible-+; Negligible-0; Negligible⇒→0
        ; NegligibleBound; _→0; →0-+ )

module CategoricalCrypto.UC.Saturated where

private variable B : ℕ → Iface

-- A family of closed systems indexed by the security parameter: a small slack
-- needs a parameter to vanish in, and the exact-versus-saturated distinction
-- only exists asymptotically.
Systems : (ℕ → Iface) → Set₁
Systems B = (n : ℕ) → Protocol unitᴵ (B n)

Bad : Systems B → Set
Bad {B} P = (n : ℕ) → St (P n) → Bool

Watch : (B : ℕ → Iface) → Set
Watch B = (n : ℕ) → Strat (Neg (B n)) (Pos (B n))
        → Strat (Neg (B n)) (Pos (B n))

-- A watch that buys no queries: it plays inside the budget it is handed.  The
-- invariance below needs this and nothing else about the watch.
QueryPreserving : Watch B → Set
QueryPreserving {B} bad = (n q : ℕ) (d : Strat (Neg (B n)) (Pos (B n)))
                        → asks≤ q d → asks≤ q (bad n d)

------------------------------------------------------------------------
-- The saturated forms

-- The audit form: at every polynomial allowance `p` there is a slack `ν` of
-- grade `G` — chosen AFTER `p`, so it may depend on it — with no strategy
-- inside the allowance pushing the watched event above `ε n (p n) + ν n`.
SaturatedBounded[_] : Grade → {B : ℕ → Iface} → Systems B → Watch B
                    → (ℕ → ℕ → ℚ) → Set
SaturatedBounded[ G ] {B} P bad ε = (p : ℕ → ℕ) → Poly p
  → Σ[ ν ∈ (ℕ → ℚ) ] G ν
  × ((n : ℕ) (d : Strat (Neg (B n)) (Pos (B n))) → asks≤ (p n) d
     → Pr (P n) (bad n d) ℚ.≤ ε n (p n) ℚ.+ ν n)

-- The trajectory form, saturated the same way — and see the header for why the
-- invariance below is stated for the audit form only.
SaturatedHit[_] : Grade → {B : ℕ → Iface} (P : Systems B) → Bad P
                → (ℕ → ℕ → ℚ) → Set
SaturatedHit[ G ] {B} P bad ε = (p : ℕ → ℕ) → Poly p
  → Σ[ ν ∈ (ℕ → ℚ) ] G ν
  × ((n : ℕ) (d : Strat (Neg (B n)) (Pos (B n))) → asks≤ (p n) d
     → PrHit (P n) (bad n) d ℚ.≤ ε n (p n) ℚ.+ ν n)

-- The observational tier: a slack the family layer's vanishing agreement can
-- absorb (`UC.Family.absorb`).
SaturatedBounded : Systems B → Watch B → (ℕ → ℕ → ℚ) → Set
SaturatedBounded = SaturatedBounded[ _→0 ]

SaturatedHit : (P : Systems B) → Bad P → (ℕ → ℕ → ℚ) → Set
SaturatedHit = SaturatedHit[ _→0 ]

-- The cryptographic tier: the slack beats every inverse polynomial, which is
-- what "modulo negligible" names and what `_→0` does not give.
SaturatedBoundedᴺ : Systems B → Watch B → (ℕ → ℕ → ℚ) → Set
SaturatedBoundedᴺ = SaturatedBounded[ Negligible ]

SaturatedHitᴺ : (P : Systems B) → Bad P → (ℕ → ℕ → ℚ) → Set
SaturatedHitᴺ = SaturatedHit[ Negligible ]

saturatedᴺ⇒saturated : {P : Systems B} {bad : Watch B} {ε : ℕ → ℕ → ℚ}
                     → SaturatedBoundedᴺ P bad ε → SaturatedBounded P bad ε
saturatedᴺ⇒saturated sat p Pp =
  let ν , neg , bnd = sat p Pp in ν , Negligible⇒→0 neg , bnd

saturatedHitᴺ⇒saturatedHit : {P : Systems B} {bad : Bad P} {ε : ℕ → ℕ → ℚ}
                           → SaturatedHitᴺ P bad ε → SaturatedHit P bad ε
saturatedHitᴺ⇒saturatedHit sat p Pp =
  let ν , neg , bnd = sat p Pp in ν , Negligible⇒→0 neg , bnd

------------------------------------------------------------------------
-- Invariance

SaturatedRespects[_] : Grade → Set₁
SaturatedRespects[ G ] =
  {B : ℕ → Iface} (P Q : Systems B) (bad : Watch B) (ε δ : ℕ → ℕ → ℚ)
  → ((n : ℕ) → P n ≈adv[ δ n ] Q n) → GradedBound G δ → QueryPreserving bad
  → SaturatedBounded[ G ] P bad ε → SaturatedBounded[ G ] Q bad ε

-- `transfer-at` at each `n` moves the bound at the ONE budget the allowance
-- fixes, adding `δ n (p n)`; the new slack `ν + δ(·, p ·)` keeps its grade
-- because reading a `GradedBound` at the allowance is already that grade and
-- the grade is closed under sums.  That closure is the whole arithmetic
-- content, and it is the only thing the two tiers do not share.
saturated-respects[_] : (G : Grade)
                      → ({s t : ℕ → ℚ} → G s → G t → G (λ n → s n ℚ.+ t n))
                      → SaturatedRespects[ G ]
saturated-respects[ G ] G-+ P Q bad ε δ near carry qp sat p Pp =
  let ν , Gν , bnd = sat p Pp
  in (λ n → ν n ℚ.+ δ n (p n)) , G-+ Gν (carry p Pp) , λ n d a →
     subst (Pr (Q n) (bad n d) ℚ.≤_) (+-assoc (ε n (p n)) (ν n) (δ n (p n)))
       (transfer-at (p n) (bad n d) (qp n (p n) d a) (near n) (bnd n d a))

-- The repaired §2 statement, proved: what `VanishingBound δ` genuinely carries.
SaturatedRespects : Set₁
SaturatedRespects = SaturatedRespects[ _→0 ]

saturated-respects : SaturatedRespects
saturated-respects = saturated-respects[ _→0 ] →0-+

-- …and §3's tier, whose carry premise is graded to match its conclusion.
SaturatedRespectsᴺ : Set₁
SaturatedRespectsᴺ = SaturatedRespects[ Negligible ]

saturated-respectsᴺ : SaturatedRespectsᴺ
saturated-respectsᴺ = saturated-respects[ Negligible ] Negligible-+

------------------------------------------------------------------------
-- The negligible-grade relation

-- Review §3 asks for a negligible observational relation OR a carry premise
-- retaining the error witness.  At this layer they are the same thing:
-- `_≈negl_` is `≈adv` with its witness KEPT and graded.  Keeping the witness
-- is exactly what a vanishing equivalence cannot do — a one-shot bad bit of
-- probability `1/(n+1)` is vanishingly far from an always-safe one and NOT
-- negligibly far — so forgetting `δ` and forgetting its grade are one loss.
-- The vanishing tier needs no such bundle: `saturated-respects` takes its
-- `VanishingBound` premise unbundled, and that is all it can spend.
infix 4 _≈negl_

_≈negl_ : Systems B → Systems B → Set
P ≈negl Q = Σ[ δ ∈ (ℕ → ℕ → ℚ) ] NegligibleBound δ
          × ((n : ℕ) → P n ≈adv[ δ n ] Q n)

≈negl-refl : {P : Systems B} → P ≈negl P
≈negl-refl {P = P} = (λ _ _ → 0ℚ) , (λ _ _ → Negligible-0)
                   , λ n b _ d _ → ≤-reflexive (advᵇ⊥-refl b (run (P n) d))

≈negl-sym : {P Q : Systems B} → P ≈negl Q → Q ≈negl P
≈negl-sym {P = P} {Q} (δ , neg , near) = δ , neg , λ n b q d a →
  subst (ℚ._≤ δ n q) (advᵇ⊥-sym b (run (P n) d) (run (Q n) d)) (near n b q d a)

≈negl-trans : {P Q R : Systems B} → P ≈negl Q → Q ≈negl R → P ≈negl R
≈negl-trans {P = P} {Q} {R} (δ₁ , neg₁ , near₁) (δ₂ , neg₂ , near₂) =
  (λ n q → δ₁ n q ℚ.+ δ₂ n q) , (λ p Pp → Negligible-+ (neg₁ p Pp) (neg₂ p Pp))
  , λ n b q d a → ≤-trans (advᵇ⊥-triangle b (run (P n) d) (run (Q n) d) (run (R n) d))
                          (+-mono-≤ (near₁ n b q d a) (near₂ n b q d a))

-- The invariance in packaged form: the relation carries the tier it is graded
-- for, and only that tier.
≈negl-respects : {P Q : Systems B} {bad : Watch B} {ε : ℕ → ℕ → ℚ}
               → P ≈negl Q → QueryPreserving bad
               → SaturatedBoundedᴺ P bad ε → SaturatedBoundedᴺ Q bad ε
≈negl-respects {P = P} {Q} {bad} {ε} (δ , neg , near) qp =
  saturated-respectsᴺ P Q bad ε δ near neg qp
