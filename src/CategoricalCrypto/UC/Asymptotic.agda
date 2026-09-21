{-# OPTIONS --safe --without-K --guardedness #-}

-- The asymptotic consumer end: a family of UC emulations between protocol
-- images, and what an ideal safety bound becomes on the real side.
--
-- The premise is a per-level emulation with its simulator visible — not a
-- direct run agreement, which is what the ledger's carry used to take
-- (`docs/protocol-implementation-review.md` §4).  It is the POINTWISE,
-- unit-grade SPECIALIZATION of asymptotic-family emulation and not the family
-- relation itself; `_≤UC^ω_` below says what that costs, and
-- `UC.Asymptotic.Family` is the family premise.
--
-- `uc-preservesᴺ` is the PROBABILITY carry: `UC.Saturated`'s negligible tier
-- transports the ideal bound across `_≈negl_`, which
-- `UC.Asymptotic.Family.≤UC^ωⁿ⇒≈negl` supplies.  Reaching it from this
-- pointwise premise costs the real side's totality, which rules out the
-- degenerate simulator — a never-starting one makes every ideal invisible —
-- and `Protocol.Live` discharges it for a dead-free system.

open import Data.Nat.Base as ℕ using (ℕ)
open import Data.Nat.Poly using (Poly)
open import Data.Product.Base using (_,_)
open import Data.Rational as ℚ using (ℚ; 0ℚ)
open import Data.Rational.Properties using (+-identityʳ; ≤-trans)
open import Relation.Binary.PropositionalEquality using (subst; sym)

open import CategoricalCrypto.Iface
open import CategoricalCrypto.Protocol.Machine using (morphism)
open import CategoricalCrypto.Protocol.Observe using (Bounded; Pr; PrHit)
open import CategoricalCrypto.Strategy using (Strat; asks≤)
open import CategoricalCrypto.UC.Approximate using (Negligible-0)
open import CategoricalCrypto.UC.Model.Setup
open import CategoricalCrypto.UC.Saturated
open import CategoricalCrypto.UC.Seam.Grounded using (closedᵒ)

module CategoricalCrypto.UC.Asymptotic where

private variable B : ℕ → Iface
                 R I : Systems B
                 ε : ℕ → ℕ → ℚ

infix 4 _≤UC^ω_

-- The premise, at each level: the real image emulates the ideal one, in the
-- INHERITED preorder — a simulator per dummy adversary, quantified at the
-- grade.  This is the standard notion at a FIXED level and it is what the
-- trivial-grade collapse consumes; it is emphatically not a direct run
-- agreement.
--
-- It is also, just as emphatically, NOT asymptotic-family emulation but its
-- pointwise/unit-grade specialization, and the difference is not bookkeeping.
-- `_≤UC_` at one level compares two processes at an ε quantified over EVERY
-- positive value, so with the real side total the collapse hands back agreement
-- at every positive error at that level
-- (`UC.Asymptotic.Family.pointwise-exact` states exactly that).  A pair whose
-- verdict probabilities differ by `2⁻ⁿ` at level `n` therefore FAILS this
-- premise at every level (`Family.pointwise-rejects`) while being negligibly
-- different — which is what an asymptotic premise has to admit.  So this
-- relation is strictly stronger than the family one: it rejects families the
-- family premise accepts (`Family.admits-inv-pow-2`).
--
-- `UC.Asymptotic.Family._≤UC^ωⁿ_` is that family premise, and `uc-≤UC^ωⁿ`
-- proves this relation plus the real side's totality includes into it, so every
-- theorem off it is a specialization of one stated there.
_≤UC^ω_ : Systems B → Systems B → Set₁
_≤UC^ω_ {B} R I = (n : ℕ)
  → closedᵒ (morphism (R n)) ≤UC closedᵒ (morphism (I n))

------------------------------------------------------------------------
-- The probability carry

-- An exact per-level bound IS its own saturated form, at zero slack.
boundedᴺ : {bad : Watch B} → ((n : ℕ) → Bounded (I n) (bad n) (ε n))
         → SaturatedBoundedᴺ I bad ε
boundedᴺ {I = I} {ε = ε} {bad} bnd p _ = (λ _ → 0ℚ) , Negligible-0 , λ n d a →
  subst (Pr (I n) (bad n d) ℚ.≤_) (sym (+-identityʳ (ε n (p n)))) (bnd n (p n) d a)

-- The transport itself: `UC.Saturated`'s repaired invariance, at the
-- negligible tier, consuming the emulation family.
uc-preservesᴺ : {bad : Watch B} → QueryPreserving bad → R ≈negl I
              → SaturatedBoundedᴺ I bad ε → SaturatedBoundedᴺ R bad ε
uc-preservesᴺ {ε = ε} qp near = ≈negl-respects {ε = ε} (≈negl-sym near) qp

-- What a monitor bound gives about the STATE: nothing, unless the system's own
-- audit answers are truthful about it, which is a property of the
-- implementation and not of UC (review requirement 5).  `aud` is the
-- instrumentation that makes the monitor see every boundary the trajectory
-- inspects and `bud` is what it costs the allowance — both explicit, both
-- charged, and the cost reappears in the conclusion's own bound.
saturatedHitᴺ-from-monitor :
    {P : Systems B} {Bad : Bad P} {bad : Watch B} (bud : ℕ → ℕ → ℕ)
    (aud : (n : ℕ) → Strat (Neg (B n)) (Pos (B n)) → Strat (Neg (B n)) (Pos (B n)))
  → ((p : ℕ → ℕ) → Poly p → Poly (λ n → bud n (p n)))
  → ((n q : ℕ) (d : Strat (Neg (B n)) (Pos (B n)))
     → asks≤ q d → asks≤ (bud n q) (aud n d))
  → ((n : ℕ) (d : Strat (Neg (B n)) (Pos (B n)))
     → PrHit (P n) (Bad n) d ℚ.≤ Pr (P n) (bad n (aud n d)))
  → SaturatedBoundedᴺ P bad ε → SaturatedHitᴺ P Bad (λ n q → ε n (bud n q))
saturatedHitᴺ-from-monitor bud aud Pbud aud-asks truthful sat p Pp =
  let ν , neg , bnd = sat (λ n → bud n (p n)) (Pbud p Pp)
  in ν , neg , λ n d a → ≤-trans (truthful n d) (bnd n (aud n d) (aud-asks n (p n) d a))
