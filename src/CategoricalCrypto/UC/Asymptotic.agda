{-# OPTIONS --safe --without-K --guardedness #-}

-- The asymptotic consumer end: a FAMILY of UC emulations between protocol
-- images, and what an ideal safety bound becomes on the real side.
--
-- The premise is a per-level emulation with its simulator visible — not a
-- direct run agreement, which is what the ledger's carry used to take
-- (`docs/protocol-implementation-review.md` §4).  Two things are then carried,
-- and by different routes, because the two ends of the seam are:
--
--   * `UC.Asymptotic.Audit.uc-audit-carry` is the GRADED carry
--     (`UC.Audit.audit-carry`) read at the family: the ideal side's designated
--     audit event crosses each emulation, the simulator absorbed into the
--     context and its queries charged there (`simCost`).  It lives next door
--     because the two halves in one module cost 127 s warm and apart 10 + 10 s
--     — the seal-level terms of the collapse and the audit event's
--     instantiation are cheap alone and not together.
--
--   * `uc-preservesᴺ` here is the PROBABILITY carry: at the trivial grade the
--     simulator is provably blind (`UC.Seam.Grounded.subBlind`), so an
--     emulation collapses to the direct agreement `povCarry` consumes, and
--     `UC.Saturated`'s negligible tier transports the bound.  Totality is what
--     rules out the degenerate simulator — a never-starting one makes every
--     ideal invisible — and `Protocol.Live` discharges it for a dead-free
--     system.
--
-- The two do not compose: turning the graded conclusion back into a
-- probability needs the absorbed context to be one of the contexts the IDEAL
-- event permits, and `UC.Seam.Audit.watched` permits a context only when its
-- observation is `≈ₚ`-EQUAL to an ideal monitored run.  The simulator's own
-- initialization makes it ε-close and no more (that is exactly what `subBlind`
-- proves and all it can prove), so the inclusion is not derivable here.  The
-- probability route is the one that closes, and it charges no `simCost`
-- because at the trivial grade the simulator costs the ideal side nothing.

open import Data.Bool.Base using (Bool)
open import Data.Nat.Base as ℕ using (ℕ)
open import Data.Nat.Poly using (Poly)
open import Data.Product.Base using (_,_)
open import Data.Rational as ℚ using (ℚ; 0ℚ)
open import Data.Rational.Properties using (+-identityʳ; ≤-trans)
open import Relation.Binary.PropositionalEquality using (subst; sym)

open import CategoricalCrypto.Iface
open import CategoricalCrypto.Protocol using (Protocol)
open import CategoricalCrypto.Protocol.Machine using (morphism)
open import CategoricalCrypto.Protocol.Machine.Total using (TotalRun)
open import CategoricalCrypto.Protocol.Observe using (Bounded; Pr; PrHit)
open import CategoricalCrypto.Strategy using (Strat; asks≤)
open import CategoricalCrypto.UC.Approximate
  using (Negligible; NegligibleBound; Negligible-0)
open import CategoricalCrypto.UC.Model.Seal using (procᵒ)
open import CategoricalCrypto.UC.Model.Setup
open import CategoricalCrypto.UC.Saturated
open import CategoricalCrypto.UC.Seam using (Agreeˢ)
open import CategoricalCrypto.UC.Seam.Carry using (agreeToAdv)
import CategoricalCrypto.UC.Seam.Grounded as Gr

module CategoricalCrypto.UC.Asymptotic where

open Gr using (ιᴳ; unitGrade)

private variable B : ℕ → Iface
                 R I : Systems B
                 ε : ℕ → ℕ → ℚ
                 ν : ℕ → ℚ

infix 4 _≤UC^ω_

-- The premise, at each level: the real image emulates the ideal one, in the
-- INHERITED preorder — a simulator per dummy adversary, quantified at the
-- grade.  This is the standard notion and it is what the trivial-grade
-- collapse consumes; it is emphatically not a direct run agreement.
_≤UC^ω_ : Systems B → Systems B → Set₁
_≤UC^ω_ {B} R I = (n : ℕ)
  → (ιᴳ (B n) ∘ procᵒ (morphism (R n))) ≤UC (ιᴳ (B n) ∘ procᵒ (morphism (I n)))

------------------------------------------------------------------------
-- The probability carry

-- At the trivial grade an emulation IS the agreement layer 1 consumes.
uc-agree : ((n : ℕ) → TotalRun (B n) (morphism (R n)))
         → ((n : ℕ) → TotalRun (B n) (morphism (I n)))
         → R ≤UC^ω I
         → (n : ℕ) → Agreeˢ (B n) (morphism (R n)) (morphism (I n))
uc-agree {B} tR tI em n = unitGrade (B n) _ _ (tR n) (tI n) (em n)

-- …read as the negligible-graded relation of `UC.Saturated`, whose witness is
-- kept.  The slack is a parameter because an ε-quantified agreement gives a
-- bound at every POSITIVE slack and has no zero instance to give; any positive
-- negligible `ν` will do (`UC.Approximate.Decay.negligible-slack`).
uc-≈negl : ((n : ℕ) → 0ℚ ℚ.< ν n) → Negligible ν
         → ((n : ℕ) → Agreeˢ (B n) (morphism (R n)) (morphism (I n))) → R ≈negl I
uc-≈negl {ν = ν} {R = R} {I} pos neg ag =
  (λ n _ → ν n) , (λ _ _ → neg) , λ n → agreeToAdv (R n) (I n) (ag n) (ν n) (pos n)

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

------------------------------------------------------------------------
-- …and back to the trajectory

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
