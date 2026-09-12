{-# OPTIONS --safe --without-K --guardedness #-}

-- The graded carry at the family: `UC.Audit.audit-carry` read at a family of
-- BUDGETED emulations, the simulator's own query cost charged.
--
-- `UC.Asymptotic`'s header has the split, and this is where `simCost` is paid.
-- The real-side event class is `absorb (sim em) cs` — the largest class closed
-- into the ideal one, by the proved `absorb-absorbs` — so nothing at all is
-- assumed about the real side.
--
-- `uc-audit-carry` ends at a graded bound and cannot do better: extracting a
-- probability from it would need the extraction context, the simulator in front
-- of it, to observe an ideal monitored run EXACTLY, which an almost-surely-total
-- initialization never gives.  `uc-audit-boundedᵖ` is the route that does reach
-- a probability, and it takes `UC.Seam.Audit.Prefix.uc-audit-bounded′`, which
-- has no event class on it at all — the simulator's initialization is a prefix
-- and a prefix never adds mass (`sim-prefixed`).
--
-- `uc-audit-carryᵈ` is `uc-audit-carry`'s own conclusion with the event class
-- spelled out instead of designated: same hypotheses, same number, no
-- `watched`/`absorb` in the statement.

open import Data.Nat.Base using (ℕ)
open import Data.Product.Base using (_,_; proj₁)
open import Data.Rational as ℚ using (ℚ; 0ℚ)
open import Data.Rational.Properties using (+-monoˡ-≤; ≤-trans)

open import ProbabilisticLogic.Dp using (_≈ₚ_)
open import ProbabilisticLogic.Dp.Advantage using (Pr≤; ≼ₚ⇒≼ₚ[0])
open import ProbabilisticLogic.Dp.Mass using (ASTotal)

open import CategoricalCrypto.Iface
open import CategoricalCrypto.Protocol.Machine using (morphism; runᴹ)
open import CategoricalCrypto.Protocol.Observe using (Bounded)
open import CategoricalCrypto.Strategy using (Strat; asks≤)
open import CategoricalCrypto.UC.Model.Bridge using (ucBaseᵒ)
open import CategoricalCrypto.UC.Model.Observation using (𝟘ᵒ)
open import CategoricalCrypto.UC.Model.Seal using (ifaceᵒ)
open import CategoricalCrypto.UC.Model.Setup
open import CategoricalCrypto.UC.Saturated using (QueryPreserving; Systems; Watch)
open import CategoricalCrypto.UC.Seam.Audit
  using ( _≤UC[_]_; emulate; sim; simCost; AuditBound; absorb; absorb-absorbs
        ; carry-obs; audit-carry; module TrivialGrade )
open import CategoricalCrypto.UC.Seam.Audit.Bounded using (supply)
open import CategoricalCrypto.UC.Seam.Audit.Prefix using (uc-audit-bounded′)
open import CategoricalCrypto.UC.Seam.Grounding.Dead using (pointᵒ)
import CategoricalCrypto.UC.Seam.Grounded as Gr

module CategoricalCrypto.UC.Asymptotic.Audit where

-- The event class is spelled in `ucBaseᵒ`'s own action, which `absorb` is stated
-- over; `UC.Model.Setup`'s agrees with it on the nose but is a different record
-- (`UC.Seam.Audit.Context`'s header).
open import CategoricalCrypto.UC.Emulation ucBaseᵒ
  using (Closure; Test; _⊛_; obs; tv₁) renaming (sub to subᵉ)

open Gr using (closedᵒ; 𝟘ᴳ; ιᴳ)
open TrivialGrade 𝟘ᴳ ιᴳ using (watched)

private variable B : ℕ → Iface
                 R I : Systems B
                 cs : ℕ → ℕ
                 ε : ℕ → ℕ → ℚ
                 ν : ℕ → ℚ

infix 4 _≤UC^ω[_]_

-- The premise: the emulation layer's own emulation, whose simulator carries a
-- query bound.  A carry that charges the simulator needs it; the trivial-grade
-- collapse next door does not, the simulator asking nothing there.
_≤UC^ω[_]_ : Systems B → (ℕ → ℕ) → Systems B → Set₁
_≤UC^ω[_]_ {B} R cs I = (n : ℕ)
  → closedᵒ (morphism (R n)) ≤UC[ cs n ] closedᵒ (morphism (I n))

-- Each level's ideal audit bound crosses its emulation: the real side reads
-- the absorbed event class and pays `simCost` for the simulator's queries.
uc-audit-carry : (em : R ≤UC^ω[ cs ] I) (bad : Watch B)
               → ((n : ℕ) → AuditBound (closedᵒ (morphism (I n)))
                              (watched (I n) (bad n)) (ε n))
               → ((n : ℕ) → 0ℚ ℚ.< ν n) → (n : ℕ)
               → AuditBound (closedᵒ (morphism (R n)))
                   (absorb (sim (em n)) (cs n) (watched (I n) (bad n)))
                   (λ q → ε n (simCost q (cs n)) ℚ.+ ν n)
uc-audit-carry {I = I} {ε = ε} {ν = ν} em bad bnd pos n =
  audit-carry _ _ (em n) {𝔉 = 𝔉ₙ} (absorb-absorbs {𝔉 = 𝔉ₙ}) (ε n) (ν n) (pos n) (bnd n)
  where 𝔉ₙ = watched (I n) (bad n)

------------------------------------------------------------------------
-- …and the same conclusion with no event class in it

-- Plan §4.2's property-specific statement, at the existing test, closure,
-- monitor transformation and budget witness: IF the simulator-fronted context
-- observes the ideal monitor's verdict on a strategy the allowance `q` affords,
-- THEN the real system's own observation in that context is under the ideal
-- bound at `q`, plus the carry's slack.  `AuditEvent`, `AuditBound`, `watched`
-- and `absorb` occur nowhere in it, and the ideal supply is layer 1's own
-- `Bounded` rather than a graded premise about a designated class.
--
-- What is spent is `UC.Seam.Audit.carry-obs` — the emulation's domination, the
-- simulator slid onto the test — and `UC.Seam.Audit.Bounded.supply`, the
-- rational arithmetic §4.1 keeps in `Bounded`.  Neither the simulator's query
-- certificate nor `ctxBudget` is consumed: those are `AuditBound`'s way of
-- moving an allowance across a quantifier over budgeted TESTS, and the
-- allowance moves here in the strategy `d` instead.
uc-audit-carryᵈ : (em : R ≤UC^ω[ cs ] I) (bad : Watch B)
                → ((n : ℕ) → Bounded (I n) (bad n) (ε n))
                → ((n : ℕ) → 0ℚ ℚ.< ν n)
                → (n : ℕ) (W : Channel)
                  (Et : Test (W ⊛ (𝟘ᴳ ⊛ ifaceᵒ (B n)))) (m : Closure (W ⊛ 𝟘ᵒ))
                  (q : ℕ) (d : Strat (Neg (B n)) (Pos (B n))) → asks≤ q d
                → obs (tv₁ W (closedᵒ (morphism (I n)))
                           (tv₁ W (subᵉ (sim (em n))) Et)) m
                  ≈ₚ runᴹ (morphism (I n)) (bad n d)
                → (k : ℕ) → Pr≤ k (obs (tv₁ W (closedᵒ (morphism (R n))) Et) m)
                            ℚ.≤ ε n q ℚ.+ ν n
uc-audit-carryᵈ {I = I} {ε = ε} {ν = ν} em bad bi pos n W Et m q d a near k =
  let j , le = carry-obs _ _ (sim (em n)) (emulate (em n)) W Et m (ν n) (pos n) k
  in ≤-trans le (+-monoˡ-≤ (ν n)
       (supply (I n) (bad n) (ε n) q d a (bi n) _ (≼ₚ⇒≼ₚ[0] (proj₁ near)) j))

-- …and it recovers `uc-audit-carry`'s object, not merely its number: the
-- designated class unfolds to exactly the hypothesis above, so the `AuditBound`
-- is this theorem past one Σ-pattern, with the two budget certificates unused.
-- The ideal premise is the `Bounded` the designated one is equivalent to at this
-- grade (`UC.Seam.Audit.Bounded.boundedIsAudit`/`auditIsBounded`).
--
-- The conclusion is `uc-audit-carry`'s, spelled again rather than pinned to it
-- by an `at`-style identity: that pin makes Agda unify two applied `AuditBound`s
-- at `absorb … (watched …)`, which does not come back (`docs/consumer-migration.md`
-- has the measurement).
uc-audit-carryᵈ-bound : (em : R ≤UC^ω[ cs ] I) (bad : Watch B)
                      → ((n : ℕ) → Bounded (I n) (bad n) (ε n))
                      → ((n : ℕ) → 0ℚ ℚ.< ν n) → (n : ℕ)
                      → AuditBound (closedᵒ (morphism (R n)))
                          (absorb (sim (em n)) (cs n) (watched (I n) (bad n)))
                          (λ q → ε n (simCost q (cs n)) ℚ.+ ν n)
uc-audit-carryᵈ-bound em bad bi pos n W Et m _ _ (d , a , near) =
  uc-audit-carryᵈ em bad bi pos n W Et m _ d a near

-- …and the same crossing read back as layer 1's own probability: the ideal
-- bound is an ordinary `Bounded` on the monitor's verdict, and what comes out is
-- the real system's, with the simulator's queries charged and its
-- initialization tolerated.  The extra hypotheses — that initialization's
-- almost-sure totality, which `UC.Seam.Grounded.simTotal⇒point` reads off the
-- real family's own `TotalRun`, and the monitor's budget law — are part of the
-- statement and are not consumed by the direct route that now proves it
-- (`docs/direct-extraction.md`).
uc-audit-boundedᵖ : (em : R ≤UC^ω[ cs ] I) (bad : Watch B)
                  → ((n : ℕ) → ASTotal (pointᵒ 𝟘ᴳ 𝟘ᴳ (sim (em n))))
                  → QueryPreserving bad
                  → ((n : ℕ) → Bounded (I n) (bad n) (ε n))
                  → ((n : ℕ) → 0ℚ ℚ.< ν n) → (n : ℕ)
                  → Bounded (R n) (bad n) (λ q → ε n (simCost q (cs n)) ℚ.+ ν n)
uc-audit-boundedᵖ {R = R} {cs = cs} {I = I} {ε = ε} {ν = ν} em bad tot qp bi pos n =
  uc-audit-bounded′ _ (R n) (I n) (bad n) (em n) (ε n) (ν n) (pos n) (tot n) (qp n) (bi n)
