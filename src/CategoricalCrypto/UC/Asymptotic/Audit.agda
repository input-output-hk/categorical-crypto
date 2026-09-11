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
-- a probability, and the price is the widened event class `watchedᵖ` —
-- `UC.Seam.Audit.Prefix` is where that is proved and priced.

open import Data.Nat.Base using (ℕ)
open import Data.Rational as ℚ using (ℚ; 0ℚ)

open import ProbabilisticLogic.Dp.Mass using (ASTotal)

open import CategoricalCrypto.Iface using (Iface)
open import CategoricalCrypto.Protocol.Machine using (morphism)
open import CategoricalCrypto.Protocol.Observe using (Bounded)
open import CategoricalCrypto.UC.Model.Seal using (procᵒ)
open import CategoricalCrypto.UC.Model.Setup
open import CategoricalCrypto.UC.Saturated using (QueryPreserving; Systems; Watch)
open import CategoricalCrypto.UC.Seam.Audit
  using ( _≤UC[_]_; sim; simCost; AuditBound; absorb; absorb-absorbs; audit-carry
        ; module TrivialGrade )
open import CategoricalCrypto.UC.Seam.Audit.Prefix using (uc-audit-bounded)
open import CategoricalCrypto.UC.Seam.Grounding.Dead using (pointᵒ)
import CategoricalCrypto.UC.Seam.Grounded as Gr

module CategoricalCrypto.UC.Asymptotic.Audit where

open Gr using (𝟘ᴳ; ιᴳ)
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
  → (ιᴳ (B n) ∘ procᵒ (morphism (R n))) ≤UC[ cs n ] (ιᴳ (B n) ∘ procᵒ (morphism (I n)))

-- Each level's ideal audit bound crosses its emulation: the real side reads
-- the absorbed event class and pays `simCost` for the simulator's queries.
uc-audit-carry : (em : R ≤UC^ω[ cs ] I) (bad : Watch B)
               → ((n : ℕ) → AuditBound (ιᴳ (B n) ∘ procᵒ (morphism (I n)))
                              (watched (I n) (bad n)) (ε n))
               → ((n : ℕ) → 0ℚ ℚ.< ν n) → (n : ℕ)
               → AuditBound (ιᴳ (B n) ∘ procᵒ (morphism (R n)))
                   (absorb (sim (em n)) (cs n) (watched (I n) (bad n)))
                   (λ q → ε n (simCost q (cs n)) ℚ.+ ν n)
uc-audit-carry {I = I} {ε = ε} {ν = ν} em bad bnd pos n =
  audit-carry _ _ (em n) {𝔉 = 𝔉ₙ} (absorb-absorbs {𝔉 = 𝔉ₙ}) (ε n) (ν n) (pos n) (bnd n)
  where 𝔉ₙ = watched (I n) (bad n)

-- …and the same crossing read back as layer 1's own probability, at the widened
-- class: the ideal bound is an ordinary `Bounded` on the monitor's verdict, and
-- what comes out is the real system's, with the simulator's queries charged and
-- its initialization tolerated.  The extra hypothesis is that initialization's
-- almost-sure totality, which `UC.Seam.Grounded.simTotal⇒point` reads off the
-- real family's own `TotalRun` exactly as `subBlind⇒unitGrade` does.
uc-audit-boundedᵖ : (em : R ≤UC^ω[ cs ] I) (bad : Watch B)
                  → ((n : ℕ) → ASTotal (pointᵒ 𝟘ᴳ 𝟘ᴳ (sim (em n))))
                  → QueryPreserving bad
                  → ((n : ℕ) → Bounded (I n) (bad n) (ε n))
                  → ((n : ℕ) → 0ℚ ℚ.< ν n) → (n : ℕ)
                  → Bounded (R n) (bad n) (λ q → ε n (simCost q (cs n)) ℚ.+ ν n)
uc-audit-boundedᵖ {R = R} {cs = cs} {I = I} {ε = ε} {ν = ν} em bad tot qp bi pos n =
  uc-audit-bounded _ (R n) (I n) (bad n) (em n) (ε n) (ν n) (pos n) (tot n) (qp n) (bi n)
