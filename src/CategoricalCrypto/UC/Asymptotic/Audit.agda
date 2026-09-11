{-# OPTIONS --safe --without-K --guardedness #-}

-- The graded carry at the family: `UC.Audit.audit-carry` read at a family of
-- BUDGETED emulations, the simulator's own query cost charged.
--
-- `UC.Asymptotic`'s header has the split: this half and the probability half
-- do not compose, and this one is where `simCost` is paid.  The real-side
-- event class is `absorb (sim em) cs` — the largest class closed into the
-- ideal one, by the proved `absorb-absorbs` — so nothing at all is assumed
-- about the real side.

open import Data.Nat.Base using (ℕ)
open import Data.Rational as ℚ using (ℚ; 0ℚ)

open import CategoricalCrypto.Iface using (Iface)
open import CategoricalCrypto.Protocol.Machine using (morphism)
open import CategoricalCrypto.UC.Model.Seal using (procᵒ)
open import CategoricalCrypto.UC.Model.Setup
open import CategoricalCrypto.UC.Saturated using (Systems; Watch)
open import CategoricalCrypto.UC.Seam.Audit
  using ( _≤UC[_]_; sim; simCost; AuditBound; absorb; absorb-absorbs; audit-carry
        ; module TrivialGrade )
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
