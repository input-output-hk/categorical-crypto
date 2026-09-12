{-# OPTIONS --safe --without-K --guardedness #-}

-- Universal composition on a real protocol, with the error kept: Blum
-- coin-tossing run over the HASH-BASED commitment emulates the same protocol
-- run over the ideal `F_com`, at the commitment's own schedule reindexed by
-- what the composition spends.
--
-- The commitment's UC-level ε-statement is not a theorem yet
-- (`docs/dp-transport.md`), so it is the HYPOTHESIS, in the canonical witness
-- form `_≤UC^ωᵉ_`; everything `UC.Asymptotic.Compose.UC-composeᵉ` asks of the
-- morphisms it moves is discharged here (`Examples.CoinToss.UC`), and
-- `Allowance-mono` lands on the OUTER comparison, which is the zero schedule
-- because the two sides share their upper stage — `hash-liftᵉ`'s discharge,
-- verbatim.
--
-- What this is NOT is an emulation of an ideal coin functionality: that is the
-- second hop, and it is FALSE at this domain.  `docs/coin-toss.md` gives the
-- two-query counterexample and what would remove it.

open import Data.Nat.Base using (ℕ)
open import Data.Nat.Poly using (poly-const)
open import Data.Product.Base using (_,_; proj₁; proj₂)
open import Data.Rational as ℚ using (ℚ; 0ℚ)
open import Data.Rational.Properties using (≤-refl)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import CategoricalCrypto.UC.Approximate using (Negligible-0; NegligibleBound)
open import CategoricalCrypto.UC.Asymptotic.Compose using (UC-composeᵉ; _∙ᶠ_)
open import CategoricalCrypto.UC.Asymptotic.Contextual
open import CategoricalCrypto.UC.Budget using (simCost)
open import CategoricalCrypto.UC.Model.Seal using (ifaceᵒ)
open import CategoricalCrypto.UC.Model.Setup

import CategoricalCrypto.Examples.CoinToss as CT
import CategoricalCrypto.Examples.CoinToss.Hiding as CTH
import CategoricalCrypto.Examples.CoinToss.Hiding.UC as CTHU
import CategoricalCrypto.Examples.CoinToss.UC as CTU
import CategoricalCrypto.Examples.ROCommitment as RO
import CategoricalCrypto.Examples.ROCommitment.Hiding as ROH
import CategoricalCrypto.Examples.ROCommitment.Hiding.UC as ROHU
import CategoricalCrypto.Examples.ROCommitment.UC as ROU

module CategoricalCrypto.Examples.CoinToss.Compose where

------------------------------------------------------------------------
-- The two stages as families

-- The commitment's resource, its simulator-facing port, its corrupt-committer
-- port and its honest port; then the coin-toss stage's own two.
Resᶠ Advᶠ Lkᶠ Honᶠ Advᶜᶠ Honᶜᶠ : ℕ → Channel
Resᶠ  n = ifaceᵒ (RO.Resᴵ n)
Advᶠ  n = ifaceᵒ (RO.Advᴵ n)
Lkᶠ   n = ifaceᵒ (RO.Lkᴵ n)
Honᶠ  n = ifaceᵒ (RO.Honᴵ n)
Advᶜᶠ n = ifaceᵒ (CT.Advᴵᶜ n)
Honᶜᶠ n = ifaceᵒ (CT.Honᴵᶜ n)

realᶠ : Homᶠ Resᶠ Advᶠ Honᶠ
realᶠ = ROU.realᵒ

idealᶠ : Homᶠ Resᶠ Lkᶠ Honᶠ
idealᶠ = ROU.idealᵒ

-- The coin-toss stage, whose DOMAIN is the commitment's codomain: that is what
-- lets `_∙ᶠ_` plug the two together.
tossᶠ : Homᶠ Honᶠ Advᶜᶠ Honᶜᶠ
tossᶠ = CTU.tossᵒ

------------------------------------------------------------------------
-- The composed statement

-- The commitment stays below the coin toss and only its world changes, so the
-- upper stage is compared with ITSELF: the outer witness is `idᶜ` at the zero
-- schedule, which is both `NegligibleBound` and `Allowance-mono` for free.
-- The whole error is the commitment's, read at the allowance the composition
-- rescales it by.
coin-toss-from-com : realᶠ ≤UC^ωᵉ idealᶠ
                   → (tossᶠ ∙ᶠ realᶠ) ≤UC^ωᵉ (tossᶠ ∙ᶠ idealᶠ)
coin-toss-from-com (sf , εf , nf , ef) =
  UC-composeᵉ sf εf nf ef
              idᶜ (λ _ _ → 0ℚ) (λ _ _ → Negligible-0) (λ _ _ → ≤-refl)
              (≈C⇒≈ctx λ n → Equiv.sym (sub-identityˡ (tossᶠ n)))
              (λ _ → 1) (poly-const 1) CTU.recvQB
              (λ _ → 0) (poly-const 0) CTU.tossQB

------------------------------------------------------------------------
-- …and the schedule it carries, exactly

-- `UC-composeᵉ`'s two substitutions instantiated: the OUTER one contributes
-- `0ℚ` (the shared upper stage), and the inner one is read at
-- `simCost q ((cost idᶜ n ⊔ 1) * 0)` — the coin-toss stage makes no downward
-- call, so the continuation costs the test one activation and no more.
εᶜᵗ : (ℕ → ℕ → ℚ) → ℕ → ℕ → ℚ
εᶜᵗ ε n q = 0ℚ ℚ.+ ε n (simCost q 0)

-- Mechanical, not a copied formula: this stops checking the moment the
-- substitution changes.
schedule-pin : (w : realᶠ ≤UC^ωᵉ idealᶠ)
             → proj₁ (proj₂ (coin-toss-from-com w)) ≡ εᶜᵗ (proj₁ (proj₂ w))
schedule-pin _ = refl

------------------------------------------------------------------------
-- The same, at the other corruption

-- `F_com`'s two halves are two different ports (`docs/fcom-hiding.md`), so
-- this is a second theorem and not an instance of the first.  What changes
-- quantitatively is only the coin-toss stage's own rate — it drives `F_com`
-- here, where the extraction half's stage only listened — and `simCost` reads
-- `0` and `1` at the same allowance, so the composed schedule is the same
-- expression.
Advʰᶠ Lkʰᶠ Honʰᶠ Advᶜʰᶠ Honᶜʰᶠ : ℕ → Channel
Advʰᶠ   n = ifaceᵒ (ROH.Advᴵʰ n)
Lkʰᶠ    n = ifaceᵒ (ROH.Lkᴵʰ n)
Honʰᶠ   n = ifaceᵒ (ROH.Honᴵʰ n)
Advᶜʰᶠ  n = ifaceᵒ (CTH.Advᴵᶜʰ n)
Honᶜʰᶠ  n = ifaceᵒ (CTH.Honᴵᶜʰ n)

realʰᶠ : Homᶠ Resᶠ Advʰᶠ Honʰᶠ
realʰᶠ = ROHU.realʰᵒ

idealʰᶠ : Homᶠ Resᶠ Lkʰᶠ Honʰᶠ
idealʰᶠ = ROHU.idealʰᵒ

tossʰᶠ : Homᶠ Honʰᶠ Advᶜʰᶠ Honᶜʰᶠ
tossʰᶠ = CTHU.tossʰᵒ

coin-toss-from-comʰ : realʰᶠ ≤UC^ωᵉ idealʰᶠ
                    → (tossʰᶠ ∙ᶠ realʰᶠ) ≤UC^ωᵉ (tossʰᶠ ∙ᶠ idealʰᶠ)
coin-toss-from-comʰ (sf , εf , nf , ef) =
  UC-composeᵉ sf εf nf ef
              idᶜ (λ _ _ → 0ℚ) (λ _ _ → Negligible-0) (λ _ _ → ≤-refl)
              (≈C⇒≈ctx λ n → Equiv.sym (sub-identityˡ (tossʰᶠ n)))
              (λ _ → 1) (poly-const 1) CTHU.comQB
              (λ _ → 1) (poly-const 1) CTHU.tossʰQB

schedule-pinʰ : (w : realʰᶠ ≤UC^ωᵉ idealʰᶠ)
              → proj₁ (proj₂ (coin-toss-from-comʰ w)) ≡ εᶜᵗ (proj₁ (proj₂ w))
schedule-pinʰ _ = refl
