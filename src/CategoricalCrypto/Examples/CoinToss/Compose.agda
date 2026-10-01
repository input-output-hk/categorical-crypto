{-# OPTIONS --safe --without-K --guardedness #-}

-- Blum coin-tossing over the hash-based commitment emulates the same protocol
-- over the ideal `F_com`, at the commitment's schedule reindexed by what the
-- composition spends.  The commitment's UC-level ε-statement is not yet a
-- theorem (`docs/dp-transport.md`), so it is the hypothesis; the hop to an
-- ideal coin is `Examples.CoinToss.Ideal.Compose`.

open import Categories.LocallyGraded.SubCategory

open import Data.Nat.Base
open import Data.Nat.Poly
open import Data.Nat.Positive
open import Data.Nat.Properties using (*-identityʳ)
open import Data.Product.Base
open import Data.Rational as ℚ using (ℚ; 0ℚ) renaming (_*_ to _*ℚ_)
open import Data.Rational.Properties using (+-identityˡ)
open import Relation.Binary.PropositionalEquality

open import ProbabilisticLogic.Distribution.Uniform

open import CategoricalCrypto.Examples.ROCommitment.Asymptotic
open import CategoricalCrypto.UC.Approximate
open import CategoricalCrypto.UC.Model.Enrichment
open import CategoricalCrypto.UC.Model.Family.Contextual
open import CategoricalCrypto.UC.Model.Seal
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

open Compose
open GradedSubCat gradingᵒ using (Pred)

------------------------------------------------------------------------
-- The two stages as families

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

tossᶠ : Homᶠ Honᶠ Advᶜᶠ Honᶜᶠ
tossᶠ = CTU.tossᵒ

------------------------------------------------------------------------
-- The composed statement

εᶜᵗ : (ℕ → ℕ → ℚ) → ℕ → ℕ → ℚ
εᶜᵗ ε n q = 0ℚ ℚ.+ ε n (scale q 1⁺)

εᶜᵗ-negligible : (ε : ℕ → ℕ → ℚ) → NegligibleBound ε → NegligibleBound (εᶜᵗ ε)
εᶜᵗ-negligible ε nf =
  composeError-negligible (λ _ → 1⁺) (λ _ → 1⁺) ε (λ _ _ → 0ℚ) poly⁺-1 poly⁺-1 nf (λ _ _ → Negligible-0)

simᶜᵗ : {Lk Adv Advᶜ : ℕ → Channel} → Certified Lk Adv → Certified (Lk ⊗ᶠ Advᶜ) (Adv ⊗ᶠ Advᶜ)
simᶜᵗ sf = composeSim sf idᶜ

-- A stage entering the grading at `1⁺` over a commitment at the same rate, at
-- either corruption and over either resource boundary.
module _ {Rs Adv Lk Hon Advᶜ Honᶜ : ℕ → Channel} {real : Homᶠ Rs Adv Hon}
         {ideal : Homᶠ Rs Lk Hon} (toss : Homᶠ Hon Advᶜ Honᶜ)
         (cr : (n : ℕ) → Pred 1⁺ (real n)) (ct : (n : ℕ) → Pred 1⁺ (toss n)) where

  toss-overᵇ : (sf : Certified Lk Adv) (εf : ℕ → ℕ → ℚ) → real ≤UC[ sf , εf ] ideal
             → (toss ∙ᶠ real) ≤UC[ simᶜᵗ sf , εᶜᵗ εf ] (toss ∙ᶠ ideal)
  toss-overᵇ sf εf ef =
    ≤UC[]-compose′ {u = toss} {v = toss} sf idᶜ (λ _ → 1⁺) (λ _ → 1⁺) εf (λ _ _ → 0ℚ)
      (λ n → imageᵒ (cr n)) (λ n → imageᵒ (ct n)) ef
      (≈C⇒≈ctx λ n → Equiv.sym (sub-identityˡ (toss n)))

  toss-over : real ≤UC^ωᵉ ideal → (toss ∙ᶠ real) ≤UC^ωᵉ (toss ∙ᶠ ideal)
  toss-over (sf , εf , nf , ef) = simᶜᵗ sf , εᶜᵗ εf , εᶜᵗ-negligible εf nf , toss-overᵇ sf εf ef

coin-toss-from-comᵇ : (sf : Certified Lkᶠ Advᶠ) (εf : ℕ → ℕ → ℚ)
                    → realᶠ ≤UC[ sf , εf ] idealᶠ
                    → (tossᶠ ∙ᶠ realᶠ) ≤UC[ simᶜᵗ sf , εᶜᵗ εf ] (tossᶠ ∙ᶠ idealᶠ)
coin-toss-from-comᵇ = toss-overᵇ tossᶠ ROU.recvQB CTU.tossQB

coin-toss-from-com : realᶠ ≤UC^ωᵉ idealᶠ → (tossᶠ ∙ᶠ realᶠ) ≤UC^ωᵉ (tossᶠ ∙ᶠ idealᶠ)
coin-toss-from-com = toss-over tossᶠ ROU.recvQB CTU.tossQB

------------------------------------------------------------------------
-- The same, at the other corruption

-- The corrupted-receiver case (`docs/fcom-hiding.md`): its stage drives
-- `F_com` but still enters the grading at `1⁺`, so the schedule is again `εᶜᵗ`.
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

coin-toss-from-comʰᵇ : (sf : Certified Lkʰᶠ Advʰᶠ) (εf : ℕ → ℕ → ℚ)
                     → realʰᶠ ≤UC[ sf , εf ] idealʰᶠ
                     → (tossʰᶠ ∙ᶠ realʰᶠ) ≤UC[ simᶜᵗ sf , εᶜᵗ εf ] (tossʰᶠ ∙ᶠ idealʰᶠ)
coin-toss-from-comʰᵇ =
  toss-overᵇ tossʰᶠ ROHU.comQB CTHU.tossʰQB

coin-toss-from-comʰ : realʰᶠ ≤UC^ωᵉ idealʰᶠ → (tossʰᶠ ∙ᶠ realʰᶠ) ≤UC^ωᵉ (tossʰᶠ ∙ᶠ idealʰᶠ)
coin-toss-from-comʰ =
  toss-over tossʰᶠ ROHU.comQB CTHU.tossʰQB

------------------------------------------------------------------------
-- …at the commitment's own simulator and its own schedule

-- The premise's simulator, certificate and schedule are all in the
-- repository, so `coin-toss-from-comᶜ` narrows it to the one relation that is
-- not (`docs/fcom-extraction.md`'s `raw-emulation`).
comSim : Certified Lkᶠ Advᶠ
comSim = (λ _ → positive 2) , poly-const 2 , λ n → ROU.simᵒ n , qbᵒ (ROU.simQB n)

-- …and the corrupted receiver's, which programs rather than extracts and so
-- costs one downward message per activation instead of two.
comSimʰ : Certified Lkʰᶠ Advʰᶠ
comSimʰ = (λ _ → 1⁺) , poly⁺-1 , λ n → ROHU.simʰᵒ n , qbᵒ (ROHU.simQBʰ n)

coin-toss-from-comᶜ : realᶠ ≈ctx[ εᶜ ] subᶠ comSim idealᶠ
                    → (tossᶠ ∙ᶠ realᶠ) ≤UC^ωᵉ (tossᶠ ∙ᶠ idealᶠ)
coin-toss-from-comᶜ e = coin-toss-from-com (comSim , εᶜ , εᶜ-negligible , e)

-- The commitment's own formula, unrescaled: the stage enters the grading at
-- `1⁺` (`Examples.CoinToss.UC.tossQB`) and the upper simulator is `idᶜ`.
composed-ε : (n q : ℕ) → εᶜᵗ εᶜ n q ≡ fromℕ (q * q + q + q) *ℚ inv-pow-2 n
composed-ε n q = trans (+-identityˡ _) (cong (εᶜ n) (*-identityʳ q))
