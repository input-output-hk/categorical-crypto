{-# OPTIONS --safe --without-K --guardedness #-}

-- `Examples.ROCommitment.Realization.Statement`'s two assembly obligations,
-- discharged: the coin-toss headline theorems follow from the commitment's
-- emulation at the RESOURCE-INSTALLED boundary just as they do from the open
-- one, and at the same schedule.
--
-- The two premises differ by one associativity of `_∘_`: `UC-composeᵉ` builds
-- `tossᶠ ∙ᶠ (realᶠ ∘ resᶠ)` where `coin-hybridᵉ` wants
-- `(tossᶠ ∙ᶠ realᶠ) ∘ resᶠ`, and `≤UC^ωᵉ-resp` rebuilds the witness with the
-- SAME simulator and the SAME schedule, so no allowance moves.  `≤UC^ωᵉ-dom`
-- is not spent here at all — it is what the open-premise proofs use to close
-- the boundary AFTER composing, and this premise is closed already.
--
-- The two pins are the point: `assembly` carries `εᶜⁱ` and `assemblyʰ` carries
-- `εᶜʳ`, the very expressions `Ideal.Compose.schedule-pinⁱ` and
-- `Ideal.Receiver.Compose.schedule-pinʳ` pin for the open premise, so moving
-- the boundary changes no number.

open import Data.Nat.Base using (ℕ)
open import Data.Nat.Poly using (poly-const)
open import Data.Product.Base using (_,_; proj₁; proj₂)
open import Data.Rational as ℚ using (0ℚ)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import CategoricalCrypto.Examples.CoinToss.Compose
open import CategoricalCrypto.Examples.CoinToss.Ideal.Compose
  using (coin-hybridᵉ; resᶠ; εᶜⁱ)
open import CategoricalCrypto.Examples.CoinToss.Ideal.Receiver.Compose
  using (coin-hybridʳ; εᶜʳ)
open import CategoricalCrypto.Examples.ROCommitment.Realization.Statement
open import CategoricalCrypto.UC.Approximate using (Negligible-0)
open import CategoricalCrypto.UC.Asymptotic.Compose
  using (UC-composeᵉ; _∙ᶠ_; ≤UC^ωᵉ-trans)
open import CategoricalCrypto.UC.Asymptotic.Contextual
open import CategoricalCrypto.UC.Budget using (Budget)
open import CategoricalCrypto.UC.Model.Dominated using (qb-gradedᵒ)
open import CategoricalCrypto.UC.Model.Enrichment using (budgetᵒ)
open import CategoricalCrypto.UC.Model.Family using (PolyQB)
open import CategoricalCrypto.UC.Model.Setup

import CategoricalCrypto.Examples.CoinToss.Hiding.UC as CTHU
import CategoricalCrypto.Examples.CoinToss.Ideal.UC as CTIU
import CategoricalCrypto.Examples.CoinToss.UC as CTU
import CategoricalCrypto.Examples.ROCommitment.Hiding.UC as ROHU
import CategoricalCrypto.Examples.ROCommitment.UC as ROU

module CategoricalCrypto.Examples.ROCommitment.Realization.Assembly where

open Budget budgetᵒ using (QB; qb-∘)

------------------------------------------------------------------------
-- The four resource-installed families are closed

-- The resource is `QB 0`, and the product of any rate with it is `0`.
RcomQB : (n : ℕ) → QB 0 (Rcom n)
RcomQB n = qb-∘ (CTU.recvQB n) (CTIU.resourceQBᵒ n)

RcomʰQB : (n : ℕ) → QB 0 (Rcomʰ n)
RcomʰQB n = qb-∘ (CTHU.comQB n) (CTIU.resourceQBᵒ n)

RcomPolyQB : PolyQB Rcom
RcomPolyQB = (λ _ → 0) , poly-const 0 , RcomQB

IcomPolyQB : PolyQB Icom
IcomPolyQB =
  (λ _ → 0) , poly-const 0 , λ n → qb-∘ (qb-gradedᵒ (ROU.idealQB n)) (CTIU.resourceQBᵒ n)

RcomʰPolyQB : PolyQB Rcomʰ
RcomʰPolyQB = (λ _ → 0) , poly-const 0 , RcomʰQB

IcomʰPolyQB : PolyQB Icomʰ
IcomʰPolyQB =
  (λ _ → 0) , poly-const 0 , λ n → qb-∘ (qb-gradedᵒ (ROHU.idealʰQB n)) (CTIU.resourceQBᵒ n)

------------------------------------------------------------------------
-- The first hop, over the closed boundary

-- `Examples.CoinToss.Compose.coin-toss-from-com` with the commitment replaced
-- by the resource-installed pair: the upper stage is still compared with
-- itself at the zero schedule, and the moved morphisms are now closed.
coin-from-Rcom : Realization → (tossᶠ ∙ᶠ Rcom) ≤UC^ωᵉ (tossᶠ ∙ᶠ Icom)
coin-from-Rcom (sf , εf , nf , ef) =
  UC-composeᵉ sf εf nf ef
              idᶜ (λ _ _ → 0ℚ) (λ _ _ → Negligible-0)
              (≈C⇒≈ctx λ n → Equiv.sym (sub-identityˡ (tossᶠ n)))
              (λ _ → 0) (poly-const 0) RcomQB
              (λ _ → 0) (poly-const 0) CTU.tossQB

coin-from-Rcomʰ : Realizationʰ → (tossʰᶠ ∙ᶠ Rcomʰ) ≤UC^ωᵉ (tossʰᶠ ∙ᶠ Icomʰ)
coin-from-Rcomʰ (sf , εf , nf , ef) =
  UC-composeᵉ sf εf nf ef
              idᶜ (λ _ _ → 0ℚ) (λ _ _ → Negligible-0)
              (≈C⇒≈ctx λ n → Equiv.sym (sub-identityˡ (tossʰᶠ n)))
              (λ _ → 0) (poly-const 0) RcomʰQB
              (λ _ → 1) (poly-const 1) CTHU.tossʰQB

------------------------------------------------------------------------
-- …and the whole assembly

assembly : Assembly
assembly w =
  ≤UC^ωᵉ-trans (≤UC^ωᵉ-resp (λ _ → sym-assoc) (λ _ → sym-assoc) (coin-from-Rcom w))
               coin-hybridᵉ

assemblyʰ : Assemblyʰ
assemblyʰ w =
  ≤UC^ωᵉ-trans (≤UC^ωᵉ-resp (λ _ → sym-assoc) (λ _ → sym-assoc) (coin-from-Rcomʰ w))
               coin-hybridʳ

pin : (w : Realization) → proj₁ (proj₂ (assembly w)) ≡ εᶜⁱ (proj₁ (proj₂ w))
pin _ = refl

pinʰ : (w : Realizationʰ) → proj₁ (proj₂ (assemblyʰ w)) ≡ εᶜʳ (proj₁ (proj₂ w))
pinʰ _ = refl
