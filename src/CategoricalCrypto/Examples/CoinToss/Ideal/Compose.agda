{-# OPTIONS --safe --without-K --guardedness #-}

-- The second hop, and the whole statement: Blum coin-tossing over the
-- hash-based commitment, over the concrete resource, emulates an IDEAL COIN.
--
-- The comparison boundary is CLOSED.  `docs/coin-toss.md` §5 shows why it has
-- to be: at an open domain `_≈ctx[_]_`'s closure quantifier owns `F_com`'s
-- memory, and nothing says the cell returns the bit it was given.  Plugging
-- `Examples.ROCommitment.Resource.resource` under both sides takes that memory
-- out of the context's hands, and it is free — the resource is closed, so
-- `UC.Asymptotic.Compose.≈ctx-dom` moves it into the closure at rate `0`,
-- where `ctxBudget`'s guard swallows the factor and the schedule is unchanged.
-- No `Allowance-mono` is spent anywhere.
--
-- The premise is still the commitment's own UC-level ε-statement, exactly as
-- in `Examples.CoinToss.Compose`; the second hop adds `0ℚ` to its schedule.

open import Data.Nat.Base using (ℕ; _*_; _+_)
open import Data.Nat.Poly using (poly-const)
open import Data.Product.Base using (_,_; proj₁; proj₂)
open import Data.Rational as ℚ using (ℚ; 0ℚ) renaming (_*_ to _*ℚ_)
open import Data.Rational.Properties using (+-identityʳ)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans)

open import ProbabilisticLogic.Distribution.Uniform using (fromℕ; inv-pow-2)

open import CategoricalCrypto.Examples.CoinToss.Compose
open import CategoricalCrypto.Examples.ROCommitment.Asymptotic using (εᶜ; εᶜ-negligible)
open import CategoricalCrypto.UC.Approximate using (Negligible-0)
open import CategoricalCrypto.UC.Asymptotic.Compose
  using (_∙ᶠ_; _⊗ᶠ_; ≤UC^ωᵉ-dom; ≤UC^ωᵉ-trans)
open import CategoricalCrypto.UC.Asymptotic.Contextual
open import CategoricalCrypto.UC.Asymptotic.Family using (≤UC^ωᵉ⇒≤UCᴺ)
open import CategoricalCrypto.UC.Budget using (Budget)
open import CategoricalCrypto.UC.Model.Dominated using (qb-gradedᵒ)
open import CategoricalCrypto.UC.Model.Enrichment using (budgetᵒ)
open import CategoricalCrypto.UC.Model.Family using (PolyQB)
open import CategoricalCrypto.UC.Model.Family.Negligible using (module Canonicalᴺ)
open import CategoricalCrypto.UC.Model.Observation using (𝟘ᵒ)
open import CategoricalCrypto.UC.Model.Seal using (gradedᵒ; ifaceᵒ; procᵒ)
open import CategoricalCrypto.UC.Model.Setup
open import CategoricalCrypto.UC.QueryBound using (qb-closed)

import CategoricalCrypto.Examples.CoinToss.Ideal as CTI
import CategoricalCrypto.Examples.CoinToss.Ideal.UC as CTIU
import CategoricalCrypto.Examples.CoinToss.UC as CTU
import CategoricalCrypto.Examples.ROCommitment.Resource as RR

module CategoricalCrypto.Examples.CoinToss.Ideal.Compose where

open Budget budgetᵒ using (qb-∘; qb-T₁; qb-a⇒)

------------------------------------------------------------------------
-- The closed boundary, and the ideal coin over it

Lkᶜᶠ : ℕ → Channel
Lkᶜᶠ n = ifaceᵒ (CTI.Lkᴵᶜ n)

resᶠ : (n : ℕ) → 𝟘ᵒ ⇒ Resᶠ n
resᶠ n = procᵒ (RR.resource n)

Fcoinᶠ : Homᶠ (λ _ → 𝟘ᵒ) Lkᶜᶠ Honᶜᶠ
Fcoinᶠ n = gradedᵒ (CTI.Fcoin n)

-- The joint simulator, certified: one downward `Lkᴵᶜ` message per activation.
simᶜᶠ : Certified Lkᶜᶠ (Lkᶠ ⊗ᶠ Advᶜᶠ)
simᶜᶠ = (λ n → gradedᵒ (CTI.simJ n)) , (λ _ → 1) , poly-const 1 , CTIU.simJQB

------------------------------------------------------------------------
-- The two hops

-- Exact, hence at the zero schedule: `Examples.CoinToss.Ideal.Machine` is the
-- machine equality and `CTIU.coin-hop` reads it across the seal.
coin-hybridᵉ : (λ n → (tossᶠ ∙ᶠ idealᶠ) n ∘ resᶠ n) ≤UC^ωᵉ Fcoinᶠ
coin-hybridᵉ = simᶜᶠ , (λ _ _ → 0ℚ) , (λ _ _ → Negligible-0) , ≈C⇒≈ctx CTIU.coin-hop

coin-toss-ideal : realᶠ ≤UC^ωᵉ idealᶠ
                → (λ n → (tossᶠ ∙ᶠ realᶠ) n ∘ resᶠ n) ≤UC^ωᵉ Fcoinᶠ
coin-toss-ideal w =
  ≤UC^ωᵉ-trans (≤UC^ωᵉ-dom resᶠ CTIU.resourceQBᵒ (coin-toss-from-com w)) coin-hybridᵉ

------------------------------------------------------------------------
-- …and the schedule the composite carries

-- `≤UC^ωᵉ-trans` reads the second schedule at `simCost q (cost s₁)`, and the
-- second schedule is constantly `0ℚ`, so the whole error is the first hop's —
-- itself the commitment's, unrescaled (`Compose.composed-ε`).
εᶜⁱ : (ℕ → ℕ → ℚ) → ℕ → ℕ → ℚ
εᶜⁱ ε n q = εᶜᵗ ε n q ℚ.+ 0ℚ

schedule-pinⁱ : (w : realᶠ ≤UC^ωᵉ idealᶠ)
              → proj₁ (proj₂ (coin-toss-ideal w)) ≡ εᶜⁱ (proj₁ (proj₂ w))
schedule-pinⁱ _ = refl

------------------------------------------------------------------------
-- …at the commitment's own simulator and schedule

coin-toss-idealᶜ : realᶠ ≈ctx[ εᶜ ] subᶠ comSim idealᶠ
                 → (λ n → (tossᶠ ∙ᶠ realᶠ) n ∘ resᶠ n) ≤UC^ωᵉ Fcoinᶠ
coin-toss-idealᶜ e = coin-toss-ideal (comSim , εᶜ , εᶜ-negligible , e)

ideal-ε : (n q : ℕ) → εᶜⁱ εᶜ n q ≡ fromℕ (q * q + q + q) *ℚ inv-pow-2 n
ideal-ε n q = trans (+-identityʳ _) (composed-ε n q)

------------------------------------------------------------------------
-- …and its consequence in the canonical negligible `UCSetup`

-- Both compared families are CLOSED, so a `Fam`-hom's carried polynomial is
-- the factors' own: `qb-closed` for the ideal coin, and for the real composite
-- the toss stage's `QB 0`, the receiver's `QB 1` and the resource's `QB 0`,
-- whose product the resource takes back to `0`.
FcoinQB : PolyQB Fcoinᶠ
FcoinQB = (λ _ → 0) , poly-const 0 , λ n → qb-gradedᵒ (qb-closed (CTI.Fcoin n))

coinRealQB : PolyQB (λ n → (tossᶠ ∙ᶠ realᶠ) n ∘ resᶠ n)
coinRealQB =
    (λ _ → 0) , poly-const 0
  , λ n → qb-∘ (qb-∘ (qb-∘ qb-a⇒ (qb-T₁ (CTU.tossQB n))) (CTU.recvQB n))
               (CTIU.resourceQBᵒ n)

-- `≤UC^ωᵉ⇒≤UCᴺ` does NOT spend the schedule, so the statement lands in the
-- LOCAL-NEGLIGIBLE `ucSetupᴺ` and not only in the vanishing `Canonical^ω`.
coin-toss-idealᴺ :
    realᶠ ≤UC^ωᵉ idealᶠ
  → Canonicalᴺ._≤UC_ ((λ n → (tossᶠ ∙ᶠ realᶠ) n ∘ resᶠ n) , coinRealQB)
                     (Fcoinᶠ , FcoinQB)
coin-toss-idealᴺ w =
  let s , ε , neg , e = coin-toss-ideal w
  in ≤UC^ωᵉ⇒≤UCᴺ s ε neg coinRealQB FcoinQB e
