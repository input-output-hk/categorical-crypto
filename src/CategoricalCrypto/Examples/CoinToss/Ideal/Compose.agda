{-# OPTIONS --safe --without-K --guardedness #-}

-- The second hop, and the whole statement: Blum coin-tossing over the
-- hash-based commitment, over the concrete resource, emulates an ideal coin.
--
-- The comparison boundary is closed: at an open domain the closure quantifier
-- of `_≈ctx[_]_` owns `F_com`'s memory, and nothing says the cell returns the
-- bit it was given (`docs/coin-toss.md` §5).  Plugging `resource` under both
-- sides is free: it is closed, so `≈ctx-dom` absorbs it at rate `1⁺`.

open import Categories.LocallyGraded.SubCategory

open import Data.Nat.Base
open import Data.Nat.Positive
open import Data.Nat.Properties using (≤-refl)
open import Data.Product.Base
open import Data.Rational as ℚ using (ℚ; 0ℚ) renaming (_*_ to _*ℚ_)
open import Data.Rational.Properties using (+-identityʳ)
open import Relation.Binary.PropositionalEquality

open import ProbabilisticLogic.Distribution.Uniform

open import CategoricalCrypto.Examples.CoinToss.Compose
open import CategoricalCrypto.Examples.ROCommitment.Asymptotic
open import CategoricalCrypto.UC.Approximate
open import CategoricalCrypto.UC.Model.Dominated
open import CategoricalCrypto.UC.Model.Enrichment
open import CategoricalCrypto.UC.Model.Family
open import CategoricalCrypto.UC.Model.Family.Contextual
open import CategoricalCrypto.UC.Model.Family.Emulation
open import CategoricalCrypto.UC.Model.Observation
open import CategoricalCrypto.UC.Model.Seal
open import CategoricalCrypto.UC.Model.Setup
open import CategoricalCrypto.UC.QueryBound using (qb-closed; qb-mono)

import CategoricalCrypto.Examples.CoinToss.Ideal as CTI
import CategoricalCrypto.Examples.CoinToss.Ideal.UC as CTIU
import CategoricalCrypto.Examples.CoinToss.UC as CTU
import CategoricalCrypto.Examples.ROCommitment.Resource as RR
import CategoricalCrypto.Examples.ROCommitment.UC as ROU

module CategoricalCrypto.Examples.CoinToss.Ideal.Compose where

open Compose

open GradedSubCat gradingᵒ

------------------------------------------------------------------------
-- The closed boundary, and the ideal coin over it

Lkᶜᶠ : ℕ → Channel
Lkᶜᶠ n = ifaceᵒ (CTI.Lkᴵᶜ n)

resᶠ : (n : ℕ) → 𝟘ᵒ ⇒ Resᶠ n
resᶠ n = procᵒ (RR.resource n)

Fcoinᶠ : Homᶠ (λ _ → 𝟘ᵒ) Lkᶜᶠ Honᶜᶠ
Fcoinᶠ n = gradedᵒ (CTI.Fcoin n)

simᶜᶠ : Certified Lkᶜᶠ (Lkᶠ ⊗ᶠ Advᶜᶠ)
simᶜᶠ = (λ _ → 1⁺) , poly⁺-1 , λ n → gradedᵒ (CTI.simJ n) , CTIU.simJQB n

------------------------------------------------------------------------
-- The second hop

coin-hybridᵇ : (λ n → (tossᶠ ∙ᶠ idealᶠ) n ∘ resᶠ n) ≤UC[ simᶜᶠ , (λ _ _ → 0ℚ) ] Fcoinᶠ
coin-hybridᵇ = ≈C⇒≈ctx CTIU.coin-hop

coin-hybridᵉ : (λ n → (tossᶠ ∙ᶠ idealᶠ) n ∘ resᶠ n) ≤UC^ωᵉ Fcoinᶠ
coin-hybridᵉ = simᶜᶠ , (λ _ _ → 0ℚ) , (λ _ _ → Negligible-0) , coin-hybridᵇ

------------------------------------------------------------------------
-- …and the simulator and the schedule the composite carries

εᶜⁱ : (ℕ → ℕ → ℚ) → ℕ → ℕ → ℚ
εᶜⁱ ε n q = εᶜᵗ ε n q ℚ.+ 0ℚ

simᶜⁱ : Certified Lkᶠ Advᶠ → Certified Lkᶜᶠ (Advᶠ ⊗ᶠ Advᶜᶠ)
simᶜⁱ sf = simᶜᵗ sf ∘ᶜ simᶜᶠ

coin-toss-idealᵇ : (sf : Certified Lkᶠ Advᶠ) (εf : ℕ → ℕ → ℚ)
                 → realᶠ ≤UC[ sf , εf ] idealᶠ
                 → (λ n → (tossᶠ ∙ᶠ realᶠ) n ∘ resᶠ n) ≤UC[ simᶜⁱ sf , εᶜⁱ εf ] Fcoinᶠ
coin-toss-idealᵇ sf εf ef =
  ≤UC[]-trans (simᶜᵗ sf) simᶜᶠ (εᶜᵗ εf) (λ _ _ → 0ℚ)
    (≤UC[]-dom resᶠ (λ n → imageᵒ (ROU.resourceQBᵒ n)) (simᶜᵗ sf) (εᶜᵗ εf)
               (coin-toss-from-comᵇ sf εf ef))
    coin-hybridᵇ

coin-toss-ideal : realᶠ ≤UC^ωᵉ idealᶠ → (λ n → (tossᶠ ∙ᶠ realᶠ) n ∘ resᶠ n) ≤UC^ωᵉ Fcoinᶠ
coin-toss-ideal (sf , εf , nf , ef) =
    simᶜⁱ sf , εᶜⁱ εf
  , seqError-negligible (simᶜᵗ {Advᶜ = Advᶜᶠ} sf) (εᶜᵗ εf) (λ _ _ → 0ℚ)
                        (εᶜᵗ-negligible εf nf) (λ _ _ → Negligible-0)
  , coin-toss-idealᵇ sf εf ef

------------------------------------------------------------------------
-- …at the commitment's own simulator and schedule

coin-toss-idealᶜ : realᶠ ≈ctx[ εᶜ ] subᶠ comSim idealᶠ
                 → (λ n → (tossᶠ ∙ᶠ realᶠ) n ∘ resᶠ n) ≤UC^ωᵉ Fcoinᶠ
coin-toss-idealᶜ e = coin-toss-ideal (comSim , εᶜ , εᶜ-negligible , e)

ideal-ε : (n q : ℕ) → εᶜⁱ εᶜ n q ≡ fromℕ (q * q + q + q) *ℚ inv-pow-2 n
ideal-ε n q = trans (+-identityʳ _) (composed-ε n q)

------------------------------------------------------------------------
-- …and its consequence in the canonical negligible `UCSetup`

-- Both families are closed, so they enter `Famᴹ` at the unit rate.
Fcoinʷ : Δ 𝟘ᵒ ⇒^ω (Lkᶜᶠ ⊛ω Honᶜᶠ)
Fcoinʷ = (λ _ → 1⁺) , poly⁺-1
       , λ n → Fcoinᶠ n , qb-gradedᵒ (qb-mono z≤n (qb-closed (CTI.Fcoin n)))

coinRealʷ : Δ 𝟘ᵒ ⇒^ω ((Advᶠ ⊗ᶠ Advᶜᶠ) ⊛ω Honᶜᶠ)
coinRealʷ =
    (λ _ → 1⁺) , poly⁺-1
  , λ n → (tossᶠ ∙ᶠ realᶠ) n ∘ resᶠ n
        , pred-sub ≤-refl
            (pred-∘ (pred-∘ (pred-∘ pred-α⇐ (pred-⊗ pred-id (CTU.tossQB n))) (ROU.recvQB n))
                    (ROU.resourceQBᵒ n))

-- `≤UC[]⇒≤UCᴺ` does not go through the vanishing collapse, so the statement
-- lands in the LOCAL-NEGLIGIBLE `ucSetupᴺ` and not only in `Canonical^ω`.
-- What it keeps is the certified simulator and a negligible witness chosen
-- per context — NOT `εᶜⁱ` itself, which stays at `coin-toss-idealᵇ`.
coin-toss-idealᴺ : realᶠ ≤UC^ωᵉ idealᶠ → coinRealʷ Canonicalᴺ.≤UC Fcoinʷ
coin-toss-idealᴺ w =
  let s , ε , neg , e = coin-toss-ideal w
  in ≤UC[]⇒≤UCᴺ s ε neg coinRealʷ Fcoinʷ e
