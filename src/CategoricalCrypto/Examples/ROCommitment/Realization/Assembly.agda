{-# OPTIONS --safe --without-K --guardedness #-}

-- The commitment's emulation at the resource-installed boundary
-- (`docs/rcom-icom-b1.md`), and the coin-toss assembly from it.
--
-- `Examples.CoinToss.Ideal.Compose.coin-toss-ideal` and its corrupted-receiver
-- twin take the commitment's emulation at the open resource domain, i.e. over
-- every query-bounded resource, while the game bound behind it is proved
-- against one lazily sampled oracle and cell.  `Realization`/`Realizationʰ`
-- state the comparison with `Examples.ROCommitment.Resource.resource`
-- installed below both sides; `assembly`/`assemblyʰ` derive the coin-toss
-- conclusions from it at the same schedules (`pin`/`pinʰ`).

open import Categories.LocallyGraded.SubCategory

open import Data.Nat.Base
open import Data.Nat.Positive
open import Data.Nat.Properties
open import Data.Product.Base
open import Relation.Binary.PropositionalEquality

open import CategoricalCrypto.Examples.CoinToss.Compose
open import CategoricalCrypto.Examples.CoinToss.Ideal.Compose
open import CategoricalCrypto.Examples.CoinToss.Ideal.Receiver.Compose
open import CategoricalCrypto.UC.Model.Dominated
open import CategoricalCrypto.UC.Model.Enrichment
open import CategoricalCrypto.UC.Model.Family
open import CategoricalCrypto.UC.Model.Family.Contextual
open import CategoricalCrypto.UC.Model.Observation
open import CategoricalCrypto.UC.Model.Setup

import CategoricalCrypto.Examples.CoinToss.Hiding.UC as CTHU
import CategoricalCrypto.Examples.CoinToss.UC as CTU
import CategoricalCrypto.Examples.ROCommitment.Hiding.UC as ROHU
import CategoricalCrypto.Examples.ROCommitment.UC as ROU

module CategoricalCrypto.Examples.ROCommitment.Realization.Assembly where

open GradedSubCat gradingᵒ
open Compose

------------------------------------------------------------------------
-- The two compared systems, at the resource-installed boundary

Rcom : Homᶠ (λ _ → 𝟘ᵒ) Advᶠ Honᶠ
Rcom n = realᶠ n ∘ resᶠ n

Icom : Homᶠ (λ _ → 𝟘ᵒ) Lkᶠ Honᶠ
Icom n = idealᶠ n ∘ resᶠ n

Rcomʰ : Homᶠ (λ _ → 𝟘ᵒ) Advʰᶠ Honʰᶠ
Rcomʰ n = realʰᶠ n ∘ resᶠ n

Icomʰ : Homᶠ (λ _ → 𝟘ᵒ) Lkʰᶠ Honʰᶠ
Icomʰ n = idealʰᶠ n ∘ resᶠ n

------------------------------------------------------------------------
-- The theorem to prove

Realization Realizationʰ : Set _
Realization  = Rcom  ≤UC^ωᵉ Icom
Realizationʰ = Rcomʰ ≤UC^ωᵉ Icomʰ

------------------------------------------------------------------------
-- The two real resource-installed families are closed

RcomQB : (n : ℕ) → Pred 1⁺ (Rcom n)
RcomQB n = pred-sub ≤-refl (pred-∘ (ROU.recvQB n) (ROU.resourceQBᵒ n))

RcomʰQB : (n : ℕ) → Pred 1⁺ (Rcomʰ n)
RcomʰQB n = pred-sub ≤-refl (pred-∘ (ROHU.comQB n) (ROU.resourceQBᵒ n))

------------------------------------------------------------------------
-- The first hop, over the closed boundary

-- `Examples.CoinToss.Compose.coin-toss-from-com` at the resource-installed
-- pair.
coin-from-Rcom : Realization → (tossᶠ ∙ᶠ Rcom) ≤UC^ωᵉ (tossᶠ ∙ᶠ Icom)
coin-from-Rcom = toss-over tossᶠ RcomQB CTU.tossQB

coin-from-Rcomʰ : Realizationʰ → (tossʰᶠ ∙ᶠ Rcomʰ) ≤UC^ωᵉ (tossʰᶠ ∙ᶠ Icomʰ)
coin-from-Rcomʰ = toss-over tossʰᶠ RcomʰQB CTHU.tossʰQB

------------------------------------------------------------------------
-- …and the whole assembly

-- `UC-composeᵉ` builds `toss ∙ᶠ (real ∘ res)` where the coin hybrid wants
-- `(toss ∙ᶠ real) ∘ res`: one `sym-assoc` apart.
assembly : Realization → (λ n → (tossᶠ ∙ᶠ realᶠ) n ∘ resᶠ n) ≤UC^ωᵉ Fcoinᶠ
assembly w =
  ≤UC^ωᵉ-trans (≤UC^ωᵉ-resp (λ _ → sym-assoc) (λ _ → sym-assoc) (coin-from-Rcom w))
               coin-hybridᵉ

assemblyʰ : Realizationʰ → (λ n → (tossʰᶠ ∙ᶠ realʰᶠ) n ∘ resᶠ n) ≤UC^ωᵉ Fcoinʰᶠ
assemblyʰ w =
  ≤UC^ωᵉ-trans (≤UC^ωᵉ-resp (λ _ → sym-assoc) (λ _ → sym-assoc) (coin-from-Rcomʰ w))
               coin-hybridʳ

pin : (w : Realization) → proj₁ (proj₂ (assembly w)) ≡ εᶜⁱ (proj₁ (proj₂ w))
pin _ = refl

pinʰ : (w : Realizationʰ) → proj₁ (proj₂ (assemblyʰ w)) ≡ εᶜʳ (proj₁ (proj₂ w))
pinʰ _ = refl
