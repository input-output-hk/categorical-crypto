{-# OPTIONS --safe --without-K --guardedness #-}

-- The boundary of the commitment realization the coin-toss headline theorems
-- still assume, as checked types rather than prose: `docs/rcom-icom-b1.md`.
--
-- `Examples.CoinToss.Ideal.Compose.coin-toss-ideal` and its corrupted-receiver
-- twin take the commitment's emulation at the OPEN resource domain.  That
-- premise quantifies the closure over every query-bounded resource, where the
-- game bound behind it (`Examples.ROCommitment.Game.extraction-bound`) is
-- proved against ONE lazily-sampled oracle and one-shot cell.  `Realization`
-- is the same comparison with `Examples.ROCommitment.Resource.resource`
-- installed below both sides, which is the boundary the game can reach, and
-- `Assembly` is what a proof of it still owes the headline theorem.
--
-- The channel families are `Examples.CoinToss.Compose`'s, where they were
-- first named; nothing here is a new machine.

open import CategoricalCrypto.Examples.CoinToss.Compose
open import CategoricalCrypto.Examples.CoinToss.Ideal.Compose using (Fcoinᶠ; resᶠ)
open import CategoricalCrypto.Examples.CoinToss.Ideal.Receiver.Compose using (Fcoinʰᶠ)
open import CategoricalCrypto.UC.Asymptotic.Compose using (_∙ᶠ_)
open import CategoricalCrypto.UC.Asymptotic.Contextual using (Homᶠ; _≤UC^ωᵉ_)
open import CategoricalCrypto.UC.Model.Observation using (𝟘ᵒ)
open import CategoricalCrypto.UC.Model.Setup

module CategoricalCrypto.Examples.ROCommitment.Realization.Statement where

------------------------------------------------------------------------
-- The two compared systems, at the resource-installed boundary

-- The corrupted-committer pair: the honest receiver and the ideal
-- functionality, each over the concrete resource, hence CLOSED in their domain
-- and still graded by the corrupted committer's port.
Rcom : Homᶠ (λ _ → 𝟘ᵒ) Advᶠ Honᶠ
Rcom n = realᶠ n ∘ resᶠ n

Icom : Homᶠ (λ _ → 𝟘ᵒ) Lkᶠ Honᶠ
Icom n = idealᶠ n ∘ resᶠ n

-- …and the corrupted-receiver pair.
Rcomʰ : Homᶠ (λ _ → 𝟘ᵒ) Advʰᶠ Honʰᶠ
Rcomʰ n = realʰᶠ n ∘ resᶠ n

Icomʰ : Homᶠ (λ _ → 𝟘ᵒ) Lkʰᶠ Honʰᶠ
Icomʰ n = idealʰᶠ n ∘ resᶠ n

------------------------------------------------------------------------
-- The theorem to prove, and what consuming it still owes

Realization Realizationʰ : Set _
Realization  = Rcom  ≤UC^ωᵉ Icom
Realizationʰ = Rcomʰ ≤UC^ωᵉ Icomʰ

-- The assembly obligations: the conclusions of `coin-toss-ideal` and
-- `coin-toss-idealʳ` from the resource-installed premise instead of the open
-- one.  The two parenthesizations differ by one associativity of `_∘_`.
Assembly Assemblyʰ : Set _
Assembly  = Realization  → (λ n → (tossᶠ  ∙ᶠ realᶠ)  n ∘ resᶠ n) ≤UC^ωᵉ Fcoinᶠ
Assemblyʰ = Realizationʰ → (λ n → (tossʰᶠ ∙ᶠ realʰᶠ) n ∘ resᶠ n) ≤UC^ωᵉ Fcoinʰᶠ
