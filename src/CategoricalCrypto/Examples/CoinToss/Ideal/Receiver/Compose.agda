{-# OPTIONS --safe --without-K --guardedness #-}

-- The corrupted-receiver second hop, and the whole statement at that
-- corruption: Blum coin-tossing over the hash-based commitment, over the
-- concrete resource, emulates an ideal coin.
--
-- Assembled as `Examples.CoinToss.Ideal.Compose`, except for the second hop's
-- error.  The honest committer's share is drawn when the environment starts
-- it and read when the corrupted receiver answers, so the ideal coin draws one
-- activation later (`docs/coin-toss.md` §5) and the two systems agree only as
-- runs (`Receiver.Machine.coin-runʰ`).  Carrying a run agreement into a
-- context costs the domination's positive slack, so this hop lands at `2⁻ⁿ`.

open import Categories.LocallyGraded.SubCategory

open import Data.Nat.Base
open import Data.Nat.Positive
open import Data.Nat.Properties using (*-identityʳ; ≤-refl)
open import Data.Product.Base
open import Data.Rational as ℚ using (ℚ; 0ℚ) renaming (_*_ to _*ℚ_)
open import Data.Rational.Properties using (+-identityˡ)
open import Relation.Binary.PropositionalEquality

open import ProbabilisticLogic.Distribution.Uniform
open import ProbabilisticLogic.Dp.Advantage

open import CategoricalCrypto.Iface

open import CategoricalCrypto.Examples.CoinToss.Compose
open import CategoricalCrypto.Examples.CoinToss.Ideal.Compose
open import CategoricalCrypto.Examples.ROCommitment.Hiding.Asymptotic
open import CategoricalCrypto.UC.Approximate
open import CategoricalCrypto.UC.Approximate.Decay
open import CategoricalCrypto.UC.Model.Dominated
open import CategoricalCrypto.UC.Model.Enrichment
open import CategoricalCrypto.UC.Model.Family
open import CategoricalCrypto.UC.Model.Family.Contextual
open import CategoricalCrypto.UC.Model.Family.Emulation
open import CategoricalCrypto.UC.Model.Observation
open import CategoricalCrypto.UC.Model.Seal
open import CategoricalCrypto.UC.Model.Setup
open import CategoricalCrypto.UC.QueryBound using (qb-closed; qb-mono)

import CategoricalCrypto.Examples.CoinToss.Hiding as CTH
import CategoricalCrypto.Examples.CoinToss.Hiding.UC as CTHU
import CategoricalCrypto.Examples.CoinToss.Ideal.Receiver as CTR
import CategoricalCrypto.Examples.CoinToss.Ideal.Receiver.Hybrid as CTRH
import CategoricalCrypto.Examples.CoinToss.Ideal.Receiver.Machine as CTRM
import CategoricalCrypto.Examples.CoinToss.Ideal.Receiver.UC as CTRU
import CategoricalCrypto.Examples.ROCommitment.Hiding as ROH
import CategoricalCrypto.Examples.ROCommitment.Hiding.UC as ROHU
import CategoricalCrypto.Examples.ROCommitment.UC as ROU

module CategoricalCrypto.Examples.CoinToss.Ideal.Receiver.Compose where

open Compose

open GradedSubCat gradingᵒ

------------------------------------------------------------------------
-- The ideal coin over the closed boundary

-- The composed grade in the two spellings the seal keeps apart: `Lk♯ᶠ` is the
-- one a single `gradedᵒ` hands out, `Lkʰᶠ ⊗ᶠ Advᶜʰᶠ` the one `_∙ᶠ_` produces,
-- and `CTRU.flatʰ` is the identity between them.
Lk♯ᶠ Lkᶜʰᶠ : ℕ → Channel
Lk♯ᶠ  n = ifaceᵒ (ROH.Lkᴵʰ n ⊗ᴵ CTH.Advᴵᶜʰ n)
Lkᶜʰᶠ n = ifaceᵒ (CTR.Lkᴵᶜʰ n)

Fcoinʰᶠ : Homᶠ (λ _ → 𝟘ᵒ) Lkᶜʰᶠ Honᶜʰᶠ
Fcoinʰᶠ n = gradedᵒ (CTR.Fcoinʰ n)

hybʰᶠ idlʰᶠ : Homᶠ (λ _ → 𝟘ᵒ) Lk♯ᶠ Honᶜʰᶠ
hybʰᶠ n = gradedᵒ (CTRH.hybridᴹʰ n)
idlʰᶠ n = gradedᵒ (CTRM.idealᴹʰ n)

simᶜʰᶠ : Certified Lkᶜʰᶠ (Lkʰᶠ ⊗ᶠ Advᶜʰᶠ)
simᶜʰᶠ = (λ _ → 1⁺) , poly⁺-1 , λ n → gradedᵒ (CTR.simJʰ n) , CTRU.simJʰQB n

flatᶜʰ : Certified Lk♯ᶠ (Lkʰᶠ ⊗ᶠ Advᶜʰᶠ)
flatᶜʰ = (λ _ → 1⁺) , poly⁺-1 , λ n → CTRU.flatʰ n , CTRU.flatʰQB n

------------------------------------------------------------------------
-- The second hop, and its slack

-- The domination's positive slack, paid at `2⁻ⁿ`: an exact run agreement has
-- no zero instance to hand a context (`UC.Approximate.Decay.negligible-slack`
-- is the same schedule at the same place in `UC.Model.Family.Ingest`).
ηʰ : ℕ → ℕ → ℚ
ηʰ n _ = 0ℚ ℚ.+ inv-pow-2 n

ηʰ-negligible : NegligibleBound ηʰ
ηʰ-negligible =
  GradedBound-+[ Negligible ] Negligible-+ (λ _ _ → 0ℚ) (λ n _ → inv-pow-2 n)
    (λ _ _ → Negligible-0) (λ _ _ → negligible-slack (λ _ → ≤-refl))

coin-ctxᴬʰ : hybʰᶠ ≈ctxᴬ[ ηʰ ] idlʰᶠ
coin-ctxᴬʰ n W E m qE qm =
  dominatedᵍ W E m qE qm (CTRH.hybridᴹʰ n) (CTRM.idealᴹʰ n)
             0ℚ (inv-pow-2 n) (0<inv-pow-2 n) (λ d → ≈ₚ⇒≈ₚ[0] (CTRM.coin-runʰ n d))

-- …regraded to the spelling the composition produces, which costs nothing:
-- the regrading is the identity process, so `scale _ 1⁺` reads the schedule
-- at an allowance it does not depend on.
coin-hybridʳᵇ : (λ n → (tossʰᶠ ∙ᶠ idealʰᶠ) n ∘ resᶠ n) ≤UC[ simᶜʰᶠ , ηʰ ] Fcoinʰᶠ
coin-hybridʳᵇ =
  ≈ctx-resp ηʰ CTRU.hyb-flatʰ CTRU.idl-flatʰ
    (≈ctx-sub flatᶜʰ ηʰ (≈ctxᴬ⇒≈ctx ηʰ coin-ctxᴬʰ))

coin-hybridʳ : (λ n → (tossʰᶠ ∙ᶠ idealʰᶠ) n ∘ resᶠ n) ≤UC^ωᵉ Fcoinʰᶠ
coin-hybridʳ = simᶜʰᶠ , ηʰ , ηʰ-negligible , coin-hybridʳᵇ

------------------------------------------------------------------------
-- …and the whole statement

εᶜʳ : (ℕ → ℕ → ℚ) → ℕ → ℕ → ℚ
εᶜʳ ε n q = εᶜᵗ ε n q ℚ.+ ηʰ n q

simᶜʳ : Certified Lkʰᶠ Advʰᶠ → Certified Lkᶜʰᶠ (Advʰᶠ ⊗ᶠ Advᶜʰᶠ)
simᶜʳ sf = simᶜᵗ sf ∘ᶜ simᶜʰᶠ

coin-toss-idealʳᵇ : (sf : Certified Lkʰᶠ Advʰᶠ) (εf : ℕ → ℕ → ℚ)
                  → realʰᶠ ≤UC[ sf , εf ] idealʰᶠ
                  → (λ n → (tossʰᶠ ∙ᶠ realʰᶠ) n ∘ resᶠ n)
                    ≤UC[ simᶜʳ sf , εᶜʳ εf ] Fcoinʰᶠ
coin-toss-idealʳᵇ sf εf ef =
  ≤UC[]-trans (simᶜᵗ sf) simᶜʰᶠ (εᶜᵗ εf) ηʰ
    (≤UC[]-dom resᶠ (λ n → imageᵒ (ROU.resourceQBᵒ n)) (simᶜᵗ sf) (εᶜᵗ εf)
               (coin-toss-from-comʰᵇ sf εf ef))
    coin-hybridʳᵇ

coin-toss-idealʳ : realʰᶠ ≤UC^ωᵉ idealʰᶠ
                 → (λ n → (tossʰᶠ ∙ᶠ realʰᶠ) n ∘ resᶠ n) ≤UC^ωᵉ Fcoinʰᶠ
coin-toss-idealʳ (sf , εf , nf , ef) =
    simᶜʳ sf , εᶜʳ εf
  , seqError-negligible (simᶜᵗ {Advᶜ = Advᶜʰᶠ} sf) (εᶜᵗ εf) ηʰ
                        (εᶜᵗ-negligible εf nf) ηʰ-negligible
  , coin-toss-idealʳᵇ sf εf ef

coin-toss-idealʳᶜ : realʰᶠ ≈ctx[ εᵗ ] subᶠ comSimʰ idealʰᶠ
                  → (λ n → (tossʰᶠ ∙ᶠ realʰᶠ) n ∘ resᶠ n) ≤UC^ωᵉ Fcoinʰᶠ
coin-toss-idealʳᶜ e = coin-toss-idealʳ (comSimʰ , εᵗ , εᵗ-negligible , e)

ideal-εʳ : (n q : ℕ) → εᶜʳ εᵗ n q ≡ fromℕ (q + (q + q)) *ℚ inv-pow-2 n ℚ.+ inv-pow-2 n
ideal-εʳ n q = cong₂ ℚ._+_ (trans (+-identityˡ _) (cong (εᵗ n) (*-identityʳ q)))
                           (+-identityˡ (inv-pow-2 n))

------------------------------------------------------------------------
-- …and its consequence in the canonical negligible `UCSetup`

Fcoinʰʷ : Δ 𝟘ᵒ ⇒^ω (Lkᶜʰᶠ ⊛ω Honᶜʰᶠ)
Fcoinʰʷ = (λ _ → 1⁺) , poly⁺-1
        , λ n → Fcoinʰᶠ n , qb-gradedᵒ (qb-mono z≤n (qb-closed (CTR.Fcoinʰ n)))

coinRealʰʷ : Δ 𝟘ᵒ ⇒^ω ((Advʰᶠ ⊗ᶠ Advᶜʰᶠ) ⊛ω Honᶜʰᶠ)
coinRealʰʷ =
    (λ _ → 1⁺) , poly⁺-1
  , λ n → (tossʰᶠ ∙ᶠ realʰᶠ) n ∘ resᶠ n
        , pred-sub ≤-refl
            (pred-∘ (pred-∘ (pred-∘ pred-α⇐ (pred-⊗ pred-id (CTHU.tossʰQB n))) (ROHU.comQB n))
                    (ROU.resourceQBᵒ n))

coin-toss-idealʳᴺ : realʰᶠ ≤UC^ωᵉ idealʰᶠ → coinRealʰʷ Canonicalᴺ.≤UC Fcoinʰʷ
coin-toss-idealʳᴺ w =
  let s , ε , neg , e = coin-toss-idealʳ w
  in ≤UC[]⇒≤UCᴺ s ε neg coinRealʰʷ Fcoinʰʷ e
