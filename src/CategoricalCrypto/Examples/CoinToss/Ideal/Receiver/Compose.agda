{-# OPTIONS --safe --without-K --guardedness #-}

-- The corrupted-RECEIVER second hop, and the whole statement at that
-- corruption: Blum coin-tossing over the hash-based commitment, over the
-- concrete resource, emulates an IDEAL COIN.
--
-- `Examples.CoinToss.Ideal.Compose` is the corrupted-committer twin and the
-- assembly is its: the comparison boundary is CLOSED (`≤UC^ωᵉ-dom` at the
-- resource, free), the premise is the commitment's own UC-level ε-statement,
-- and `≤UC^ωᵉ-trans` puts the two hops together.
--
-- What differs is the second hop's error.  The committer's is EXACT, because
-- there the coin's draw and its use land in the same activation and the two
-- systems are equal as MACHINES.  Here they are not — the honest committer's
-- share is drawn when the environment starts it and read when the corrupted
-- receiver answers, so the ideal coin draws one activation later
-- (`docs/coin-toss.md` §5).  What is exact is the two systems' RUNS
-- (`Receiver.Machine.coin-runʰ`), at every strategy and with no budget
-- condition, and carrying a run agreement into a CONTEXT costs the
-- domination's positive slack.  So this hop lands at `2⁻ⁿ`, not at `0`, and
-- the composed schedule is the hiding bound PLUS that slack.

open import Data.Nat.Base using (ℕ; _+_)
open import Data.Nat.Poly using (poly-const)
open import Data.Nat.Properties using (*-identityʳ; ≤-refl)
open import Data.Product.Base using (_,_; proj₁; proj₂)
open import Data.Rational as ℚ using (ℚ; 0ℚ) renaming (_*_ to _*ℚ_)
open import Data.Rational.Properties using (+-identityˡ)
open import Relation.Binary.PropositionalEquality using (_≡_; cong; cong₂; refl; trans)

open import ProbabilisticLogic.Distribution.Uniform using (fromℕ; inv-pow-2)
open import ProbabilisticLogic.Dp.Advantage using (≈ₚ⇒≈ₚ[0])

open import CategoricalCrypto.Iface using (_⊗ᴵ_)

open import CategoricalCrypto.Examples.CoinToss.Compose
open import CategoricalCrypto.Examples.CoinToss.Ideal.Compose using (resᶠ)
open import CategoricalCrypto.Examples.CoinToss.Ideal.Receiver.Dominated using (dominatedᵍ)
open import CategoricalCrypto.Examples.ROCommitment.Hiding.Asymptotic using (εᵗ; εᵗ-negligible)
open import CategoricalCrypto.UC.Approximate
  using (GradedBound-+[_]; Negligible; Negligible-+; Negligible-0; NegligibleBound)
open import CategoricalCrypto.UC.Approximate.Decay using (negligible-slack; 0<inv-pow-2)
open import CategoricalCrypto.UC.Asymptotic.Compose
  using (_∙ᶠ_; _⊗ᶠ_; ≤UC^ωᵉ-dom; ≤UC^ωᵉ-trans)
open import CategoricalCrypto.UC.Asymptotic.Contextual
open import CategoricalCrypto.UC.Model.Observation using (𝟘ᵒ)
open import CategoricalCrypto.UC.Model.Seal using (gradedᵒ; ifaceᵒ)
open import CategoricalCrypto.UC.Model.Setup

import CategoricalCrypto.Examples.CoinToss.Hiding as CTH
import CategoricalCrypto.Examples.CoinToss.Ideal.Receiver as CTR
import CategoricalCrypto.Examples.CoinToss.Ideal.Receiver.Hybrid as CTRH
import CategoricalCrypto.Examples.CoinToss.Ideal.Receiver.Machine as CTRM
import CategoricalCrypto.Examples.CoinToss.Ideal.Receiver.UC as CTRU
import CategoricalCrypto.Examples.CoinToss.Ideal.UC as CTIU
import CategoricalCrypto.Examples.ROCommitment.Hiding as ROH

module CategoricalCrypto.Examples.CoinToss.Ideal.Receiver.Compose where

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

-- The two compared systems at that spelling: the hybrid as one closed
-- machine, and the joint simulator over the ideal coin as another.
hybʰᶠ idlʰᶠ : Homᶠ (λ _ → 𝟘ᵒ) Lk♯ᶠ Honᶜʰᶠ
hybʰᶠ n = gradedᵒ (CTRH.hybridᴹʰ n)
idlʰᶠ n = gradedᵒ (CTRM.idealᴹʰ n)

-- The joint simulator, certified: one downward `Lkᴵᶜʰ` message per activation.
simᶜʰᶠ : Certified Lkᶜʰᶠ (Lkʰᶠ ⊗ᶠ Advᶜʰᶠ)
simᶜʰᶠ = (λ n → gradedᵒ (CTR.simJʰ n)) , (λ _ → 1) , poly-const 1 , CTRU.simJʰQB

flatᶜʰ : Certified Lk♯ᶠ (Lkʰᶠ ⊗ᶠ Advᶜʰᶠ)
flatᶜʰ = CTRU.flatʰ , (λ _ → 1) , poly-const 1 , CTRU.flatʰQB

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

-- `Receiver.Machine.coin-runʰ` under every ancilla context, at the grade the
-- seal hands a single `gradedᵒ`.
coin-ctxᴬʰ : hybʰᶠ ≈ctxᴬ[ ηʰ ] idlʰᶠ
coin-ctxᴬʰ n W E m qE qm =
  dominatedᵍ W E m qE qm (CTRH.hybridᴹʰ n) (CTRM.idealᴹʰ n)
             0ℚ (inv-pow-2 n) (0<inv-pow-2 n) (λ d → ≈ₚ⇒≈ₚ[0] (CTRM.coin-runʰ n d))

-- …regraded to the spelling the composition produces, which costs nothing:
-- the regrading is the identity process, so `simCost _ 1` reads the schedule
-- at an allowance it does not depend on.
coin-hybridʳ : (λ n → (tossʰᶠ ∙ᶠ idealʰᶠ) n ∘ resᶠ n) ≤UC^ωᵉ Fcoinʰᶠ
coin-hybridʳ =
    simᶜʰᶠ , ηʰ , ηʰ-negligible
  , ≈ctx-resp ηʰ CTRU.hyb-flatʰ CTRU.idl-flatʰ
      (≈ctx-sub flatᶜʰ ηʰ (≈ctxᴬ⇒≈ctx ηʰ coin-ctxᴬʰ))

------------------------------------------------------------------------
-- …and the whole statement

coin-toss-idealʳ : realʰᶠ ≤UC^ωᵉ idealʰᶠ
                 → (λ n → (tossʰᶠ ∙ᶠ realʰᶠ) n ∘ resᶠ n) ≤UC^ωᵉ Fcoinʰᶠ
coin-toss-idealʳ w =
  ≤UC^ωᵉ-trans (≤UC^ωᵉ-dom resᶠ CTIU.resourceQBᵒ (coin-toss-from-comʰ w)) coin-hybridʳ

-- `≤UC^ωᵉ-trans` reads the second schedule at `simCost q (cost s₁ n)`, and
-- `ηʰ` does not depend on its allowance, so the reindexing changes nothing.
εᶜʳ : (ℕ → ℕ → ℚ) → ℕ → ℕ → ℚ
εᶜʳ ε n q = εᶜᵗ ε n q ℚ.+ ηʰ n q

-- Mechanical, not a copied formula: this stops checking the moment the
-- substitution changes.
schedule-pinʳ : (w : realʰᶠ ≤UC^ωᵉ idealʰᶠ)
              → proj₁ (proj₂ (coin-toss-idealʳ w)) ≡ εᶜʳ (proj₁ (proj₂ w))
schedule-pinʳ _ = refl

-- …at the commitment's own hiding schedule: the hiding bound, unrescaled,
-- plus the one slack the run-level hop spends.
ideal-εʳ : (n q : ℕ) → εᶜʳ εᵗ n q ≡ fromℕ (q + (q + q)) *ℚ inv-pow-2 n ℚ.+ inv-pow-2 n
ideal-εʳ n q = cong₂ ℚ._+_ (trans (+-identityˡ _) (cong (εᵗ n) (*-identityʳ q)))
                           (+-identityˡ (inv-pow-2 n))
