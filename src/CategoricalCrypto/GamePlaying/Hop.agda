{-# OPTIONS --safe --without-K #-}

-- Assembling a game hop out of `GamePlaying`'s two bridges.
--
--   • `runWith-bisim` — two kernels that are COUPLED step by step (their
--     one-query expectations agree at related states, on any pair of
--     integrands that agrees at related outcomes) run alike at EVERY adaptive
--     distinguisher.  This is the induction that identifies a coupling's
--     marginals with the reference kernels they are supposed to be:
--     `Examples.MerkleDamgard.Core`'s `ghost-erase` (real side) and
--     `ideal-marginal` (ideal side) are its two instances, and both are
--     EXACT — no ε.
--   • `hop-bound` — the ε-statement.  With both marginals identified and a
--     `SuperCert` bounding the coupling's flag, the advantage of any m-query
--     distinguisher between the two REFERENCE kernels is at most `ε m`.
--     `Coupling.FLGP` supplies the identical-until-bad half and
--     `badProb-bounded` the supermartingale half; this is the last step of
--     every proof in that shape.

open import categorical-crypto.Prelude hiding (_>>=_)

open import Data.Rational using (ℚ) renaming (_-_ to _-ℚ_; ∣_∣ to ∣_∣ℚ; _≤_ to _≤ℚ_)
open import Data.Rational.Properties using (≤-trans)

open import CategoricalCrypto.GamePlaying
open import CategoricalCrypto.Interaction
open import CategoricalCrypto.Strategy
open import ProbabilisticLogic.Distribution.RationalDist
open import ProbabilisticLogic.Distribution.RationalDist.Expectation

module CategoricalCrypto.GamePlaying.Hop where

------------------------------------------------------------------------
-- Coupled kernels run alike

module _ {Q R St St′ : Type} (resp : St → Q → Dist-ℚ (St × R))
         (resp′ : St′ → Q → Dist-ℚ (St′ × R)) (_≋_ : St → St′ → Type) where

  -- One query's coupling: at related states the two kernels give the same
  -- expectation to integrands that cannot tell related outcomes apart.  The
  -- relation is what carries the ancillary state one side has and the other
  -- does not (a flag, a ghost table).
  StepBisim : Type
  StepBisim = ∀ s s′ → s ≋ s′ → ∀ q (F : St × R → ℚ) (F′ : St′ × R → ℚ)
            → (∀ t t′ → proj₁ t ≋ proj₁ t′ → proj₂ t ≡ proj₂ t′ → F t ≡ F′ t′)
            → E (resp s q) F ≡ E (resp′ s′ q) F′

  runWith-bisim : StepBisim → ∀ d s s′ → s ≋ s′
                → Pr₁ (runWith resp s d) ≡ Pr₁ (runWith resp′ s′ d)
  runWith-bisim bis (out b) s s′ rel = refl
  runWith-bisim bis (ask q k) s s′ rel =
    trans (Pr₁-bind (resp s q) K)
   (trans (bis s s′ rel q (λ t → Pr₁ (K t)) (λ t′ → Pr₁ (K′ t′)) point)
          (sym (Pr₁-bind (resp′ s′ q) K′)))
    where
      K  = λ (t : St × R) → runWith resp (proj₁ t) (k (proj₂ t))
      K′ = λ (t′ : St′ × R) → runWith resp′ (proj₁ t′) (k (proj₂ t′))
      point : ∀ t t′ → proj₁ t ≋ proj₁ t′ → proj₂ t ≡ proj₂ t′ → Pr₁ (K t) ≡ Pr₁ (K′ t′)
      point t t′ r eq =
        subst (λ z → Pr₁ (K t) ≡ Pr₁ (runWith resp′ (proj₁ t′) (k z))) eq
          (runWith-bisim bis (k (proj₂ t)) (proj₁ t) (proj₁ t′) r)
  runWith-bisim bis (coin μ k) s s′ rel =
    trans (Pr₁-bind μ (λ b → runWith resp s (k b)))
   (trans (lookupᴰℚ-cong-P (entries μ) (λ b → runWith-bisim bis (k b) s s′ rel))
          (sym (Pr₁-bind μ (λ b → runWith resp′ s′ (k b)))))

------------------------------------------------------------------------
-- The hop

module _ {Q R St StR StI : Type} (bad : St → Bool)
         (respB : St → Q → Dist-ℚ (St × (R × R))) where

  open Coupling bad respB

  hop-bound : {ε : ℕ → ℚ} (respR : StR → Q → Dist-ℚ (StR × R))
              (respI : StI → Q → Dist-ℚ (StI × R)) (s₀ : St) (sR : StR) (sI : StI)
            → (∀ d → Pr₁ (runWith realK s₀ d) ≡ Pr₁ (runWith respR sR d))
            → (∀ d → Pr₁ (runWith idealK s₀ d) ≡ Pr₁ (runWith respI sI d))
            → SuperCert realK bad s₀ ε
            → ∀ m d → asks≤ m d
            → ∣ Pr₁ (runWith respI sI d) -ℚ Pr₁ (runWith respR sR d) ∣ℚ ≤ℚ ε m
  hop-bound {ε} respR respI s₀ sR sI eR eI cert m d le =
    subst (_≤ℚ ε m) (cong₂ (λ x y → ∣ x -ℚ y ∣ℚ) (eI d) (eR d))
      (≤-trans (FLGP s₀ d) (badProb-bounded cert m d le))
