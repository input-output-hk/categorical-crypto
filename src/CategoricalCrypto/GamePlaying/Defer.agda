{-# OPTIONS --safe --without-K #-}

-- Deferred sampling: a secret PLANTED in the state and the same secret DRAWN
-- at the step that first reads it give the same run distribution.
--
-- `runWith-avg` is `Hop.runWith-bisim` with an average in front of one side.
-- The planted kernel is run at a FAMILY of states indexed by the secret, the
-- deferring kernel at a single state, and the two agree at every adaptive
-- distinguisher once they agree at one query.  At a point-mass `μ` and a
-- constant family it IS `runWith-bisim`, so the induction
-- `Examples.MerkleDamgard.Core.ideal-marginal` runs is its `V ≡ ⊤` case.
--
-- What it is FOR is the caveat `docs/ro-game-hop.md` records: a secret already
-- determined by the state is one the next query hits with probability 1, so no
-- `SuperCert` can bound a flag that reads it.  Moving the draw is the only way
-- to put such a flag in reach of `Potential.rare-cert`, and this is the lemma
-- that moves it.  Two `Dist-ℚ`s never share a sample, which is why the `coin`
-- case is `Expectation.E-swap` and nothing else.

open import categorical-crypto.Prelude hiding (_>>=_)

open import Data.Rational using (ℚ)

open import CategoricalCrypto.Interaction
open import CategoricalCrypto.Strategy
open import ProbabilisticLogic.Distribution.RationalDist
open import ProbabilisticLogic.Distribution.RationalDist.Expectation

module CategoricalCrypto.GamePlaying.Defer where

module _ {Q R V StE StL : Type} (μ : Dist-ℚ V)
         (resp : StE → Q → Dist-ℚ (StE × R)) (resp′ : StL → Q → Dist-ℚ (StL × R))
         (_≋_ : (V → StE) → StL → Type) where

  -- One query, averaged.  The relation compares a family of planted states
  -- with one deferring state; a family of outcomes counts as related when its
  -- states are and its answer does not depend on the secret.  At the step that
  -- DRAWS the secret the consumer discharges this with a constant family, which
  -- is where `E-const` collapses the average that has just been created.
  AvgBisim : Type
  AvgBisim = ∀ f s → f ≋ s → ∀ q (F : StE × R → ℚ) (F′ : StL × R → ℚ)
           → (∀ (g : V → StE × R) t → (λ v → proj₁ (g v)) ≋ proj₁ t
              → (∀ v → proj₂ (g v) ≡ proj₂ t) → E μ (λ v → F (g v)) ≡ F′ t)
           → E μ (λ v → E (resp (f v) q) F) ≡ E (resp′ s q) F′

  runWith-avg : AvgBisim → ∀ d f s → f ≋ s
              → E μ (λ v → Pr₁ (runWith resp (f v) d)) ≡ Pr₁ (runWith resp′ s d)
  runWith-avg bis (out b) f s rel = E-const μ (Pr₁ (return-ℚ b))
  runWith-avg bis (ask q k) f s rel =
    trans (lookupᴰℚ-cong-P (entries μ) (λ v → Pr₁-bind (resp (f v) q) K))
   (trans (bis f s rel q (λ t → Pr₁ (K t)) (λ t′ → Pr₁ (K′ t′)) point)
          (sym (Pr₁-bind (resp′ s q) K′)))
    where
      K  = λ (t : StE × R) → runWith resp (proj₁ t) (k (proj₂ t))
      K′ = λ (t′ : StL × R) → runWith resp′ (proj₁ t′) (k (proj₂ t′))
      point : ∀ g t → (λ v → proj₁ (g v)) ≋ proj₁ t → (∀ v → proj₂ (g v) ≡ proj₂ t)
            → E μ (λ v → Pr₁ (K (g v))) ≡ Pr₁ (K′ t)
      point g t r eq =
        trans (lookupᴰℚ-cong-P (entries μ)
                (λ v → cong (λ z → Pr₁ (runWith resp (proj₁ (g v)) (k z))) (eq v)))
              (runWith-avg bis (k (proj₂ t)) (λ v → proj₁ (g v)) (proj₁ t) r)
  runWith-avg bis (coin ν k) f s rel =
    trans (lookupᴰℚ-cong-P (entries μ)
            (λ v → Pr₁-bind ν (λ b → runWith resp (f v) (k b))))
   (trans (E-swap μ ν (λ v b → Pr₁ (runWith resp (f v) (k b))))
   (trans (lookupᴰℚ-cong-P (entries ν) (λ b → runWith-avg bis (k b) f s rel))
          (sym (Pr₁-bind ν (λ b → runWith resp′ s (k b))))))
