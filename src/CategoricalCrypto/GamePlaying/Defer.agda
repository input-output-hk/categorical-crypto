{-# OPTIONS --safe --without-K #-}

-- Deferred sampling: a secret PLANTED in the state and the same secret DRAWN
-- at the step that first reads it give the same run distribution.
--
-- What it is FOR is the caveat `docs/ro-game-hop.md` records: a secret already
-- determined by the state is one the next query hits with probability 1, so no
-- `SuperCert` can bound a flag that reads it.  Moving the draw is the only way
-- to put such a flag in reach of `Potential.rare-cert`, and this is the lemma
-- that moves it.

open import categorical-crypto.Prelude hiding (_>>=_)

open import Data.Rational

open import CategoricalCrypto.Interaction
open import CategoricalCrypto.Strategy
open import ProbabilisticLogic.Distribution.RationalDist
open import ProbabilisticLogic.Distribution.RationalDist.Expectation

module CategoricalCrypto.GamePlaying.Defer where

module _ {R V StE StL : Type} (μ : Dist-ℚ V) (_≋_ : (V → StE) → StL → Type) where

  -- The point hypothesis of an averaged bisimulation (below): a family of
  -- outcomes counts as related to one outcome when its states are and its
  -- answer does not depend on the secret.
  AvgPoint : (StE × R → ℚ) → (StL × R → ℚ) → Type
  AvgPoint F F′ = ∀ (g : V → StE × R) t → (λ v → proj₁ (g v)) ≋ proj₁ t
                → (∀ v → proj₂ (g v) ≡ proj₂ t) → E μ (λ v → F (g v)) ≡ F′ t

  -- …at a constant family: at the step that DRAWS the secret, `E-const`
  -- collapses the average that has just been created.
  avg-here : (F : StE × R → ℚ) (F′ : StL × R → ℚ) → AvgPoint F F′
           → ∀ w s → (λ _ → proj₁ w) ≋ s → F w ≡ F′ (s , proj₂ w)
  avg-here F F′ pt w s rel =
    trans (sym (E-const μ (F w))) (pt (λ _ → w) (s , proj₂ w) rel (λ _ → refl))

module _ {Q R V StE StL : Type} (μ : Dist-ℚ V)
         (resp : StE → Q → Dist-ℚ (StE × R)) (resp′ : StL → Q → Dist-ℚ (StL × R))
         (_≋_ : (V → StE) → StL → Type) where

  -- One query, averaged.  The relation compares a family of planted states
  -- with one deferring state.
  AvgBisim : Type
  AvgBisim = ∀ f s → f ≋ s → ∀ q (F : StE × R → ℚ) (F′ : StL × R → ℚ)
           → AvgPoint μ _≋_ F F′ → E μ (λ v → E (resp (f v) q) F) ≡ E (resp′ s q) F′

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
      point : AvgPoint μ _≋_ (λ t → Pr₁ (K t)) (λ t′ → Pr₁ (K′ t′))
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
