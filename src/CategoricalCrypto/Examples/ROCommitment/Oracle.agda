{-# OPTIONS --safe --without-K #-}

-- The lazily sampled oracle both closed `F_com` games run on.
--
-- The games keep the table inside different states, so `fetchT` takes the
-- embedding `g` of the post-table into the caller's state (`fetchT id` in
-- `Hiding.Game`, `fetchT (_, m)` in `Game`).  Taking `g` rather than mapping
-- the result afterwards keeps the kernel reducing under the games' `E-bind`
-- rewrites; a `Dmap` in front would not.

open import Data.List.Base
open import Data.Maybe.Base
open import Data.Nat.Base
open import Data.Product.Base
open import Data.Rational
open import Data.Sum.Base
open import Data.Unit.Base
open import Function.Base
open import Relation.Binary.PropositionalEquality

open import ProbabilisticLogic.Distribution.RationalDist
open import ProbabilisticLogic.Distribution.RationalDist.Expectation
open import ProbabilisticLogic.Distribution.Uniform

module CategoricalCrypto.Examples.ROCommitment.Oracle (k : ℕ) where

open import CategoricalCrypto.Examples.ROCommitment.Extraction k

fetchT : {A : Set} → (Tbl → A) → Tbl → Pt → Dist-ℚ (A × Dig)
fetchT g t x = case lookupPt t x of λ where
  (just d) → return-ℚ (g t , d)
  nothing → uniform-Vec k >>=ᴹ λ h → return-ℚ (g ((x , h) ∷ t) , h)

fetchT-hit : {A : Set} (g : Tbl → A) (t : Tbl) (x : Pt) (d : Dig)
           → lookupPt t x ≡ just d → fetchT g t x ≡ return-ℚ (g t , d)
fetchT-hit g t x d eq rewrite eq = refl

fetchT-miss : {A : Set} (g : Tbl → A) (t : Tbl) (x : Pt) → lookupPt t x ≡ nothing
            → fetchT g t x ≡ (uniform-Vec k >>=ᴹ λ h → return-ℚ (g ((x , h) ∷ t) , h))
fetchT-miss g t x eq rewrite eq = refl

fetchT-cong : {A A′ : Set} (g : Tbl → A) (g′ : Tbl → A′) (t : Tbl) (x : Pt)
              (H : A × Dig → ℚ) (H′ : A′ × Dig → ℚ)
            → ((u : Tbl) (d : Dig) → H (g u , d) ≡ H′ (g′ u , d))
            → E (fetchT g t x) H ≡ E (fetchT g′ t x) H′
fetchT-cong g g′ t x H H′ pt with lookupPt t x
... | just d  = trans (lookupᴰℚ-return (g t , d) H)
                      (trans (pt t d) (sym (lookupᴰℚ-return (g′ t , d) H′)))
... | nothing = trans (lookupᴰℚ-Dmap (λ h → g ((x , h) ∷ t) , h) (uniform-Vec k) H)
                (trans (lookupᴰℚ-cong-P (entries (uniform-Vec k)) λ h → pt ((x , h) ∷ t) h)
                       (sym (lookupᴰℚ-Dmap (λ h → g′ ((x , h) ∷ t) , h) (uniform-Vec k) H′)))

fetchT-sup : (t : Tbl) (x : Pt)
           → OnSupport (λ u → (proj₁ u ≡ t × lookupPt t x ≡ just (proj₂ u))
                            ⊎ (proj₁ u ≡ (x , proj₂ u) ∷ t × lookupPt t x ≡ nothing))
                       (fetchT id t x)
fetchT-sup t x with lookupPt t x
... | just d  = OnSupport-return (inj₁ (refl , refl))
... | nothing = OnSupport-map (uniform-Vec k) _
                  (λ h → inj₂ (refl , refl))

-- The fetch with the fresh sample supplied, so that a coupling can feed it
-- another game's draw; read against `fetchT` at a table that misses no more
-- often (`fetchT-transfer`).
fetchR : Tbl → Pt → Dig → Tbl × Dig
fetchR t′ x h = case lookupPt t′ x of λ where
  (just d) → t′ , d
  nothing → (x , h) ∷ t′ , h

fetchR-hit : (t′ : Tbl) (x : Pt) (d h : Dig) → lookupPt t′ x ≡ just d
           → fetchR t′ x h ≡ (t′ , d)
fetchR-hit t′ x d h eq rewrite eq = refl

fetchR-miss : (t′ : Tbl) (x : Pt) (h : Dig) → lookupPt t′ x ≡ nothing
            → fetchR t′ x h ≡ ((x , h) ∷ t′ , h)
fetchR-miss t′ x h eq rewrite eq = refl

fetchT-transfer : (t t′ : Tbl) (x : Pt) → (lookupPt t′ x ≡ nothing → lookupPt t x ≡ nothing)
                → (G : Tbl × Dig → ℚ)
                → E (fetchT id t x) (λ u → G (fetchR t′ x (proj₂ u))) ≡ E (fetchT id t′ x) G
fetchT-transfer t t′ x miss G = aux (lookupPt t′ x) refl
  where
  aux : (o : Maybe Dig) → lookupPt t′ x ≡ o
      → E (fetchT id t x) (λ u → G (fetchR t′ x (proj₂ u))) ≡ E (fetchT id t′ x) G
  aux (just d) eq′ =
    trans (trans (lookupᴰℚ-cong-P (entries (fetchT id t x))
                   (λ u → cong G (fetchR-hit t′ x d (proj₂ u) eq′)))
                 (E-const (fetchT id t x) (G (t′ , d))))
          (sym (trans (cong (λ ν → E ν G) (fetchT-hit id t′ x d eq′))
                      (lookupᴰℚ-return (t′ , d) G)))
  aux nothing eq′ =
    trans (trans (cong (λ ν → E ν (λ u → G (fetchR t′ x (proj₂ u))))
                       (fetchT-miss id t x (miss eq′)))
          (trans (lookupᴰℚ-Dmap (λ h → (x , h) ∷ t , h) (uniform-Vec k)
                   (λ u → G (fetchR t′ x (proj₂ u))))
                 (lookupᴰℚ-cong-P (entries (uniform-Vec k))
                   (λ h → cong G (fetchR-miss t′ x h eq′)))))
          (sym (trans (cong (λ ν → E ν G) (fetchT-miss id t′ x eq′))
                      (lookupᴰℚ-Dmap (λ h → (x , h) ∷ t′ , h) (uniform-Vec k) G)))
