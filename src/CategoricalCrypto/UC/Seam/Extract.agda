{-# OPTIONS --safe --without-K --guardedness #-}

-- A budgeted context, read off its certificate as a strategy.
--
-- A `Strat` is a finite tree and a `Dₚ` context's coin tree is not, so no
-- single strategy simulates a context: the extraction is FUEL-indexed, and
-- past the fuel it answers `out (not b)`, the verdict that scores 0 under
-- `indᵇ b` (what that buys each direction: `UC.Seam.Transfer`).
--
-- It reads the certificate's REFINED emissions rather than the step itself,
-- and that is what makes the ask bound free: a downward output lands in
-- `Below Φ r`, so the potential strictly drops at every `ask`, and `asks≤ r`
-- is then the same induction as the extraction.

open import Data.Bool.Base
open import Data.List.Base
open import Data.Nat.Base as ℕ
open import Data.Product.Base
open import Data.Rational as ℚ
open import Data.Rational.Properties
open import Data.Sum.Base
open import Data.Unit.Base
open import Level
open import Relation.Binary.PropositionalEquality

import Data.List.NonEmpty as NE
import Data.List.Relation.Unary.All as All

open import ProbabilisticLogic.Distribution.RationalDist
open import ProbabilisticLogic.Distribution.RationalDist.Expectation
open import ProbabilisticLogic.Dp

open import CategoricalCrypto.Iface
open import CategoricalCrypto.Strategy
open import CategoricalCrypto.UC.Machine
open import CategoricalCrypto.UC.QueryBound

module CategoricalCrypto.UC.Seam.Extract
  (B : Iface) (K : Proc B Ωᴵ) (q : ℕ) (cert : Certified q K) where

open QBᵢ cert public

Ansᶜ : ℕ → Set
Ansᶜ r = Ans Φ (Neg B) Bool r

------------------------------------------------------------------------
-- A node's two weights, as a distribution

coinᵈ : {A : Set} → Dₚ A → Dist-ℚ Bool
coinᵈ X = mk-Dist ((wt X true , true) NE.∷ ((wt X false , false) ∷ []))
                  (trans (cong (wt X true ℚ.+_) (+-identityʳ (wt X false))) (wt-1 X))
                  (wt-nn X true All.∷ wt-nn X false All.∷ All.[])

E-coinᵈ : {A : Set} (X : Dₚ A) (F : Bool → ℚ)
        → E (coinᵈ X) F ≡ wt X true ℚ.* F true ℚ.+ wt X false ℚ.* F false
E-coinᵈ X F = cong (wt X true ℚ.* F true ℚ.+_) (+-identityʳ (wt X false ℚ.* F false))

------------------------------------------------------------------------
-- The extraction

-- `b` is the verdict the truncation must not score; `f` the fuel, `r` the
-- potential the emission tree is refined against.
mutual
  extract : Bool → ℕ → (r : ℕ) → Dₚ (Ansᶜ r) → Strat (Neg B) (Pos B)
  extract b zero    r X = out (not b)
  extract b (suc f) r X = coin (coinᵈ X) λ c → extractL b f r (br X c)

  extractL : Bool → ℕ → (r : ℕ) → Ansᶜ r ⊎ Dₚ (Ansᶜ r) → Strat (Neg B) (Pos B)
  extractL b f r (inj₁ (inj₁ ((s , _) , n))) = ask n λ p → extract b f (Φ s) (onLᵍ s p)
  extractL b f r (inj₁ (inj₂ (_ , v)))       = out v
  extractL b f r (inj₂ X′)                   = extract b f r X′

------------------------------------------------------------------------
-- …and the ask bound it comes with

mutual
  extract-asks : (b : Bool) (f r : ℕ) (X : Dₚ (Ansᶜ r)) → asks≤ r (extract b f r X)
  extract-asks b zero    r X = tt
  extract-asks b (suc f) r X = λ c → extractL-asks b f r (br X c)

  extractL-asks : (b : Bool) (f r : ℕ) (y : Ansᶜ r ⊎ Dₚ (Ansᶜ r))
                → asks≤ r (extractL b f r y)
  extractL-asks b f (suc r) (inj₁ (inj₁ ((s , s≤s lt) , n))) =
    λ p → asks≤-mono lt _ (extract-asks b f (Φ s) (onLᵍ s p))
  extractL-asks b f r (inj₁ (inj₂ _)) = tt
  extractL-asks b f r (inj₂ X′)       = extract-asks b f r X′
