{-# OPTIONS --safe --without-K --guardedness #-}

-- A budgeted context, read off its certificate as a strategy.
--
-- A `Strat` is a finite tree and a `Dₚ` context's coin tree is not, so no
-- single strategy simulates a context: the extraction is FUEL-indexed, and
-- past the fuel it answers `out (not b)` — the verdict that scores 0 under
-- `indᵇ b`, which is what makes the truncation invisible from BOTH sides at
-- that one test (`UC.Seam.Transfer`).
--
-- It reads the certificate's REFINED emissions rather than the step itself,
-- and that is what makes the ask bound free: a downward output lands in
-- `Below Φ r`, so the potential strictly drops at every `ask`, and `asks≤ r`
-- is then the same induction as the extraction.  The step is recovered from
-- the refinement by `cohL`/`cohR`, which is where the two agree.
--
-- Each node of the emission tree becomes a `coin` on that node's own two
-- weights, which is exactly what `Dₚ`'s record carries: `coinᵈ`'s
-- non-negativity and mass-one are the node's `wt-nn` and `wt-1`.

open import Data.Bool.Base using (Bool; true; false; not)
open import Data.List.Base using ([]; _∷_)
open import Data.Nat.Base as ℕ using (ℕ; zero; suc; s≤s)
open import Data.Product.Base using (_,_; proj₁)
open import Data.Rational as ℚ using (ℚ; 0ℚ; 1ℚ)
open import Data.Rational.Properties using (+-identityʳ)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Unit.Base using (tt)
open import Level using (0ℓ)
open import Relation.Binary.PropositionalEquality using (_≡_; cong; trans)

import Data.List.NonEmpty as NE
import Data.List.Relation.Unary.All as All

open import ProbabilisticLogic.Distribution.RationalDist using (Dist-ℚ; mk-Dist; entries)
open import ProbabilisticLogic.Distribution.RationalDist.Expectation using (E)
open import ProbabilisticLogic.Dp

open import CategoricalCrypto.Iface
open import CategoricalCrypto.Strategy
open import CategoricalCrypto.UC.Machine using (Proc; Ωᴵ)
open import CategoricalCrypto.UC.QueryBound using (QBᵢ; Certified; Ans)

module CategoricalCrypto.UC.Seam.Extract
  (B : Iface) (K : Proc B Ωᴵ) (q : ℕ) (cert : Certified q K) where

open QBᵢ cert public

-- The certificate's refined emission: a query below, with the potential
-- strictly dropped, or a verdict above.
Ansᶜ : ℕ → Set
Ansᶜ r = Ans Φ (Neg B) Bool r

------------------------------------------------------------------------
-- A node's two weights, as a distribution

coinᵈ : {A : Set} → Dₚ A → Dist-ℚ Bool
coinᵈ X = mk-Dist ((wt X true , true) NE.∷ ((wt X false , false) ∷ []))
                  (trans (cong (wt X true ℚ.+_) (+-identityʳ (wt X false))) (wt-1 X))
                  (wt-nn X true All.∷ wt-nn X false All.∷ All.[])

-- `E` of a two-entry distribution is the node's own average.
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
