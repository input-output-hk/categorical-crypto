{-# OPTIONS --safe --without-K #-}

-- The LOCAL negligible agreement of an index-family of observations:
--
--     μ ∼ᴺ ν  =  ∃ negligible δ. ∀ i. μ i is δ(κ i)-close to ν i
--
-- The existential is INSIDE nothing: one δ serves every index, but δ is chosen
-- per PAIR, which is what makes this the local relation of
-- `docs/graded-observation-redesign.md` — a consumer that quantifies contexts
-- outside it (`UC.Family.Negligible`'s `_≈ℰᴺ_`) gets a witness per context and
-- no uniform one.  Keeping the witness is the whole difference from
-- `UC.Approximate.Induced`, which quantifies its ambient error away.
--
-- It is an instance, not a construction of its own: `familySpace` is the
-- approximate space of observation families over rational-sequence errors, and
-- `_∼ᴺ_` is `Approx.Small`'s existential collapse of it at the negligible
-- class — `∼ᴺ≡∼Small` pins that, and the equivalence comes from there rather
-- than being proved again.  What a collapse class must be is exactly what
-- `Negligible` is: it contains zero and is closed under sums.
--
-- Stated over `ℚ-errors` rather than an arbitrary `ErrorAlgebra`, because
-- `Negligible` is a decay class of `ℕ → ℚ`; the index is read through `κ`
-- alone, as in `UC.Family`.

open import Data.Nat.Base using (ℕ)
open import Data.Product.Base using (Σ-syntax; _×_; _,_)
open import Data.Rational as ℚ using (ℚ)
open import Level using (Level; 0ℓ)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)
open import Relation.Binary.Structures using (IsEquivalence)

open import CategoricalCrypto.Approx.Error using (ℚ-ordered)
open import CategoricalCrypto.Approx.Schedule using (pointwise)
open import CategoricalCrypto.UC.Approximate
  using (Approximation; Negligible; Negligible-+; Negligible-0; ℚ-errors)

import CategoricalCrypto.Approx.Small as Smallᴹ
import CategoricalCrypto.Approx.Space as Spaceᴹ

module CategoricalCrypto.UC.Approximate.Local
  {os ℓa : Level} {Obs : Set os} (apx : Approximation Obs ℚ-errors ℓa)
  (Ix : Set) (κ : Ix → ℕ) where

open Approximation apx

private
  Sched = pointwise ℕ ℚ-ordered
  module Sp = Spaceᴹ Sched
  module Sm = Smallᴹ Sched

infix 4 _∼ᴺ_

_∼ᴺ_ : (Ix → Obs) → (Ix → Obs) → Set ℓa
μ ∼ᴺ ν = Σ[ δ ∈ (ℕ → ℚ) ] Negligible δ × ((i : Ix) → μ i ≈[ δ (κ i) ] ν i)

familySpace : Sp.ApproxSpace os ℓa
familySpace = record
  { Carrier = Ix → Obs
  ; approx = record
      { _≈[_]_    = λ μ δ ν → (i : Ix) → μ i ≈[ δ (κ i) ] ν i
      ; ≈[]-refl  = λ _ → ≈[]-refl
      ; ≈[]-sym   = λ h i → ≈[]-sym (h i)
      ; ≈[]-trans = λ h k i → ≈[]-trans (h i) (k i)
      ; ≈[]-mono  = λ le h i → ≈[]-mono (le (κ i)) (h i)
      }
  }

negligible : Sm.SmallClass 0ℓ
negligible = record
  { Small = Negligible ; small-ε₀ = Negligible-0 ; small-⊕ = Negligible-+ }

open Sm.Collapse negligible os ℓa using (_∼Small_; ∼Small-isEquivalence)

∼ᴺ≡∼Small : {μ ν : Ix → Obs} → (μ ∼ᴺ ν) ≡ _∼Small_ familySpace μ ν
∼ᴺ≡∼Small = refl

∼ᴺ-isEquivalence : IsEquivalence _∼ᴺ_
∼ᴺ-isEquivalence = ∼Small-isEquivalence familySpace

-- What the relation gives BACK, at an approximation that hides no gap
-- (`UC.Approximate.Separating`): the witness dominates the actual difference,
-- so a difference `Negligible` excludes is not admitted.  `κ` must be onto —
-- a bound at every index says nothing at a security parameter no index reaches.
--
-- The two families and the difference are EXPLICIT: each sits under an
-- application in the separation hypothesis, which is no pattern.
∼ᴺ-gap : (μ ν : Ix → Obs) (s : ℕ → ℚ) → ((n : ℕ) → Σ[ i ∈ Ix ] κ i ≡ n)
       → ({i : Ix} {ε : ℚ} → μ i ≈[ ε ] ν i → s (κ i) ℚ.≤ ε)
       → μ ∼ᴺ ν → Σ[ δ ∈ (ℕ → ℚ) ] Negligible δ × ((n : ℕ) → s n ℚ.≤ δ n)
∼ᴺ-gap μ ν s onto sep (δ , neg , h) = δ , neg , λ n →
  let i , eq = onto n in subst (λ m → s m ℚ.≤ δ m) eq (sep (h i))
