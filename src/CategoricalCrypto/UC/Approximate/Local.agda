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
-- The laws are the error algebra's read at `Negligible`: zero error is
-- reflexivity, symmetry is symmetry, and `Negligible-+` is transitivity.  So
-- this is an `IsEquivalence` and hence a `UC.Core.Observation`'s comparison at
-- no further cost — `Observation` asks for an arbitrary equivalence and this is
-- one (`UC/Core.agda:80-93`).
--
-- Stated over `ℚ-errors` rather than an arbitrary `ErrorAlgebra`, because
-- `Negligible` is a decay class of `ℕ → ℚ`; the index is read through `κ`
-- alone, as in `UC.Family`.

open import Data.Nat.Base using (ℕ)
open import Data.Product.Base using (Σ; Σ-syntax; _×_; _,_)
open import Data.Rational as ℚ using (ℚ; 0ℚ)
open import Level using (Level)
open import Relation.Binary.PropositionalEquality using (_≡_; subst)
open import Relation.Binary.Structures using (IsEquivalence)

open import CategoricalCrypto.UC.Approximate
  using (Approximation; Negligible; Negligible-+; Negligible-0; ℚ-errors)

module CategoricalCrypto.UC.Approximate.Local
  {os ℓa : Level} {Obs : Set os} (apx : Approximation Obs ℚ-errors ℓa)
  (Ix : Set) (κ : Ix → ℕ) where

open Approximation apx

infix 4 _∼ᴺ_

_∼ᴺ_ : (Ix → Obs) → (Ix → Obs) → Set ℓa
μ ∼ᴺ ν = Σ[ δ ∈ (ℕ → ℚ) ] Negligible δ × ((i : Ix) → μ i ≈[ δ (κ i) ] ν i)

∼ᴺ-isEquivalence : IsEquivalence _∼ᴺ_
∼ᴺ-isEquivalence = record
  { refl  = (λ _ → 0ℚ) , Negligible-0 , λ _ → ≈[]-refl
  ; sym   = λ (δ , neg , h) → δ , neg , λ i → ≈[]-sym (h i)
  ; trans = λ (δ , nδ , h) (γ , nγ , k) →
      (λ n → δ n ℚ.+ γ n) , Negligible-+ nδ nγ , λ i → ≈[]-trans (h i) (k i)
  }

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
