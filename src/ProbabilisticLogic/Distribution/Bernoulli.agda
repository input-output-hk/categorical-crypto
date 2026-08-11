{-# OPTIONS --safe --without-K #-}

open import categorical-crypto.Prelude as P hiding (pure; _>>=_; _⊎_; _*_; _/_; isEquivalence; trans)

open import Algebra
open import Relation.Binary using (Setoid)
open import Relation.Unary using (U; _≐_)
import Relation.Binary.Reasoning.Setoid as ≈-Reasoning

open import Data.List.Properties using (length-++; length-replicate; ++-identityʳ)
import Data.List.NonEmpty as NE
open import Data.List.Relation.Unary.Any using (here; there)
import Data.List.Relation.Unary.All as All
open import Data.List.Relation.Unary.AllPairs using ([]; _∷_)
open import Data.List.Relation.Unary.Unique.Propositional using (Unique)
open import Data.Rational as ℚ using (ℚ; _/_)
open import Data.Rational.Properties using (/-cong)
open import Data.Integer using (+_)

open import ProbabilisticLogic.Abstract
open import ProbabilisticLogic.Reasoning

module ProbabilisticLogic.Distribution.Bernoulli c ℓ (a : Abstract c ℓ) where

open Abstract a
open import ProbabilisticLogic.Logic c ℓ a
open import ProbabilisticLogic.Expectation c ℓ a

-- The Bernoulli distribution Bernoulli(m / (m + n)) on `Bool`, with
-- probability of `true` equal to m / (m + n).  Built directly via the
-- generic `weighted-K` helper.

private
  outcomes : (m n : ℕ) ⦃ _ : NonZero (m +ℕ n) ⦄ → NE.List⁺ Bool
  outcomes (suc m) n       = weighted-K ((suc m , true) NE.∷ (n , false) ∷ [])
  outcomes zero    (suc n) = weighted-K ((suc n , false) NE.∷ [])

  outcomes-toList : ∀ m n ⦃ _ : NonZero (m +ℕ n) ⦄
                  → NE.toList (outcomes m n) ≡ replicate m true ++ replicate n false
  outcomes-toList (suc m) n =
    cong (true ∷_) (cong (replicate m true ++_) (++-identityʳ (replicate n false)))
  outcomes-toList zero    (suc n) =
    cong (false ∷_) (++-identityʳ (replicate n false))

  filterᵇ-falses : ∀ n → filterᵇ id (replicate n false) ≡ []
  filterᵇ-falses zero    = P.refl
  filterᵇ-falses (suc n) = filterᵇ-falses n

  filterᵇ-trues-length : ∀ m n
                       → length (filterᵇ id (replicate m true ++ replicate n false)) ≡ m
  filterᵇ-trues-length zero    n = cong length (filterᵇ-falses n)
  filterᵇ-trues-length (suc m) n = cong suc (filterᵇ-trues-length m n)

  filterᵇ-not-falses-length : ∀ n → length (filterᵇ not (replicate n false)) ≡ n
  filterᵇ-not-falses-length zero    = P.refl
  filterᵇ-not-falses-length (suc n) = cong suc (filterᵇ-not-falses-length n)

  filterᵇ-not-trues-falses-length : ∀ m n
                                  → length (filterᵇ not (replicate m true ++ replicate n false)) ≡ n
  filterᵇ-not-trues-falses-length zero    n = filterᵇ-not-falses-length n
  filterᵇ-not-trues-falses-length (suc m) n = filterᵇ-not-trues-falses-length m n

  canonical-length : ∀ m n → length (replicate m true ++ replicate n false) ≡ m +ℕ n
  canonical-length m n =
    P.trans (length-++ (replicate m true))
            (cong₂ _+ℕ_ (length-replicate m) (length-replicate n))

  outcomes-trues-length : ∀ m n ⦃ _ : NonZero (m +ℕ n) ⦄
                        → length (filterᵇ id (NE.toList (outcomes m n))) ≡ m
  outcomes-trues-length m n =
    P.trans (cong (length P.∘ filterᵇ id) (outcomes-toList m n))
            (filterᵇ-trues-length m n)

  outcomes-falses-length : ∀ m n ⦃ _ : NonZero (m +ℕ n) ⦄
                         → length (filterᵇ not (NE.toList (outcomes m n))) ≡ n
  outcomes-falses-length m n =
    P.trans (cong (length P.∘ filterᵇ not) (outcomes-toList m n))
            (filterᵇ-not-trues-falses-length m n)

  outcomes-length : ∀ m n ⦃ _ : NonZero (m +ℕ n) ⦄
                  → NE.length (outcomes m n) ≡ m +ℕ n
  outcomes-length m n =
    P.trans (cong length (outcomes-toList m n)) (canonical-length m n)

bernoulli : (m n : ℕ) ⦃ _ : NonZero (m +ℕ n) ⦄ → ProbDistr Bool
bernoulli m n = empirical (outcomes m n)

P-bernoulli-true : ∀ m n ⦃ _ : NonZero (m +ℕ n) ⦄ → bernoulli m n ∙ (↑ id) ≈ fromℚ (+ m / (m +ℕ n))
P-bernoulli-true m n = begin
  bernoulli m n ∙ (↑ id)
    ≈⟨ empirical-eq ⟩
  fromℚ (+ length (filterᵇ id (NE.toList (outcomes m n))) / NE.length (outcomes m n))
    ≡⟨ cong fromℚ (/-cong (cong +_ (outcomes-trues-length m n)) (outcomes-length m n)) ⟩
  fromℚ (+ m / (m +ℕ n)) ∎
  where open ≈-Reasoning setoid

P-bernoulli-false : ∀ m n ⦃ _ : NonZero (m +ℕ n) ⦄ → bernoulli m n ∙ (↑ not) ≈ fromℚ (+ n / (m +ℕ n))
P-bernoulli-false m n = begin
  bernoulli m n ∙ (↑ not)
    ≈⟨ empirical-eq ⟩
  fromℚ (+ length (filterᵇ not (NE.toList (outcomes m n))) / NE.length (outcomes m n))
    ≡⟨ cong fromℚ (/-cong (cong +_ (outcomes-falses-length m n)) (outcomes-length m n)) ⟩
  fromℚ (+ n / (m +ℕ n)) ∎
  where open ≈-Reasoning setoid

------------------------------------------------------------------------
-- Expected value of a Bernoulli random variable.

-- Distinctness / U-coverage for the canonical Bool support [true, false].
bool-distinct : Unique (true ∷ false ∷ [])
bool-distinct = ((λ ()) All.∷ All.[]) ∷ (All.[] ∷ [])

bool-cover : (_∈ˡ (true ∷ false ∷ [])) ≐ U
proj₁ bool-cover _ = tt
proj₂ bool-cover {true}  _ = here P.refl
proj₂ bool-cover {false} _ = there (here P.refl)

bernoulli-full : ∀ m n ⦃ _ : NonZero (m +ℕ n) ⦄
               → bernoulli m n ∙ (_∈ˡ (true ∷ false ∷ [])) ≈ 1#
bernoulli-full m n = Eq.trans (∙-cong bool-cover) PU≈1
  where module Eq = Setoid setoid

E-bernoulli-true : ∀ m n ⦃ _ : NonZero (m +ℕ n) ⦄
                 → E[ bernoulli m n , 1[ ↑ id ] ]≈ fromℚ (+ m / (m +ℕ n))
E-bernoulli-true m n =
  E-resp-≈ (P-bernoulli-true m n)
    (E-indicator (true ∷ false ∷ []) bool-distinct (bernoulli-full m n) (↑ id))

E-bernoulli-false : ∀ m n ⦃ _ : NonZero (m +ℕ n) ⦄
                  → E[ bernoulli m n , 1[ ↑ not ] ]≈ fromℚ (+ n / (m +ℕ n))
E-bernoulli-false m n =
  E-resp-≈ (P-bernoulli-false m n)
    (E-indicator (true ∷ false ∷ []) bool-distinct (bernoulli-full m n) (↑ not))
