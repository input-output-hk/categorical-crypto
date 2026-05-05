{-# OPTIONS --safe --without-K #-}

open import categorical-crypto.Prelude as P hiding (pure; _>>=_; _⊎_; _*_; _/_; isEquivalence; trans)

open import Algebra
import Relation.Binary.Reasoning.Setoid as ≈-Reasoning

open import Data.List.Properties using (length-++; length-replicate)
import Data.List.NonEmpty as NE
open import Data.Rational as ℚ using (ℚ; _/_)
open import Data.Rational.Properties using (/-cong)
open import Data.Integer using (+_)

open import ProbabilisticLogic.Abstract
open import ProbabilisticLogic.Reasoning

module ProbabilisticLogic.Distribution.Bernoulli c ℓ (a : Abstract c ℓ) where

open Abstract a
open import ProbabilisticLogic.Logic c ℓ a

-- The Bernoulli distribution Bernoulli(m / (m + n)) on `Bool`, with
-- probability of `true` equal to m / (m + n). It is realised as the
-- empirical distribution over m trues followed by n falses; the
-- instance constraint `NonZero (m + n)` keeps the underlying list nonempty.

private
  outcomes : (m n : ℕ) ⦃ _ : NonZero (m +ℕ n) ⦄ → NE.List⁺ Bool
  outcomes (suc m) n       = true  NE.∷ replicate m true ++ replicate n false
  outcomes zero    (suc n) = false NE.∷ replicate n false

  filterᵇ-falses : ∀ n → filterᵇ id (replicate n false) ≡ []
  filterᵇ-falses zero    = P.refl
  filterᵇ-falses (suc n) = filterᵇ-falses n

  filterᵇ-trues-length : ∀ m n
                       → length (filterᵇ id (replicate m true ++ replicate n false)) ≡ m
  filterᵇ-trues-length zero    n = cong length (filterᵇ-falses n)
  filterᵇ-trues-length (suc m) n = cong suc (filterᵇ-trues-length m n)

  outcomes-trues-length : ∀ m n ⦃ _ : NonZero (m +ℕ n) ⦄
                        → length (filterᵇ id (NE.toList (outcomes m n))) ≡ m
  outcomes-trues-length (suc m) n       = cong suc (filterᵇ-trues-length m n)
  outcomes-trues-length zero    (suc n) = cong length (filterᵇ-falses (suc n))

  outcomes-length : ∀ m n ⦃ _ : NonZero (m +ℕ n) ⦄
                  → NE.length (outcomes m n) ≡ m +ℕ n
  outcomes-length (suc m) n = cong suc $ begin
    length (replicate m true ++ replicate n false)
      ≡⟨ length-++ (replicate m true) ⟩
    length (replicate m true) +ℕ length (replicate n false)
      ≡⟨ cong₂ _+ℕ_ (length-replicate m) (length-replicate n) ⟩
    m +ℕ n ∎
    where open ≡-Reasoning
  outcomes-length zero    (suc n) = cong suc (length-replicate n)

  filterᵇ-not-falses-length : ∀ n → length (filterᵇ not (replicate n false)) ≡ n
  filterᵇ-not-falses-length zero    = P.refl
  filterᵇ-not-falses-length (suc n) = cong suc (filterᵇ-not-falses-length n)

  filterᵇ-not-trues-falses-length : ∀ m n
                                  → length (filterᵇ not (replicate m true ++ replicate n false)) ≡ n
  filterᵇ-not-trues-falses-length zero    n = filterᵇ-not-falses-length n
  filterᵇ-not-trues-falses-length (suc m) n = filterᵇ-not-trues-falses-length m n

  outcomes-falses-length : ∀ m n ⦃ _ : NonZero (m +ℕ n) ⦄
                         → length (filterᵇ not (NE.toList (outcomes m n))) ≡ n
  outcomes-falses-length (suc m) n       = filterᵇ-not-trues-falses-length m n
  outcomes-falses-length zero    (suc n) = filterᵇ-not-falses-length (suc n)

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
