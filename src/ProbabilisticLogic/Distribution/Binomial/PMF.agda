{-# OPTIONS --safe --without-K #-}

-- The full binomial probability mass function (PMF):
-- P(exactly i successes in k trials) = (k C i) · m^i · n^(k − i) / (m + n)^k.
--
-- A Bernoulli step on the head bit splits `exactly (suc j)` into a disjoint
-- union of two rectangles; what makes the two rectangles' closed forms add
-- back up is Pascal's recursion,
-- `Data.Nat.Combinatorics.nCk+nC[k+1]≡[n+1]C[k+1]`.

open import categorical-crypto.Prelude as P hiding (pure; _>>=_; _⊎_; _*_; _/_; _⊗_; isEquivalence; trans)

open import Relation.Binary using (Setoid)
import Relation.Binary.Reasoning.Setoid as ≈-Reasoning
open import Relation.Unary using (_⊆_; _≐_; _∪_; ∅; U)

open import Data.Integer as ℤ using (+_)
import Data.Integer.Properties as ℤₚ
import Data.Nat as ℕ
open import Data.Nat using (_∸_; _^_)
open import Data.Nat.Combinatorics using (_C_; k>n⇒nCk≡0; nCk+nC[k+1]≡[n+1]C[k+1])
import Data.Nat.Properties as ℕₚ
open import Data.Nat.Properties.Ext using (m∸n≡suc[m∸suc[n]])
open import Data.Nat.Tactic.RingSolver using (solve-∀)
open import Data.Rational as ℚ using (ℚ; _/_)
open import Data.Rational.Properties using (/-cong)
open import Data.Rational.Properties.Ext using (/-*-/; /-+-/-same)

open import ProbabilisticLogic.Abstract
open import ProbabilisticLogic.Reasoning

open import LibExt using (_⊠_)

open ℕₚ using (_≤?_; m^n≢0; suc-injective; ≰⇒>)

module ProbabilisticLogic.Distribution.Binomial.PMF c ℓ (a : Abstract c ℓ) where

open Abstract a
open import ProbabilisticLogic.Distribution.Bernoulli c ℓ a
open import ProbabilisticLogic.Distribution.Binomial c ℓ a

private module Eq = Setoid setoid

------------------------------------------------------------------------
-- Closed-form PMF.

pmf-ℚ : (k i m n : ℕ) ⦃ _ : NonZero (m +ℕ n) ⦄ → ℚ
pmf-ℚ k i m n = + ((k C i) ℕ.* (m ^ i) ℕ.* (n ^ (k ∸ i))) / ((m +ℕ n) ^ k)
  where instance _ = m^n≢0 (m +ℕ n) k

------------------------------------------------------------------------
-- Pascal's recursion, first on numerators and then on the closed form.

private
  regroup : ∀ m n c₁ c₂ p q
          → m ℕ.* (c₁ ℕ.* p ℕ.* (n ℕ.* q)) +ℕ n ℕ.* (c₂ ℕ.* (m ℕ.* p) ℕ.* q)
          ≡ (c₁ +ℕ c₂) ℕ.* (m ℕ.* p) ℕ.* (n ℕ.* q)
  regroup = solve-∀

  regroup-∅ : ∀ m n c p r
            → m ℕ.* (c ℕ.* p ℕ.* r) +ℕ n ℕ.* 0 ≡ (c +ℕ 0) ℕ.* (m ℕ.* p) ℕ.* r
  regroup-∅ = solve-∀

  num-zero : ∀ k m n → n ℕ.* ((k C 0) ℕ.* (m ^ 0) ℕ.* (n ^ (k ∸ 0)))
                     ≡ (suc k C 0) ℕ.* (m ^ 0) ℕ.* (n ^ (suc k ∸ 0))
  num-zero k m n = P.trans (P.cong (n ℕ.*_) (ℕₚ.*-identityˡ (n ^ k)))
                           (P.sym (ℕₚ.*-identityˡ (n ℕ.* n ^ k)))

  -- Below the diagonal (`suc j ≤ k`) the exponent `k ∸ j` splits off the head
  -- factor `n` that the second rectangle contributes; above it that rectangle
  -- is empty, `k C suc j ≡ 0`.
  num-suc : ∀ k j m n
          → m ℕ.* ((k C j) ℕ.* (m ^ j) ℕ.* (n ^ (k ∸ j)))
          +ℕ n ℕ.* ((k C suc j) ℕ.* (m ^ suc j) ℕ.* (n ^ (k ∸ suc j)))
          ≡ (suc k C suc j) ℕ.* (m ^ suc j) ℕ.* (n ^ (k ∸ j))
  num-suc k j m n with suc j ≤? k
  ... | yes j<k = begin
    m ℕ.* (C₁ ℕ.* mᵖ ℕ.* (n ^ (k ∸ j))) +ℕ n ℕ.* (C₂ ℕ.* mᵖ⁺ ℕ.* nʳ)
      ≡⟨ P.cong (λ z → m ℕ.* (C₁ ℕ.* mᵖ ℕ.* z) +ℕ n ℕ.* (C₂ ℕ.* mᵖ⁺ ℕ.* nʳ)) split ⟩
    m ℕ.* (C₁ ℕ.* mᵖ ℕ.* (n ℕ.* nʳ)) +ℕ n ℕ.* (C₂ ℕ.* mᵖ⁺ ℕ.* nʳ)
      ≡⟨ regroup m n C₁ C₂ mᵖ nʳ ⟩
    (C₁ +ℕ C₂) ℕ.* mᵖ⁺ ℕ.* (n ℕ.* nʳ)
      ≡⟨ P.cong₂ (λ x z → x ℕ.* mᵖ⁺ ℕ.* z) (nCk+nC[k+1]≡[n+1]C[k+1] k j) (P.sym split) ⟩
    (suc k C suc j) ℕ.* mᵖ⁺ ℕ.* (n ^ (k ∸ j)) ∎
    where
    C₁ = k C j
    C₂ = k C suc j
    mᵖ = m ^ j
    mᵖ⁺ = m ^ suc j
    nʳ = n ^ (k ∸ suc j)
    split : n ^ (k ∸ j) ≡ n ℕ.* nʳ
    split = P.cong (n ^_) (m∸n≡suc[m∸suc[n]] j<k)
    open P.≡-Reasoning
  ... | no j≮k = begin
    m ℕ.* (C₁ ℕ.* mᵖ ℕ.* nˢ) +ℕ n ℕ.* (C₂ ℕ.* mᵖ⁺ ℕ.* (n ^ (k ∸ suc j)))
      ≡⟨ P.cong (λ z → m ℕ.* (C₁ ℕ.* mᵖ ℕ.* nˢ)
                    +ℕ n ℕ.* (z ℕ.* mᵖ⁺ ℕ.* (n ^ (k ∸ suc j)))) empty ⟩
    m ℕ.* (C₁ ℕ.* mᵖ ℕ.* nˢ) +ℕ n ℕ.* 0
      ≡⟨ regroup-∅ m n C₁ mᵖ nˢ ⟩
    (C₁ +ℕ 0) ℕ.* mᵖ⁺ ℕ.* nˢ
      ≡⟨ P.cong (λ x → x ℕ.* mᵖ⁺ ℕ.* nˢ)
                (P.trans (P.cong (C₁ +ℕ_) (P.sym empty))
                         (nCk+nC[k+1]≡[n+1]C[k+1] k j)) ⟩
    (suc k C suc j) ℕ.* mᵖ⁺ ℕ.* nˢ ∎
    where
    C₁ = k C j
    C₂ = k C suc j
    mᵖ = m ^ j
    mᵖ⁺ = m ^ suc j
    nˢ = n ^ (k ∸ j)
    empty : C₂ ≡ 0
    empty = k>n⇒nCk≡0 (≰⇒> j≮k)
    open P.≡-Reasoning

pmf-ℚ-rec-zero : ∀ k m n ⦃ _ : NonZero (m +ℕ n) ⦄
               → (+ n / (m +ℕ n)) ℚ.* pmf-ℚ k 0 m n
               ≡ pmf-ℚ (suc k) 0 m n
pmf-ℚ-rec-zero k m n = begin
  (+ n / S) ℚ.* pmf-ℚ k 0 m n      ≡⟨ /-*-/ (+ n) S (+ N) (S ^ k) ⟩
  (+ n ℤ.* + N) / (S ^ suc k)      ≡⟨ /-cong (ℤₚ.pos-* n N) P.refl ⟨
  + (n ℕ.* N) / (S ^ suc k)        ≡⟨ /-cong (P.cong +_ (num-zero k m n)) P.refl ⟩
  pmf-ℚ (suc k) 0 m n              ∎
  where
  S = m +ℕ n
  N = (k C 0) ℕ.* (m ^ 0) ℕ.* (n ^ (k ∸ 0))
  instance _ = m^n≢0 S k
  instance _ = m^n≢0 S (suc k)
  open P.≡-Reasoning

pmf-ℚ-rec-suc : ∀ k j m n ⦃ _ : NonZero (m +ℕ n) ⦄
              → ((+ m / (m +ℕ n)) ℚ.* pmf-ℚ k j m n)
              ℚ.+ ((+ n / (m +ℕ n)) ℚ.* pmf-ℚ k (suc j) m n)
              ≡ pmf-ℚ (suc k) (suc j) m n
pmf-ℚ-rec-suc k j m n = begin
  ((+ m / S) ℚ.* pmf-ℚ k j m n) ℚ.+ ((+ n / S) ℚ.* pmf-ℚ k (suc j) m n)
    ≡⟨ P.cong₂ ℚ._+_ (/-*-/ (+ m) S (+ A) (S ^ k)) (/-*-/ (+ n) S (+ B) (S ^ k)) ⟩
  ((+ m ℤ.* + A) / (S ^ suc k)) ℚ.+ ((+ n ℤ.* + B) / (S ^ suc k))
    ≡⟨ /-+-/-same (+ m ℤ.* + A) (+ n ℤ.* + B) (S ^ suc k) ⟩
  ((+ m ℤ.* + A) +ℤ (+ n ℤ.* + B)) / (S ^ suc k)
    ≡⟨ /-cong (P.cong₂ _+ℤ_ (ℤₚ.pos-* m A) (ℤₚ.pos-* n B)) P.refl ⟨
  (+ (m ℕ.* A) +ℤ + (n ℕ.* B)) / (S ^ suc k)
    ≡⟨ /-cong (ℤₚ.pos-+ (m ℕ.* A) (n ℕ.* B)) P.refl ⟨
  + (m ℕ.* A +ℕ n ℕ.* B) / (S ^ suc k)
    ≡⟨ /-cong (P.cong +_ (num-suc k j m n)) P.refl ⟩
  pmf-ℚ (suc k) (suc j) m n ∎
  where
  S = m +ℕ n
  A = (k C j) ℕ.* (m ^ j) ℕ.* (n ^ (k ∸ j))
  B = (k C suc j) ℕ.* (m ^ suc j) ℕ.* (n ^ (k ∸ suc j))
  instance _ = m^n≢0 S k
  instance _ = m^n≢0 S (suc k)
  open P.≡-Reasoning

------------------------------------------------------------------------
-- Event decompositions.

private
  -- For k = 0 the sample space is a singleton, so `exactly 0 ≐ U` and
  -- `exactly (suc i) ≐ ∅`.
  exactly-0-zero-≐-U : (λ (_ : Bool^ 0) → 0 ≡ 0) ≐ U
  exactly-0-zero-≐-U = (λ _ → tt) , (λ _ → P.refl)

  exactly-0-suc-≐-∅ : ∀ {i} → (λ (_ : Bool^ 0) → 0 ≡ suc i) ≐ ∅
  exactly-0-suc-≐-∅ = (λ ()) , (λ ())

  -- For k = suc k', `exactly 0` decomposes as `(↑ not) ⊠ exactly 0` only:
  -- the head bit must be `false`.
  exactly-suc-zero-≐ : ∀ {k} → exactly {suc k} 0 ≐ ((↑ not) ⊠ exactly 0)
  exactly-suc-zero-≐ = forward , backward
    where
      forward : ∀ {k} → exactly {suc k} 0 ⊆ ((↑ not) ⊠ exactly 0)
      forward {x = false , _} eq = tt , eq
      forward {x = true  , _} ()
      backward : ∀ {k} → ((↑ not) ⊠ exactly 0) ⊆ exactly {suc k} 0
      backward {x = false , _} (_  , eq) = eq
      backward {x = true  , _} (() , _)

  -- For k = suc k' and i = suc j, `exactly (suc j)` decomposes as the
  -- disjoint union of two rectangles.
  exactly-suc-suc-≐ : ∀ {k j} → exactly {suc k} (suc j)
                              ≐ ((↑ id) ⊠ exactly j) ∪ ((↑ not) ⊠ exactly (suc j))
  exactly-suc-suc-≐ = forward , backward
    where
      forward : ∀ {k j} → exactly {suc k} (suc j)
                        ⊆ ((↑ id) ⊠ exactly j) ∪ ((↑ not) ⊠ exactly (suc j))
      forward {x = true  , _} eq = inj₁ (tt , suc-injective eq)
      forward {x = false , _} eq = inj₂ (tt , eq)
      backward : ∀ {k j} → ((↑ id) ⊠ exactly j) ∪ ((↑ not) ⊠ exactly (suc j))
                         ⊆ exactly {suc k} (suc j)
      backward {x = true  , _} (inj₁ (_  , eq)) = P.cong suc eq
      backward {x = true  , _} (inj₂ (() , _))
      backward {x = false , _} (inj₁ (() , _))
      backward {x = false , _} (inj₂ (_  , eq)) = eq

  exactly-suc-suc-disjoint : ∀ {k j}
    → disjoint {Ω = Bool × Bool^ k}
        ((↑ id) ⊠ exactly j)
        ((↑ not) ⊠ exactly (suc j))
  exactly-suc-suc-disjoint {ω = true  , _} _        (() , _)
  exactly-suc-suc-disjoint {ω = false , _} (() , _) _

------------------------------------------------------------------------
-- The main theorem: the binomial PMF.

P-exactly-ℚ : ∀ k i m n ⦃ _ : NonZero (m +ℕ n) ⦄
            → binomial k m n ∙ exactly i ≈ fromℚ (pmf-ℚ k i m n)
P-exactly-ℚ zero zero m n = begin
  binomial 0 m n ∙ exactly 0    ≈⟨ ∙-cong exactly-0-zero-≐-U ⟩
  binomial 0 m n ∙ U            ≈⟨ PU≈1 ⟩
  1#                            ≈⟨ fromℚ-1 ⟨
  fromℚ (+ 1 / 1)               ∎
  where open ≈-Reasoning setoid
P-exactly-ℚ zero (suc i) m n = begin
  binomial 0 m n ∙ exactly (suc i) ≈⟨ ∙-cong exactly-0-suc-≐-∅ ⟩
  binomial 0 m n ∙ ∅               ≈⟨ P∅≈0 ⟩
  0#                               ≈⟨ fromℚ-0 ⟨
  fromℚ (+ 0 / 1)                  ∎
  where open ≈-Reasoning setoid
P-exactly-ℚ (suc k) zero m n = begin
  binomial (suc k) m n ∙ exactly 0
    ≈⟨ ∙-cong exactly-suc-zero-≐ ⟩
  binomial (suc k) m n ∙ ((↑ not) ⊠ exactly 0)
    ≈⟨ ⊗-rect ⟩
  bernoulli m n ∙ (↑ not) * binomial k m n ∙ exactly 0
    ≈⟨ *-cong (P-bernoulli-false m n) (P-exactly-ℚ k 0 m n) ⟩
  fromℚ (+ n / (m +ℕ n)) * fromℚ (pmf-ℚ k 0 m n)
    ≈⟨ fromℚ-homomorphism ⟩
  fromℚ ((+ n / (m +ℕ n)) ℚ.* pmf-ℚ k 0 m n)
    ≡⟨ P.cong fromℚ (pmf-ℚ-rec-zero k m n) ⟩
  fromℚ (pmf-ℚ (suc k) 0 m n)
    ∎
  where open ≈-Reasoning setoid
P-exactly-ℚ (suc k) (suc j) m n = begin
  binomial (suc k) m n ∙ exactly (suc j)
    ≈⟨ ∙-cong exactly-suc-suc-≐ ⟩
  binomial (suc k) m n ∙ (((↑ id) ⊠ exactly j) ∪ ((↑ not) ⊠ exactly (suc j)))
    ≈⟨ P-distrib-disjoint (exactly-suc-suc-disjoint {k} {j}) ⟨
  binomial (suc k) m n ∙ ((↑ id) ⊠ exactly j)
  + binomial (suc k) m n ∙ ((↑ not) ⊠ exactly (suc j))
    ≈⟨ +-cong ⊗-rect ⊗-rect ⟩
  bernoulli m n ∙ (↑ id) * binomial k m n ∙ exactly j
  + bernoulli m n ∙ (↑ not) * binomial k m n ∙ exactly (suc j)
    ≈⟨ +-cong (*-cong (P-bernoulli-true m n) (P-exactly-ℚ k j m n))
              (*-cong (P-bernoulli-false m n) (P-exactly-ℚ k (suc j) m n)) ⟩
  fromℚ (+ m / (m +ℕ n)) * fromℚ (pmf-ℚ k j m n)
  + fromℚ (+ n / (m +ℕ n)) * fromℚ (pmf-ℚ k (suc j) m n)
    ≈⟨ +-cong fromℚ-homomorphism fromℚ-homomorphism ⟩
  fromℚ ((+ m / (m +ℕ n)) ℚ.* pmf-ℚ k j m n)
  + fromℚ ((+ n / (m +ℕ n)) ℚ.* pmf-ℚ k (suc j) m n)
    ≈⟨ Eq.sym (fromℚ-+-homo _ _) ⟩
  fromℚ (((+ m / (m +ℕ n)) ℚ.* pmf-ℚ k j m n)
       ℚ.+ ((+ n / (m +ℕ n)) ℚ.* pmf-ℚ k (suc j) m n))
    ≡⟨ P.cong fromℚ (pmf-ℚ-rec-suc k j m n) ⟩
  fromℚ (pmf-ℚ (suc k) (suc j) m n)
    ∎
  where open ≈-Reasoning setoid

------------------------------------------------------------------------
-- Sample applications.

-- Two fair coins, exactly one `true`:  C(2,1)·(1/2)·(1/2) = 1/2.
two-fair-one : binomial 2 1 1 ∙ exactly 1 ≈ fromℚ (+ 1 / 2)
two-fair-one = P-exactly-ℚ 2 1 1 1

-- Three fair coins, exactly two `true`:  C(3,2)·(1/2)²·(1/2) = 3/8.
three-fair-two : binomial 3 1 1 ∙ exactly 2 ≈ fromℚ (+ 3 / 8)
three-fair-two = P-exactly-ℚ 3 2 1 1
