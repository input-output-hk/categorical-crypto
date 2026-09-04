{-# OPTIONS --safe --without-K --guardedness #-}

-- `iterₚ-codiagonal` — a loop whose body is itself a loop over the same variable
-- is one loop.
--
-- The two sandwiches nest.  What the quantitative setting costs is a SECOND
-- recursion, because the inner loop has to be measured against the OUTER loop's
-- test:
--
--   `H1 n`   the outer loop at budget `n`, dominated by the fused loop;
--   `H2 n j` the inner loop at budget `j`, measured against `Tᵗ (iterₚ v) P n`,
--            dominated by the fused loop.
--
-- `H1 (suc n)` peels one outer turn and lands on `H2 n (suc n)`; `H2` recurses on
-- `j` alone and discharges its `inj₁`-summand branch with `H1 n`, which it
-- receives as the parameter `rec`.  So the pair is lexicographic in `(n , j)`, and
-- the termination checker sees it as `H1`'s recursion on `n` handing `H1 n` to a
-- helper that recurses on `j` — no well-founded machinery.
--
-- The reverse direction needs only ONE recursion: the analogue of `H2` there is a
-- COROLLARY of `K1` (one more `stepᵢ-boundA` re-exposes the outer loop's test),
-- which is `K2` below.

open import Data.Nat.Base using (ℕ; zero; suc) renaming (_+_ to _+ℕ_; _≤_ to _≤ℕ_)
open import Data.Nat.Properties using (n≤1+n)
open import Data.Product.Base using (Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Rational as ℚ using (ℚ)
open import Data.Rational.Properties using (≤-refl; ≤-reflexive; ≤-trans)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Function.Base using (_∘_; _∘′_)
open import Level using (Level)
open import Relation.Binary.PropositionalEquality using (sym)

open import ProbabilisticLogic.Dp
open import ProbabilisticLogic.Dp.Iter

module ProbabilisticLogic.Dp.Iter.Codiagonal where

private variable ℓ : Level

flatBody : {S A B : Set ℓ} → Body S A (B ⊎ A) → Body S A B
flatBody v = mapₚ flat ∘ v

module _ {S A B : Set ℓ} (v : Body S A (B ⊎ A)) (P : S × B → ℚ) (nn : NNF P) where

  H2 : (n : ℕ)
       (rec : ∀ sp → Σ[ M ∈ ℕ ] (cum n (iterₚ (iterₚ v) sp) P
                                 ℚ.≤ cum M (iterₚ (flatBody v) sp) P))
       (j : ℕ) (sp : S × A)
     → Σ[ M ∈ ℕ ] (cum j (iterₚ v sp) (Tᵗ (iterₚ v) P n)
                   ℚ.≤ cum M (iterₚ (flatBody v) sp) P)
  H2 n rec zero    sp = 0 , ≤-refl
  H2 n rec (suc j) sp =
    suc (suc j) +ℕ i′ , ≤-trans f1 (≤-trans f2 (≤-trans (≤-reflexive f3) f4))
    where
    Φ : S × ((B ⊎ A) ⊎ A) → ℕ → Set
    Φ r i = Tᵗ v (Tᵗ (iterₚ v) P n) j r ℚ.≤ Tᵗ (flatBody v) P i (flat r)

    up : ∀ r {i i₂} → i ≤ℕ i₂ → Φ r i → Φ r i₂
    up (s , inj₁ (inj₁ b)) le q = q
    up (s , inj₁ (inj₂ p)) le q =
      ≤-trans q (cum-mono le (iterₚ (flatBody v) (s , p)) P nn)
    up (s , inj₂ p)        le q =
      ≤-trans q (cum-mono le (iterₚ (flatBody v) (s , p)) P nn)

    wit : ∀ r → Σ[ i ∈ ℕ ] Φ r i
    wit (s , inj₁ (inj₁ b)) = 0 , ≤-refl
    wit (s , inj₁ (inj₂ p)) = rec (s , p)
    wit (s , inj₂ p)        = H2 n rec j (s , p)

    unif = uniformize Φ up wit (suc j) (v sp)
    i′ = proj₁ unif

    f1 = stepᵢ-boundA j v (v sp) (Tᵗ (iterₚ v) P n) (Tᵗ-nn (iterₚ v) P n nn)
    f2 = cum-mono-Supp (suc j) (v sp) (Tᵗ v (Tᵗ (iterₚ v) P n) j)
                       (Tᵗ (flatBody v) P i′ ∘′ flat) (proj₂ unif)
    f3 = sym (mapₚ-cum (suc j) flat (v sp) (Tᵗ (flatBody v) P i′))
    f4 = stepᵢ-boundB (suc (suc j)) i′ (flatBody v) (flatBody v sp) P nn

  H1 : (n : ℕ) (sp : S × A)
     → Σ[ M ∈ ℕ ] (cum n (iterₚ (iterₚ v) sp) P ℚ.≤ cum M (iterₚ (flatBody v) sp) P)
  H1 zero    sp = 0 , ≤-refl
  H1 (suc n) sp =
    let M , le = H2 n (H1 n) (suc n) sp
    in M , ≤-trans (stepᵢ-boundA n (iterₚ v) (iterₚ v sp) P nn) le

  K1 : (n : ℕ) (sp : S × A)
     → Σ[ M ∈ ℕ ] (cum n (iterₚ (flatBody v) sp) P ℚ.≤ cum M (iterₚ (iterₚ v) sp) P)
  K1 zero    sp = 0 , ≤-refl
  K1 (suc n) sp =
    (n +ℕ i′) +ℕ i′ , ≤-trans d1 (≤-trans (≤-reflexive d2) (≤-trans d3 (≤-trans d4 d5)))
    where
    -- The inner loop's test re-exposed: one more `stepᵢ-boundA` past `K1`.
    K2 : (i : ℕ) (sq : S × A)
       → Σ[ M ∈ ℕ ] (cum i (iterₚ (flatBody v) sq) P
                     ℚ.≤ cum M (iterₚ v sq) (Tᵗ (iterₚ v) P M))
    K2 i sq =
      let M , le = K1 i sq
      in suc M
       , ≤-trans le
         (≤-trans (cum-mono (n≤1+n M) (iterₚ (iterₚ v) sq) P nn)
         (≤-trans (stepᵢ-boundA M (iterₚ v) (iterₚ v sq) P nn)
                  (cum-mono-P (suc M) (iterₚ v sq) (Tᵗ (iterₚ v) P M)
                              (Tᵗ (iterₚ v) P (suc M))
                              (Tᵗ-mono (iterₚ v) P nn (n≤1+n M)))))

    Ψ : S × ((B ⊎ A) ⊎ A) → ℕ → Set
    Ψ r i = Tᵗ (flatBody v) P n (flat r) ℚ.≤ Tᵗ v (Tᵗ (iterₚ v) P i) i r

    up : ∀ r {i i₂} → i ≤ℕ i₂ → Ψ r i → Ψ r i₂
    up (s , inj₁ (inj₁ b)) le q = q
    up (s , inj₁ (inj₂ p)) le q =
      ≤-trans q (cum-mono le (iterₚ (iterₚ v) (s , p)) P nn)
    up (s , inj₂ p) {i} {i₂} le q = ≤-trans q
      (≤-trans (cum-mono le (iterₚ v (s , p)) (Tᵗ (iterₚ v) P i)
                         (Tᵗ-nn (iterₚ v) P i nn))
               (cum-mono-P i₂ (iterₚ v (s , p)) (Tᵗ (iterₚ v) P i)
                           (Tᵗ (iterₚ v) P i₂) (Tᵗ-mono (iterₚ v) P nn le)))

    wit : ∀ r → Σ[ i ∈ ℕ ] Ψ r i
    wit (s , inj₁ (inj₁ b)) = 0 , ≤-refl
    wit (s , inj₁ (inj₂ p)) = K1 n (s , p)
    wit (s , inj₂ p)        = K2 n (s , p)

    unif = uniformize Ψ up wit n (v sp)
    i′ = proj₁ unif

    d1 = stepᵢ-boundA n (flatBody v) (flatBody v sp) P nn
    d2 = mapₚ-cum n flat (v sp) (Tᵗ (flatBody v) P n)
    d3 = cum-mono-Supp n (v sp) (Tᵗ (flatBody v) P n ∘′ flat)
                       (Tᵗ v (Tᵗ (iterₚ v) P i′) i′) (proj₂ unif)
    d4 = stepᵢ-boundB n i′ v (v sp) (Tᵗ (iterₚ v) P i′) (Tᵗ-nn (iterₚ v) P i′ nn)
    d5 = stepᵢ-boundB (n +ℕ i′) i′ (iterₚ v) (iterₚ v sp) P nn

iterₚ-codiagonal : {S A B : Set ℓ} (v : Body S A (B ⊎ A)) (sa : S × A)
                 → iterₚ (iterₚ v) sa ≈ₚ iterₚ (mapₚ flat ∘ v) sa
iterₚ-codiagonal v sa = (λ P nn n → H1 v P nn n sa) , (λ P nn n → K1 v P nn n sa)
