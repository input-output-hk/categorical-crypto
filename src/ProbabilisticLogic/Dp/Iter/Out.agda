{-# OPTIONS --safe --without-K --guardedness #-}

-- `iterₚ-out` — naturality of `iterₚ` in its output, for an EFFECTFUL
-- post-composition.
--
-- Not an instance of `Dp.Iter.Transfer.iterₚ-transfer`: there the relabelling `m`
-- is a pure function, here `k : S × B → Dₚ (S × C)` may itself diverge and branch.
--
-- The proof is the same sandwich template as `Transfer`, with one extra wrinkle:
-- the loop's own test now carries `k`'s budget, and if that budget is tied to the
-- loop's own (`Q sb = cum n (k sb) P` with `n` the loop budget) the recursion does
-- NOT close — the inner obligation lands at budget `n + n`.  The fix is to let the
-- two budgets vary independently: `core` keeps `k`'s budget `mk` FIXED while the
-- loop budget decreases, and the top-level call instantiates `mk` once.  `core′`
-- needs no such split because on that side the sandwich is applied in the opposite
-- order.

open import Data.Nat.Base using (ℕ; zero; suc) renaming (_+_ to _+ℕ_; _≤_ to _≤ℕ_)
open import Data.Nat.Properties using (n≤1+n)
open import Data.Product.Base using (Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Rational as ℚ using (ℚ)
open import Data.Rational.Properties using (≤-refl; ≤-reflexive; ≤-trans)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Function.Base using (_∘′_)
open import Level using (Level)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans)

open import ProbabilisticLogic.Dp
open import ProbabilisticLogic.Dp.Commutative using (cum-cong-P)
open import ProbabilisticLogic.Dp.Iter

module ProbabilisticLogic.Dp.Iter.Out where

private variable ℓ : Level

------------------------------------------------------------------------
-- Post-composing the exit branch, leaving the loop branch alone

inlₒ : {S C A : Set ℓ} → S × C → S × (C ⊎ A)
inlₒ (s , c) = s , inj₁ c

outκ : {S A B C : Set ℓ} → (S × B → Dₚ (S × C)) → S × (B ⊎ A) → Dₚ (S × (C ⊎ A))
outκ k (s , inj₁ b) = mapₚ inlₒ (k (s , b))
outκ k (s , inj₂ p) = returnₚ (s , inj₂ p)

bodyₒ : {S A B C : Set ℓ} → Body S A B → (S × B → Dₚ (S × C)) → Body S A C
bodyₒ u k sa = u sa >>=ₚ outκ k

-- `Tᵗ`'s exit clause is `P` composed with `inlₒ` up to `Σ`-eta, so relabelling
-- the test costs no inequality.
Tᵗ-inlₒ : {S A C : Set ℓ} (v : Body S A C) (P : S × C → ℚ) (j : ℕ) (sc : S × C)
        → Tᵗ v P j (inlₒ sc) ≡ P sc
Tᵗ-inlₒ v P j (s , c) = refl

outκ-inj₁ : {S A B C : Set ℓ} (n : ℕ) (k : S × B → Dₚ (S × C)) (v : Body S A C)
            (P : S × C → ℚ) (j : ℕ) (s : S) (b : B)
          → cum (suc n) (outκ {A = A} k (s , inj₁ b)) (Tᵗ v P j) ≡ cum n (k (s , b)) P
outκ-inj₁ n k v P j s b =
  trans (mapₚ-cum n inlₒ (k (s , b)) (Tᵗ v P j))
        (cum-cong-P n (k (s , b)) (Tᵗ v P j ∘′ inlₒ) P (Tᵗ-inlₒ v P j))

outκ-inj₂ : {S A B C : Set ℓ} (n : ℕ) (k : S × B → Dₚ (S × C)) (v : Body S A C)
            (P : S × C → ℚ) (j : ℕ) (s : S) (p : A)
          → cum (suc n) (outκ {B = B} k (s , inj₂ p)) (Tᵗ v P j)
          ≡ cum j (iterₚ v (s , p)) P
outκ-inj₂ n k v P j s p = returnₚ-cum n (s , inj₂ p) (Tᵗ v P j)

------------------------------------------------------------------------
-- The two independent-budget cores

module _ {S A B C : Set ℓ} (u : Body S A B) (k : S × B → Dₚ (S × C))
  (P : S × C → ℚ) (nn : NNF P) where

  core : (n mk : ℕ) (sp : S × A)
       → Σ[ M ∈ ℕ ] (cum n (iterₚ u sp) (λ sb → cum mk (k sb) P)
                     ℚ.≤ cum M (iterₚ (bodyₒ u k) sp) P)
  core zero    mk sp = 0 , ≤-refl
  core (suc n) mk sp =
    (suc n +ℕ i′) +ℕ i′ , ≤-trans c1 (≤-trans c2 (≤-trans c3 c4))
    where
    Q : S × B → ℚ
    Q sb = cum mk (k sb) P

    nnQ : NNF Q
    nnQ sb = cum-nn mk (k sb) P nn

    Φ : S × (B ⊎ A) → ℕ → Set
    Φ r i = Tᵗ u Q n r ℚ.≤ cum i (outκ k r) (Tᵗ (bodyₒ u k) P i)

    up : ∀ r {i i₂} → i ≤ℕ i₂ → Φ r i → Φ r i₂
    up r {i} {i₂} le q = ≤-trans q
      (≤-trans (cum-mono le (outκ k r) (Tᵗ (bodyₒ u k) P i)
                         (Tᵗ-nn (bodyₒ u k) P i nn))
               (cum-mono-P i₂ (outκ k r) (Tᵗ (bodyₒ u k) P i) (Tᵗ (bodyₒ u k) P i₂)
                           (Tᵗ-mono (bodyₒ u k) P nn le)))

    wit : ∀ r → Σ[ i ∈ ℕ ] Φ r i
    wit (s , inj₁ b) =
      suc mk , ≤-reflexive (sym (outκ-inj₁ mk k (bodyₒ u k) P (suc mk) s b))
    wit (s , inj₂ p) =
      let M , le = core n mk (s , p)
      in suc M
       , ≤-trans le (≤-trans (cum-mono (n≤1+n M) (iterₚ (bodyₒ u k) (s , p)) P nn)
                    (≤-reflexive (sym (outκ-inj₂ M k (bodyₒ u k) P (suc M) s p))))

    unif = uniformize Φ up wit (suc n) (u sp)
    i′ = proj₁ unif

    c1 = stepᵢ-boundA n u (u sp) Q nnQ
    c2 = cum-mono-Supp (suc n) (u sp) (Tᵗ u Q n)
                       (λ r → cum i′ (outκ k r) (Tᵗ (bodyₒ u k) P i′)) (proj₂ unif)
    c3 = >>=ₚ-boundB (suc n) i′ (u sp) (outκ k) (Tᵗ (bodyₒ u k) P i′)
                     (Tᵗ-nn (bodyₒ u k) P i′ nn)
    c4 = stepᵢ-boundB (suc n +ℕ i′) i′ (bodyₒ u k) (bodyₒ u k sp) P nn

  core′ : (n : ℕ) (sp : S × A)
        → Σ[ M ∈ ℕ ] (cum n (iterₚ (bodyₒ u k) sp) P
                      ℚ.≤ cum M (iterₚ u sp) (λ sb → cum n (k sb) P))
  core′ zero    sp = 0 , ≤-refl
  core′ (suc n) sp = suc n +ℕ i′ , ≤-trans e1 (≤-trans e2 (≤-trans e3 e4))
    where
    Q : S × B → ℚ
    Q sb = cum (suc n) (k sb) P

    nnQ : NNF Q
    nnQ sb = cum-nn (suc n) (k sb) P nn

    Ψ : S × (B ⊎ A) → ℕ → Set
    Ψ r i = cum (suc n) (outκ k r) (Tᵗ (bodyₒ u k) P n) ℚ.≤ Tᵗ u Q i r

    up : ∀ r {i i₂} → i ≤ℕ i₂ → Ψ r i → Ψ r i₂
    up (s , inj₁ b) le q = q
    up (s , inj₂ p) le q = ≤-trans q (cum-mono le (iterₚ u (s , p)) Q nnQ)

    wit : ∀ r → Σ[ i ∈ ℕ ] Ψ r i
    wit (s , inj₁ b) =
      0 , ≤-trans (≤-reflexive (outκ-inj₁ n k (bodyₒ u k) P n s b))
                  (cum-mono (n≤1+n n) (k (s , b)) P nn)
    wit (s , inj₂ p) =
      let M , le = core′ n (s , p)
      in M
       , ≤-trans (≤-reflexive (outκ-inj₂ n k (bodyₒ u k) P n s p))
         (≤-trans le
                  (cum-mono-P M (iterₚ u (s , p)) (λ sb → cum n (k sb) P) Q
                              (λ sb → cum-mono (n≤1+n n) (k sb) P nn)))

    e1 = stepᵢ-boundA n (bodyₒ u k) (bodyₒ u k sp) P nn
    e2 = >>=ₚ-boundA (suc n) (u sp) (outκ k) (Tᵗ (bodyₒ u k) P n)
                     (Tᵗ-nn (bodyₒ u k) P n nn)

    unif = uniformize Ψ up wit (suc n) (u sp)
    i′ = proj₁ unif

    e3 = cum-mono-Supp (suc n) (u sp)
                       (λ r → cum (suc n) (outκ k r) (Tᵗ (bodyₒ u k) P n))
                       (Tᵗ u Q i′) (proj₂ unif)
    e4 = stepᵢ-boundB (suc n) i′ u (u sp) Q nnQ

iterₚ-out : {S A B C : Set ℓ} (u : Body S A B) (k : S × B → Dₚ (S × C)) (sa : S × A)
          → (iterₚ u sa >>=ₚ k) ≈ₚ iterₚ (bodyₒ u k) sa
iterₚ-out u k sa = fst , snd
  where
  fst : (iterₚ u sa >>=ₚ k) ≼ₚ iterₚ (bodyₒ u k) sa
  fst P nn n =
    let M , le = core u k P nn n n sa
    in M , ≤-trans (>>=ₚ-boundA n (iterₚ u sa) k P nn) le

  snd : iterₚ (bodyₒ u k) sa ≼ₚ (iterₚ u sa >>=ₚ k)
  snd P nn n =
    let M , le = core′ u k P nn n sa
    in M +ℕ n , ≤-trans le (>>=ₚ-boundB M n (iterₚ u sa) k P nn)
