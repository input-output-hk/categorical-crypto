{-# OPTIONS --safe --without-K --guardedness #-}

-- Transfer of `iterₚ` onto an arbitrary FUEL-INDEXED family, one direction at
-- a time and at a fixed test.
--
-- `Dp.Iter.Transfer` transfers a loop onto another loop along a PURE state map
-- `k`, in both directions at once.  Neither half of that survives when the
-- target is a finite object: the two sides then agree only up to a depth, so
-- the target is a family `tgt n` refined by a fuel `n` rather than a map, and
-- the truncation the fuel imposes scores differently under different tests, so
-- the two directions carry different hypotheses and only the test each is
-- valid at.
--
-- The template is `Transfer.fwd`'s all the same: peel one turn off the loop
-- with `stepᵢ-boundA`, `uniformize` the per-branch budgets the recursive calls
-- hand back, spend the hypothesis at the reassembled test, and put the turns
-- back with `stepᵢ-boundB`/`>>=ₚ-boundB`.  What moves is which side the loop is
-- on: `fwd` recurses on the BUDGET (the fuel tracks it), `bwd` on the FUEL
-- (the budget is arbitrary).

open import Data.Nat.Base using (ℕ; zero; suc; _≤_) renaming (_+_ to _+ℕ_)
open import Data.Product.Base using (Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Rational as ℚ using (ℚ; 0ℚ)
open import Data.Rational.Properties using (≤-refl; ≤-trans)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Level using (Level)

open import ProbabilisticLogic.Dp
open import ProbabilisticLogic.Dp.Dominate using (Dom₀)
open import ProbabilisticLogic.Dp.Iter

module ProbabilisticLogic.Dp.Iter.OneSided where

private variable ℓ : Level

-- The loop, the two tests and the fuel-indexed target are module parameters:
-- the `where` blocks below mention them, and a `variable` there re-generalizes.
module _ {S A B T : Set ℓ} (u : Body S A B)
         (P : S × B → ℚ) (nnP : NNF P) (Q : T → ℚ) (nnQ : NNF Q)
         (tgt : ℕ → S × A → Dₚ T) (res : ℕ → S × B → Dₚ T) where

  -- What one turn of the loop is aimed at: a result leaves for `res`, a loop
  -- variable re-enters `tgt` with one fuel less.
  pick : ℕ → S × (B ⊎ A) → Dₚ T
  pick i (s , inj₁ b) = res i (s , b)
  pick i (s , inj₂ p) = tgt i (s , p)

  ------------------------------------------------------------------------
  -- The loop is dominated by the target

  module _ (hres : (i : ℕ) (sb : S × B) → Σ[ m ∈ ℕ ] (P sb ℚ.≤ cum m (res i sb) Q))
           (hstep : (i : ℕ) (sa : S × A) → Dom₀ Q (u sa >>=ₚ pick i) (tgt (suc i) sa))
           where

    fwd : (n : ℕ) (sa : S × A)
        → Σ[ m ∈ ℕ ] (cum n (iterₚ u sa) P ℚ.≤ cum m (tgt n sa) Q)
    fwd zero    sa = 0 , ≤-refl
    fwd (suc n) sa = j , ≤-trans s1 (≤-trans s2 (≤-trans s3 s4))
      where
      Φ : S × (B ⊎ A) → ℕ → Set
      Φ r i = Tᵗ u P n r ℚ.≤ cum i (pick n r) Q

      up : ∀ r {i i′} → i ≤ i′ → Φ r i → Φ r i′
      up r le q = ≤-trans q (cum-mono le (pick n r) Q nnQ)

      wit : ∀ r → Σ[ i ∈ ℕ ] Φ r i
      wit (s , inj₁ b) = hres n (s , b)
      wit (s , inj₂ p) = fwd n (s , p)

      unif = uniformize Φ up wit (suc n) (u sa)
      i′ = proj₁ unif

      s1 = stepᵢ-boundA n u (u sa) P nnP
      s2 = cum-mono-Supp (suc n) (u sa) (Tᵗ u P n) (λ r → cum i′ (pick n r) Q)
                         (proj₂ unif)
      s3 = >>=ₚ-boundB (suc n) i′ (u sa) (pick n) Q nnQ

      dom = hstep n sa (suc n +ℕ i′)
      j = proj₁ dom
      s4 = proj₂ dom

  ------------------------------------------------------------------------
  -- …and dominates it

  module _ (hres : (i n : ℕ) (sb : S × B) → cum n (res i sb) Q ℚ.≤ P sb)
           (hstep : (i : ℕ) (sa : S × A) → Dom₀ Q (tgt (suc i) sa) (u sa >>=ₚ pick i))
           (hbase : (sa : S × A) (n : ℕ) → cum n (tgt 0 sa) Q ℚ.≤ 0ℚ)
           where

    bwd : (f : ℕ) (sa : S × A) (n : ℕ)
        → Σ[ m ∈ ℕ ] (cum n (tgt f sa) Q ℚ.≤ cum m (iterₚ u sa) P)
    bwd zero    sa n = 0 , hbase sa n
    bwd (suc f) sa n =
      m₁ +ℕ i′ , ≤-trans t1 (≤-trans t2 (≤-trans t3 t4))
      where
      dom = hstep f sa n
      m₁ = proj₁ dom
      t1 = proj₂ dom
      t2 = >>=ₚ-boundA m₁ (u sa) (pick f) Q nnQ

      Ψ : S × (B ⊎ A) → ℕ → Set
      Ψ r i = cum m₁ (pick f r) Q ℚ.≤ Tᵗ u P i r

      up : ∀ r {i i′} → i ≤ i′ → Ψ r i → Ψ r i′
      up (s , inj₁ b) le q = q
      up (s , inj₂ p) le q = ≤-trans q (cum-mono le (iterₚ u (s , p)) P nnP)

      wit : ∀ r → Σ[ i ∈ ℕ ] Ψ r i
      wit (s , inj₁ b) = 0 , hres f m₁ (s , b)
      wit (s , inj₂ p) = bwd f (s , p) m₁

      unif = uniformize Ψ up wit m₁ (u sa)
      i′ = proj₁ unif

      t3 = cum-mono-Supp m₁ (u sa) (λ r → cum m₁ (pick f r) Q) (Tᵗ u P i′)
                         (proj₂ unif)
      t4 = stepᵢ-boundB m₁ i′ u (u sa) P nnP
