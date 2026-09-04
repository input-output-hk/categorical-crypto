{-# OPTIONS --safe --without-K --guardedness #-}

-- `iterₚ-transfer` — transfer of `iterₚ` along a PURE simulation.
--
-- `mapₚ` inserts a junction delay per turn, so the two loops do NOT run in
-- lockstep; lockstep is never needed, because `_≼ₚ_` only ever asks for *some*
-- budget on the right and the loop sandwich trades budget for turns.  The proof is
-- therefore the `iterₚ-congᵖ` template with the simulation integrated into the
-- test:
--
--   * `stepᵢ-boundA` peels one turn off the left loop, measuring it against
--     `Tᵗ … n` — one budget lower, which is what makes the recursion well-founded;
--   * `uniformize` maxes the per-value budgets the recursive calls hand back over
--     the depth-`n` support of the body's output;
--   * `mapₚ-cum` is EXACT, so relabelling the test by `φ k m` costs exactly one
--     budget level and no inequality;
--   * the simulation hypothesis is spent at that relabelled test;
--   * `stepᵢ-boundB` puts the turns back on the right loop.
--
-- `Dp.Elgot`'s `iterₚ-uniform` (`m = id`, `k = padₛ θ`) and `iterₚ-ctx` (`k`/`m`
-- the context-injections at each fixed context value) are instances.

open import Data.Nat.Base using (ℕ; zero; suc) renaming (_+_ to _+ℕ_; _≤_ to _≤ℕ_)
open import Data.Nat.Properties using (n≤1+n)
open import Data.Product.Base using (Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Rational as ℚ using (ℚ)
open import Data.Rational.Properties using (≤-refl; ≤-reflexive; ≤-trans)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Function.Base using (_∘′_)
open import Level using (Level)
open import Relation.Binary.PropositionalEquality using (sym)

open import ProbabilisticLogic.Dp
open import ProbabilisticLogic.Dp.Iter

module ProbabilisticLogic.Dp.Iter.Transfer where

private variable ℓ : Level

-- `S`…`B′`, the two bodies, the two pure relabellings and the test are all module
-- parameters: the recursion below keeps the test fixed and varies only the budget.
module _ {S A B S′ A′ B′ : Set ℓ}
  (u : Body S A B) (u′ : Body S′ A′ B′)
  (k : S × A → S′ × A′) (m : S × B → S′ × B′)
  (P : S′ × B′ → ℚ) (nn : NNF P) where

  nnm : NNF (λ sb → P (m sb))
  nnm sb = nn (m sb)

  module _ (hyp : ∀ sa → mapₚ (φ k m) (u sa) ≼ₚ u′ (k sa)) where

    fwd : (n : ℕ) (sa : S × A)
        → Σ[ M ∈ ℕ ] (cum n (iterₚ u sa) (λ sb → P (m sb)) ℚ.≤ cum M (iterₚ u′ (k sa)) P)
    fwd zero    sa = 0 , ≤-refl
    fwd (suc n) sa =
      j +ℕ i′ , ≤-trans s1 (≤-trans s2 (≤-trans (≤-reflexive s3) (≤-trans s4 s5)))
      where
      Φ : S × (B ⊎ A) → ℕ → Set
      Φ r i = Tᵗ u (λ sb → P (m sb)) n r ℚ.≤ Tᵗ u′ P i (φ k m r)

      up : ∀ r {i i′} → i ≤ℕ i′ → Φ r i → Φ r i′
      up (s , inj₁ b) le q = q
      up (s , inj₂ p) le q = ≤-trans q (cum-mono le (iterₚ u′ (k (s , p))) P nn)

      wit : ∀ r → Σ[ i ∈ ℕ ] Φ r i
      wit (s , inj₁ b) = 0 , ≤-refl
      wit (s , inj₂ p) = fwd n (s , p)

      unif = uniformize Φ up wit (suc n) (u sa)
      i′ = proj₁ unif

      s1 = stepᵢ-boundA n u (u sa) (λ sb → P (m sb)) nnm
      s2 = cum-mono-Supp (suc n) (u sa) (Tᵗ u (λ sb → P (m sb)) n)
                         (Tᵗ u′ P i′ ∘′ φ k m) (proj₂ unif)
      s3 = sym (mapₚ-cum (suc n) (φ k m) (u sa) (Tᵗ u′ P i′))

      dom = hyp sa (Tᵗ u′ P i′) (Tᵗ-nn u′ P i′ nn) (suc (suc n))
      j = proj₁ dom
      s4 = proj₂ dom
      s5 = stepᵢ-boundB j i′ u′ (u′ (k sa)) P nn

  module _ (hyp : ∀ sa → u′ (k sa) ≼ₚ mapₚ (φ k m) (u sa)) where

    bwd : (n : ℕ) (sa : S × A)
        → Σ[ M ∈ ℕ ] (cum n (iterₚ u′ (k sa)) P ℚ.≤ cum M (iterₚ u sa) (λ sb → P (m sb)))
    bwd zero    sa = 0 , ≤-refl
    bwd (suc n) sa =
      j +ℕ i′ , ≤-trans t1 (≤-trans t2 (≤-trans t2′ (≤-trans (≤-reflexive t3)
                (≤-trans t4 t5))))
      where
      Ψ : S × (B ⊎ A) → ℕ → Set
      Ψ r i = Tᵗ u′ P n (φ k m r) ℚ.≤ Tᵗ u (λ sb → P (m sb)) i r

      up : ∀ r {i i′} → i ≤ℕ i′ → Ψ r i → Ψ r i′
      up (s , inj₁ b) le q = q
      up (s , inj₂ p) le q =
        ≤-trans q (cum-mono le (iterₚ u (s , p)) (λ sb → P (m sb)) nnm)

      wit : ∀ r → Σ[ i ∈ ℕ ] Ψ r i
      wit (s , inj₁ b) = 0 , ≤-refl
      wit (s , inj₂ p) = bwd n (s , p)

      t1 = stepᵢ-boundA n u′ (u′ (k sa)) P nn

      dom = hyp sa (Tᵗ u′ P n) (Tᵗ-nn u′ P n nn) (suc n)
      j = proj₁ dom
      t2 = proj₂ dom
      t2′ = cum-mono (n≤1+n j) (mapₚ (φ k m) (u sa)) (Tᵗ u′ P n) (Tᵗ-nn u′ P n nn)
      t3 = mapₚ-cum j (φ k m) (u sa) (Tᵗ u′ P n)

      unif = uniformize Ψ up wit j (u sa)
      i′ = proj₁ unif

      t4 = cum-mono-Supp j (u sa) (Tᵗ u′ P n ∘′ φ k m)
                         (Tᵗ u (λ sb → P (m sb)) i′) (proj₂ unif)
      t5 = stepᵢ-boundB j i′ u (u sa) (λ sb → P (m sb)) nnm

iterₚ-transfer : {S A B S′ A′ B′ : Set ℓ} (u : Body S A B) (u′ : Body S′ A′ B′)
                 (k : S × A → S′ × A′) (m : S × B → S′ × B′)
               → (∀ sa → u′ (k sa) ≈ₚ mapₚ (φ k m) (u sa))
               → (sa : S × A) → iterₚ u′ (k sa) ≈ₚ mapₚ m (iterₚ u sa)
iterₚ-transfer u u′ k m h sa = fst , snd
  where
  fst : iterₚ u′ (k sa) ≼ₚ mapₚ m (iterₚ u sa)
  fst P nn n =
    let M , le = bwd u u′ k m P nn (λ sa′ → proj₁ (h sa′)) n sa
    in suc M , ≤-trans le (≤-reflexive (sym (mapₚ-cum M m (iterₚ u sa) P)))

  snd : mapₚ m (iterₚ u sa) ≼ₚ iterₚ u′ (k sa)
  snd P nn zero    = 0 , ≤-refl
  snd P nn (suc n) =
    let M , le = fwd u u′ k m P nn (λ sa′ → proj₂ (h sa′)) n sa
    in M , ≤-trans (≤-reflexive (mapₚ-cum n m (iterₚ u sa) P)) le
