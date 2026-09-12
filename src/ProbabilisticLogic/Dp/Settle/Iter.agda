{-# OPTIONS --safe --without-K --guardedness #-}

-- `Dp.Settle` at `Dp.Iter`'s loop.
--
-- `Settles-bind` is the junction a closed RUN passes; `iterₚ` is the one a
-- COMPOSITE's step passes, and there no unconditional statement exists — at an
-- arbitrary body the loop never exits, so `iterₚ u w` halts at no budget.  What
-- closes it is a ROUND-TRIP BOUND: a rank on loop points that strictly drops at
-- every re-entry the body's depth-`i` support can produce.  The loop's kernel
-- is then the body's kernel unrolled that many rounds (`loopK`), the round past
-- the last reading as divergence — which is what the machine does too.
--
-- `stepᵢ u x` is `x >>=ₚ contᵢ u` with the exits taken one step earlier
-- (`Dp.Iter.tagᵢ` against `tagₚ`), so both inductions below are `Dp.Settle`'s
-- with `tagᵢ` in place of `tagₚ`, and `iterₚ u w` IS `stepᵢ u (u w)`: the
-- one-turn loop lemma is `Settles-stepᵢ⋆` at `x = u w`, no fixpoint law spent.

open import Data.Bool.Base using (Bool; true; false)
open import Data.Maybe.Base using (nothing)
open import Data.Nat.Base using (ℕ; zero; suc; _+_; _≤_; _<_; s≤s; s≤s⁻¹)
open import Data.Nat.Properties using (m≤n+m; n≤1+n)
  renaming (≤-refl to ≤ℕ-refl; ≤-trans to ≤ℕ-trans)
open import Data.Product.Base using (Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Rational as ℚ using (ℚ)
open import Data.Rational.Properties using (≤-antisym; ≤-reflexive; ≤-trans)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Unit.Base using (⊤; tt)
open import Relation.Binary.PropositionalEquality

open import ProbabilisticLogic.Distribution.RationalDist
open import ProbabilisticLogic.Distribution.RationalDist.Expectation
open import ProbabilisticLogic.Distribution.RationalDist.Partial
open import ProbabilisticLogic.Dp
open import ProbabilisticLogic.Dp.Iter
open import ProbabilisticLogic.Dp.Settle
open import ProbabilisticLogic.Dp.Support

module ProbabilisticLogic.Dp.Settle.Iter where

------------------------------------------------------------------------
-- One turn of the loop

module _ {S A B : Set} where

  -- A loop taken on mass that never lands never lands either.
  Null-stepᵢ : (u : Body S A B) (x : Dₚ (S × (B ⊎ A))) → Null x → Null (stepᵢ u x)
  Null-stepᵢ u x z Q nn i = ≤-antisym
    (≤-trans (stepᵢ-≤-unfold i u x Q nn)
             (≤-reflexive (Null-bind x (contᵢ u) z Q nn (suc i))))
    (cum-nn i (stepᵢ u x) Q nn)

  -- The continuations settle at `suc j` because an exit is a `returnₚ`, whose
  -- reading budget-0 does not yet see.
  mutual
    Halts-stepᵢ : (n j : ℕ) (u : Body S A B) (x : Dₚ (S × (B ⊎ A)))
                  (κ : S × (B ⊎ A) → Dist⊥ (S × B))
                → Halts n x → Supp n x (λ p → Settles (suc j) (contᵢ u p) (κ p))
                → Halts (n + suc j) (stepᵢ u x)
    Halts-stepᵢ zero j u x κ z sp =
      Null⇒Halts (suc j) (stepᵢ u x) (Null-stepᵢ u x z)
    Halts-stepᵢ (suc n) j u x κ (inj₁ z) sp =
      Null⇒Halts (suc n + suc j) (stepᵢ u x) (Null-stepᵢ u x z)
    Halts-stepᵢ (suc n) j u x κ (inj₂ h) (s₁ , s₂) = inj₂ λ where
      true  → HaltsL-stepᵢ n j u (br x true)  κ (h true)  s₁
      false → HaltsL-stepᵢ n j u (br x false) κ (h false) s₂

    HaltsL-stepᵢ : (n j : ℕ) (u : Body S A B) (y : (S × (B ⊎ A)) ⊎ Dₚ (S × (B ⊎ A)))
                   (κ : S × (B ⊎ A) → Dist⊥ (S × B))
                 → HaltsL n y → SuppL n y (λ p → Settles (suc j) (contᵢ u p) (κ p))
                 → HaltsL (n + suc j) (tagᵢ u y)
    HaltsL-stepᵢ n j u (inj₁ (s , inj₁ b)) κ h s′ = tt
    HaltsL-stepᵢ n j u (inj₁ (s , inj₂ p)) κ h s′ =
      Halts-plus n (suc j) (iterₚ u (s , p)) (halts s′)
    HaltsL-stepᵢ n j u (inj₂ x′)           κ h s′ = Halts-stepᵢ n j u x′ κ h s′

  mutual
    cum-stepᵢ : (n j : ℕ) (u : Body S A B) (x : Dₚ (S × (B ⊎ A)))
                (κ : S × (B ⊎ A) → Dist⊥ (S × B)) (Q : S × B → ℚ) → NNF Q
              → Halts n x → Supp n x (λ p → Settles (suc j) (contᵢ u p) (κ p))
              → cum (n + suc j) (stepᵢ u x) Q ≡ cum n x (λ p → E⊥ (κ p) Q)
    cum-stepᵢ zero j u x κ Q nn z sp = Null-stepᵢ u x z Q nn (suc j)
    cum-stepᵢ (suc n) j u x κ Q nn (inj₁ z) sp =
      trans (Null-stepᵢ u x z Q nn (suc n + suc j))
            (sym (z (λ p → E⊥ (κ p) Q) (λ p → E⊥-nn (κ p) Q nn) (suc n)))
    cum-stepᵢ (suc n) j u x κ Q nn (inj₂ h) (s₁ , s₂) =
      cong₂ ℚ._+_
        (cong (wt x true ℚ.*_)  (leafᵢ-stepᵢ n j u (br x true)  κ Q nn (h true)  s₁))
        (cong (wt x false ℚ.*_) (leafᵢ-stepᵢ n j u (br x false) κ Q nn (h false) s₂))

    leafᵢ-stepᵢ : (n j : ℕ) (u : Body S A B) (y : (S × (B ⊎ A)) ⊎ Dₚ (S × (B ⊎ A)))
                  (κ : S × (B ⊎ A) → Dist⊥ (S × B)) (Q : S × B → ℚ) → NNF Q
                → HaltsL n y → SuppL n y (λ p → Settles (suc j) (contᵢ u p) (κ p))
                → leafₚ (n + suc j) (tagᵢ u y) Q ≡ leafₚ n y (λ p → E⊥ (κ p) Q)
    leafᵢ-stepᵢ n j u (inj₁ (s , inj₁ b)) κ Q nn h s′ =
      trans (sym (returnₚ-cum j (s , b) Q)) (Settles-cum s′ nn (suc j) ≤ℕ-refl)
    leafᵢ-stepᵢ n j u (inj₁ (s , inj₂ p)) κ Q nn h s′ =
      Settles-cum s′ nn (n + suc j) (m≤n+m (suc j) n)
    leafᵢ-stepᵢ n j u (inj₂ x′)           κ Q nn h s′ = cum-stepᵢ n j u x′ κ Q nn h s′

  Settles-stepᵢ : (n j : ℕ) (u : Body S A B) (x : Dₚ (S × (B ⊎ A)))
                  (ν : Dist⊥ (S × (B ⊎ A))) (κ : S × (B ⊎ A) → Dist⊥ (S × B))
                → Settles n x ν → Supp n x (λ p → Settles (suc j) (contᵢ u p) (κ p))
                → Settles (n + suc j) (stepᵢ u x) (ν >>=⊥ κ)
  Settles-stepᵢ n j u x ν κ (settles h e) sp =
    settles (Halts-stepᵢ n j u x κ h sp)
            λ Q nn → trans (cum-stepᵢ n j u x κ Q nn h sp)
                           (trans (e (λ p → E⊥ (κ p) Q) (λ p → E⊥-nn (κ p) Q nn))
                                  (sym (E⊥-bind ν κ Q)))

  -- The budgets maxed over the junction's depth-`n` support, which is where
  -- the loop's own budget is still allowed to depend on the exit taken.
  Settles-stepᵢˢ : (n : ℕ) (u : Body S A B) (x : Dₚ (S × (B ⊎ A)))
                   (ν : Dist⊥ (S × (B ⊎ A))) (κ : S × (B ⊎ A) → Dist⊥ (S × B))
                 → Settles n x ν
                 → Supp n x (λ p → Σ[ i ∈ ℕ ] Settles i (contᵢ u p) (κ p))
                 → Σ[ i ∈ ℕ ] Settles i (stepᵢ u x) (ν >>=⊥ κ)
  Settles-stepᵢˢ n u x ν κ s sp =
    let j , sp′ = uniformizeˢ Φ up n x (Supp-map Ψ Φ⋆ bump n x sp)
    in n + suc j , Settles-stepᵢ n j u x ν κ s sp′
    where
    Φ : S × (B ⊎ A) → ℕ → Set
    Φ p i = Settles (suc i) (contᵢ u p) (κ p)

    Ψ Φ⋆ : S × (B ⊎ A) → Set
    Ψ  p = Σ[ i ∈ ℕ ] Settles i (contᵢ u p) (κ p)
    Φ⋆ p = Σ[ i ∈ ℕ ] Φ p i

    up : (p : S × (B ⊎ A)) {i i′ : ℕ} → i ≤ i′ → Φ p i → Φ p i′
    up p le = Settles-mono (s≤s le)

    bump : (p : S × (B ⊎ A)) → Ψ p → Φ⋆ p
    bump p (i , t) = i , Settles-mono (n≤1+n i) t

  Settles-stepᵢ⋆ : (n : ℕ) (u : Body S A B) (x : Dₚ (S × (B ⊎ A)))
                   (ν : Dist⊥ (S × (B ⊎ A))) (κ : S × (B ⊎ A) → Dist⊥ (S × B))
                 → Settles n x ν
                 → ((p : S × (B ⊎ A)) → Σ[ i ∈ ℕ ] Settles i (contᵢ u p) (κ p))
                 → Σ[ i ∈ ℕ ] Settles i (stepᵢ u x) (ν >>=⊥ κ)
  Settles-stepᵢ⋆ n u x ν κ s w =
    Settles-stepᵢˢ n u x ν κ s (Supp-all _ w n x)

------------------------------------------------------------------------
-- The round-trip bound

module Loop {S A B : Set} (u : Body S A B) (Ku : S × A → Dist⊥ (S × (B ⊎ A)))
            (bodyS : (w : S × A) → Σ[ i ∈ ℕ ] Settles i (u w) (Ku w)) where

  -- The body's kernel unrolled `f` rounds.  A loop still running after `f` is
  -- read as divergence, which is what makes `loopK` total and what makes
  -- `Settles-iter` need the rank: without it the reading is simply wrong.
  mutual
    loopK : ℕ → S × A → Dist⊥ (S × B)
    loopK zero    w = return-ℚ nothing
    loopK (suc f) w = Ku w >>=⊥ exitK f

    exitK : ℕ → S × (B ⊎ A) → Dist⊥ (S × B)
    exitK f (s , inj₁ b) = return⊥ (s , b)
    exitK f (s , inj₂ p) = loopK f (s , p)

  module _ (rank : S × A → ℕ) where

    -- What one pass of the body may leave behind: an exit, or a re-entry of
    -- strictly smaller rank.
    Drops : ℕ → S × (B ⊎ A) → Set
    Drops r (_ , inj₁ _) = ⊤
    Drops r (s , inj₂ p) = rank (s , p) < r

    -- The round-trip bound, exactly.  At a two-factor composite `rank` counts
    -- the messages the upper factor has still to bounce off the lower one, and
    -- this is read off its step table.
    Ranked : Set
    Ranked = (w : S × A) (i : ℕ) → Supp i (u w) (Drops (rank w))

    Settles-iter : Ranked → (f : ℕ) (w : S × A) → rank w < f
                 → Σ[ i ∈ ℕ ] Settles i (iterₚ u w) (loopK f w)
    Settles-iter rk (suc f) w lt =
      Settles-stepᵢˢ (proj₁ (bodyS w)) u (u w) (Ku w) (exitK f) (proj₂ (bodyS w))
        (Supp-map (Drops (rank w)) _ serve (proj₁ (bodyS w)) (u w) (rk w _))
      where
      serve : (p : S × (B ⊎ A)) → Drops (rank w) p
            → Σ[ i ∈ ℕ ] Settles i (contᵢ u p) (exitK f p)
      serve (s , inj₁ b) _  = 1 , Settles-return (s , b)
      serve (s , inj₂ p) dr = Settles-iter rk f (s , p) (≤ℕ-trans dr (s≤s⁻¹ lt))
