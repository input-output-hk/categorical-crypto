{-# OPTIONS --safe --without-K --guardedness #-}

-- Divergence as a `cum`-level predicate.
--
-- `d ≈ₚ botₚ` says the two mass families dominate each other cofinally;
-- `Zero d` says every budgeted mass is exactly `0ℚ`.  The two are equivalent
-- (`zero⇒≈bot`/`≈bot⇒zero`, by antisymmetry against `cum-nn`), and `Zero` is
-- the form a PROPAGATION argument wants: closure under `_>>=ₚ_` in the
-- CONTINUATION (`bind-zero`) is an induction on the budget, which the cofinal
-- form has no way to state.

open import Data.Bool.Base using (true; false)
open import Data.Nat.Base using (ℕ; suc)
open import Data.Product.Base using (_,_)
open import Data.Rational as ℚ using (ℚ; 0ℚ)
open import Data.Rational.Properties using (≤-antisym; ≤-reflexive; ≤-trans)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Level using (Level)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂)

open import ProbabilisticLogic.Dp

module ProbabilisticLogic.Dp.Zero where

private variable a b : Level
                 A : Set a
                 B : Set b

Zero : {A : Set a} → Dₚ A → Set a
Zero {A = A} d = (P : A → ℚ) → NNF P → (n : ℕ) → cum n d P ≡ 0ℚ

zero-botₚ : Zero (botₚ {A = A})
zero-botₚ P nn n = botₚ-cum n P

zero⇒≈bot : {d : Dₚ A} → Zero d → d ≈ₚ botₚ
zero⇒≈bot {d = d} z =
    (λ P nn n → 0 , ≤-reflexive (trans (z P nn n) (sym (botₚ-cum 0 P))))
  , λ P nn n → n , ≤-trans (≤-reflexive (botₚ-cum n P)) (cum-nn n d P nn)

≈bot⇒zero : {d : Dₚ A} → d ≈ₚ botₚ → Zero d
≈bot⇒zero {d = d} (le , _) P nn n =
  let m , bd = le P nn n
  in ≤-antisym (≤-trans bd (≤-reflexive (botₚ-cum m P))) (cum-nn n d P nn)

zero-resp-≈ₚ : {d e : Dₚ A} → d ≈ₚ e → Zero d → Zero e
zero-resp-≈ₚ {d = d} {e} de z =
  ≈bot⇒zero (≈ₚ-trans e d botₚ (≈ₚ-sym d e de) (zero⇒≈bot z))

-- Divergence at the head swallows the continuation.
zero-bindˡ : {d : Dₚ A} (k : A → Dₚ B) → Zero d → Zero (d >>=ₚ k)
zero-bindˡ {d = d} k z = ≈bot⇒zero
  (≈ₚ-trans (d >>=ₚ k) (botₚ >>=ₚ k) botₚ
            (>>=ₚ-cong d botₚ k k (zero⇒≈bot z) (λ a → ≈ₚ-refl (k a)))
            (bot-bind-≈ₚ k))

-- …and divergence at every leaf is divergence of the whole, which is the
-- direction that needs the budget induction.
mutual
  bind-zero : (d : Dₚ A) {k : A → Dₚ B} → ((p : A) → Zero (k p)) → Zero (d >>=ₚ k)
  bind-zero d z P nn 0       = refl
  bind-zero d z P nn (suc n) =
    trans (cong₂ ℚ._+_ (cong (wt d true ℚ.*_) (leaf-zero n (br d true) z P nn))
                       (cong (wt d false ℚ.*_) (leaf-zero n (br d false) z P nn)))
          (node-zero (wt d true) (wt d false))

  leaf-zero : (n : ℕ) (x : A ⊎ Dₚ A) {k : A → Dₚ B} → ((p : A) → Zero (k p))
            → (P : B → ℚ) → NNF P → leafₚ n (tagₚ x k) P ≡ 0ℚ
  leaf-zero n (inj₁ p)  z P nn = z p P nn n
  leaf-zero n (inj₂ d′) z P nn = bind-zero d′ z P nn n
