{-# OPTIONS --safe --without-K --guardedness #-}

-- A finite rational distribution on `Bool` as a single biased coin.  `Dₚ`'s
-- step is deliberately binary (see its header), so a `Dist-ℚ Bool` — a list of
-- weighted entries, possibly with repeats — enters the delay monad only through
-- its two aggregate masses, which is exactly what `choiceₚ`'s invariants ask
-- for.  `coinₚ-cum` is the agreement: the coin scores every test the
-- distribution does, exactly, at any budget past the two branch steps.

open import Data.Bool.Base
open import Data.Nat.Base
open import Data.Product.Base using (_,_)
open import Data.Rational as ℚ
open import Data.Rational.Properties as ℚP
open import Data.Rational.Properties.Ext
open import Function.Base using (_∘′_)
open import Level using (Level)
open import Relation.Binary.PropositionalEquality

open import ProbabilisticLogic.Distribution.RationalDist

open import ProbabilisticLogic.Distribution.RationalDist.Expectation
open import ProbabilisticLogic.Distribution.Uniform
open import ProbabilisticLogic.Dp

module ProbabilisticLogic.Dp.Coin where

private variable a : Level
                 A : Set a
                 P : Bool → ℚ

-- The indicator of `false`; `bool→ℚ` is the indicator of `true`.
ind˘ : Bool → ℚ
ind˘ b = bool→ℚ (not b)

private
  0≤ind : ∀ b → 0ℚ ℚ.≤ bool→ℚ b
  0≤ind true  = 0≤1ℚ
  0≤ind false = ≤-refl

  0≤E : (μ : Dist-ℚ Bool) → (∀ b → 0ℚ ℚ.≤ P b) → 0ℚ ℚ.≤ E μ P
  0≤E {P} μ nn = ≤-trans (≤-reflexive (sym (E-const μ 0ℚ))) (E-mono μ (λ _ → 0ℚ) P nn)

  -- The two masses add to one because the two indicators do, pointwise.
  masses-1 : (μ : Dist-ℚ Bool) → E μ bool→ℚ ℚ.+ E μ ind˘ ≡ 1ℚ
  masses-1 μ = trans (sym (lookupᴰℚ-+ (entries μ) bool→ℚ ind˘))
                     (trans (lookupᴰℚ-cong-P (entries μ) sum-1) (E-const μ 1ℚ))
    where sum-1 : ∀ b → bool→ℚ b ℚ.+ ind˘ b ≡ 1ℚ
          sum-1 true  = refl
          sum-1 false = refl

coinₚ : Dist-ℚ Bool → Dₚ Bool
coinₚ μ = choiceₚ (E μ bool→ℚ) (E μ ind˘)
                  (0≤E μ 0≤ind) (0≤E μ (λ b → 0≤ind (not b)))
                  (masses-1 μ) (returnₚ true) (returnₚ false)

-- Both branches spend one delay step, so the budget is `suc (suc n)`.
coinₚ-cum : (μ : Dist-ℚ Bool) (n : ℕ) (P : Bool → ℚ)
          → cum (suc (suc n)) (coinₚ μ) P ≡ E μ P
coinₚ-cum μ n P = trans branches (trans (cong₂ ℚ._+_ (pull bool→ℚ _) (pull ind˘ _))
                                        (trans (sym (lookupᴰℚ-+ (entries μ) _ _))
                                               (lookupᴰℚ-cong-P (entries μ) split)))
  where
    branches : cum (suc (suc n)) (coinₚ μ) P
             ≡ E μ bool→ℚ ℚ.* P true ℚ.+ E μ ind˘ ℚ.* P false
    branches = cong₂ ℚ._+_ (cong (E μ bool→ℚ ℚ.*_) (returnₚ-cum n true P))
                           (cong (E μ ind˘ ℚ.*_) (returnₚ-cum n false P))

    pull : (Q : Bool → ℚ) (x : ℚ)
         → E μ Q ℚ.* x ≡ lookupᴰℚ (entries μ) (λ b → Q b ℚ.* x)
    pull Q x = trans (ℚP.*-comm (E μ Q) x)
                     (trans (sym (lookupᴰℚ-*ₗ x (entries μ) Q))
                            (lookupᴰℚ-cong-P (entries μ) (λ b → ℚP.*-comm x (Q b))))

    split : ∀ b → bool→ℚ b ℚ.* P true ℚ.+ ind˘ b ℚ.* P false ≡ P b
    split true  = trans (cong₂ ℚ._+_ (ℚP.*-identityˡ (P true)) (ℚP.*-zeroˡ (P false)))
                        (ℚP.+-identityʳ (P true))
    split false = trans (cong₂ ℚ._+_ (ℚP.*-zeroˡ (P true)) (ℚP.*-identityˡ (P false)))
                        (ℚP.+-identityˡ (P false))

------------------------------------------------------------------------
-- A balanced coin is blind to a flip

private
  -- `cum` reads a coin's bind as a two-term sum whose factors are the two
  -- masses; equal masses is exactly what lets the terms be transposed.
  branch : (μ : Dist-ℚ Bool) (h : Bool → Dₚ A) (Q : A → ℚ) (n : ℕ)
         → cum (suc (suc n)) (coinₚ μ >>=ₚ h) Q
           ≡ E μ bool→ℚ ℚ.* cum n (h true) Q ℚ.+ E μ ind˘ ℚ.* cum n (h false) Q
  branch μ h Q n =
    cong₂ ℚ._+_ (cong (E μ bool→ℚ ℚ.*_) (>>=ₚ-identityˡ-cum n true h Q))
                (cong (E μ ind˘ ℚ.*_) (>>=ₚ-identityˡ-cum n false h Q))

  transpose : {w₁ w₂ : ℚ} → w₁ ≡ w₂ → (x y : ℚ)
            → w₁ ℚ.* x ℚ.+ w₂ ℚ.* y ≡ w₁ ℚ.* y ℚ.+ w₂ ℚ.* x
  transpose {w₁} refl x y = ℚP.+-comm (w₁ ℚ.* x) (w₁ ℚ.* y)

coin-not : (μ : Dist-ℚ Bool) → E μ bool→ℚ ≡ E μ ind˘ → (f : Bool → Dₚ A)
         → (coinₚ μ >>=ₚ (f ∘′ not)) ≈ₚ (coinₚ μ >>=ₚ f)
coin-not {A = A} μ eq f = exact⇒≈ₚ _ _ agree
  where
  agree : (Q : A → ℚ) (n : ℕ)
        → cum n (coinₚ μ >>=ₚ (f ∘′ not)) Q ≡ cum n (coinₚ μ >>=ₚ f) Q
  agree Q zero          = refl
  agree Q (suc zero)    = trans (cum-1-bind (coinₚ μ) (f ∘′ not) Q)
                                (sym (cum-1-bind (coinₚ μ) f Q))
  agree Q (suc (suc n)) = trans (branch μ (f ∘′ not) Q n)
                                (trans (transpose eq (cum n (f false) Q) (cum n (f true) Q))
                                       (sym (branch μ f Q n)))

-- …so its two branch functions need only agree AFTER the flip.  This is the
-- one-time pad in the delay monad: a uniform bit masked by a fixed one is the
-- same distribution, but reindexed, and `_≈ₚ_` compares masses rather than
-- branches, so the reindexing is invisible.
coin-flip : (μ : Dist-ℚ Bool) → E μ bool→ℚ ≡ E μ ind˘ → {f g : Bool → Dₚ A}
          → ((x : Bool) → f x ≈ₚ g (not x))
          → (coinₚ μ >>=ₚ f) ≈ₚ (coinₚ μ >>=ₚ g)
coin-flip μ eq {f} {g} h =
  ≈ₚ-trans _ _ _ (>>=ₚ-cong (coinₚ μ) (coinₚ μ) f (g ∘′ not) (≈ₚ-refl _) h)
                 (coin-not μ eq g)

uniform-balanced : E uniform-Bool bool→ℚ ≡ E uniform-Bool ind˘
uniform-balanced = refl

------------------------------------------------------------------------
-- A coin is affine

private
  -- The two branch masses sum to one, so a continuation that ignores the draw
  -- is scored by the coin exactly as it is on its own — two steps later.
  const-cum : (μ : Dist-ℚ Bool) (e : Dₚ A) (Q : A → ℚ) (n : ℕ)
            → cum (suc (suc n)) (coinₚ μ >>=ₚ (λ _ → e)) Q ≡ cum n e Q
  const-cum μ e Q n =
    trans (branch μ (λ _ → e) Q n)
          (trans (sym (ℚP.*-distribʳ-+ (cum n e Q) (E μ bool→ℚ) (E μ ind˘)))
                 (trans (cong (ℚ._* cum n e Q) (masses-1 μ))
                        (ℚP.*-identityˡ (cum n e Q))))

-- `Dₚ` has divergence, so binding away a draw is not free in general — `botₚ`
-- annihilates every continuation.  A coin terminates with total mass one, and
-- for it the equation holds: this is what lets a deferred draw be introduced
-- where nothing reads it (`CategoricalCrypto.GamePlaying.Defer.Run`).
coinₚ-const : (μ : Dist-ℚ Bool) (e : Dₚ A) → (coinₚ μ >>=ₚ (λ _ → e)) ≈ₚ e
coinₚ-const μ e = below , above
  where
  below : (coinₚ μ >>=ₚ (λ _ → e)) ≼ₚ e
  below Q nn zero          = 0 , ℚP.≤-refl
  below Q nn (suc zero)    = 0 , ℚP.≤-reflexive (cum-1-bind (coinₚ μ) (λ _ → e) Q)
  below Q nn (suc (suc n)) = n , ℚP.≤-reflexive (const-cum μ e Q n)

  above : e ≼ₚ (coinₚ μ >>=ₚ (λ _ → e))
  above Q nn n = suc (suc n) , ℚP.≤-reflexive (sym (const-cum μ e Q n))
