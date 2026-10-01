{-# OPTIONS --safe --without-K --guardedness #-}

-- A `Dist-ℚ Bool` as one biased coin: its entries may repeat, so it enters `Dₚ`
-- through its two aggregate masses.

open import Data.Bool.Base
open import Data.Nat.Base
open import Data.Product.Base
open import Data.Rational as ℚ
open import Data.Rational.Properties as ℚP
open import Data.Rational.Properties.Ext
open import Data.Vec.Base as Vec using (Vec)
open import Function.Base
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

private
  masses-1 : (μ : Dist-ℚ Bool) → E μ bool→ℚ ℚ.+ E μ (indᵇ false) ≡ 1ℚ
  masses-1 μ = trans (sym (lookupᴰℚ-+ (entries μ) bool→ℚ (indᵇ false)))
                     (trans (lookupᴰℚ-cong-P (entries μ) sum-1) (E-const μ 1ℚ))
    where sum-1 : ∀ b → bool→ℚ b ℚ.+ indᵇ false b ≡ 1ℚ
          sum-1 true  = refl
          sum-1 false = refl

coinₚ : Dist-ℚ Bool → Dₚ Bool
coinₚ μ = choiceₚ (E μ bool→ℚ) (E μ (indᵇ false))
                  (E-nn μ _ 0≤bool) (E-nn μ _ (indᵇ-nn false))
                  (masses-1 μ) (returnₚ true) (returnₚ false)

-- Both branches spend one delay step, so the budget is `suc (suc n)`.
coinₚ-cum : (μ : Dist-ℚ Bool) (n : ℕ) (P : Bool → ℚ) → cum (suc (suc n)) (coinₚ μ) P ≡ E μ P
coinₚ-cum μ n P = trans branches (trans (cong₂ ℚ._+_ (pull bool→ℚ _) (pull (indᵇ false) _))
                                        (trans (sym (lookupᴰℚ-+ (entries μ) _ _))
                                               (lookupᴰℚ-cong-P (entries μ) split)))
  where
    branches : cum (suc (suc n)) (coinₚ μ) P
             ≡ E μ bool→ℚ ℚ.* P true ℚ.+ E μ (indᵇ false) ℚ.* P false
    branches = cong₂ ℚ._+_ (cong (E μ bool→ℚ ℚ.*_) (returnₚ-cum n true P))
                           (cong (E μ (indᵇ false) ℚ.*_) (returnₚ-cum n false P))

    pull : (Q : Bool → ℚ) (x : ℚ) → E μ Q ℚ.* x ≡ lookupᴰℚ (entries μ) (λ b → Q b ℚ.* x)
    pull Q x = trans (ℚP.*-comm (E μ Q) x)
                     (trans (sym (lookupᴰℚ-*ₗ x (entries μ) Q))
                            (lookupᴰℚ-cong-P (entries μ) (λ b → ℚP.*-comm x (Q b))))

    split : ∀ b → bool→ℚ b ℚ.* P true ℚ.+ indᵇ false b ℚ.* P false ≡ P b
    split true  = trans (cong₂ ℚ._+_ (ℚP.*-identityˡ (P true)) (ℚP.*-zeroˡ (P false)))
                        (ℚP.+-identityʳ (P true))
    split false = trans (cong₂ ℚ._+_ (ℚP.*-zeroˡ (P true)) (ℚP.*-identityˡ (P false)))
                        (ℚP.+-identityˡ (P false))

------------------------------------------------------------------------
-- A balanced coin is blind to a flip

private
  branch : (μ : Dist-ℚ Bool) (h : Bool → Dₚ A) (Q : A → ℚ) (n : ℕ)
         → cum (suc (suc n)) (coinₚ μ >>=ₚ h) Q
           ≡ E μ bool→ℚ ℚ.* cum n (h true) Q ℚ.+ E μ (indᵇ false) ℚ.* cum n (h false) Q
  branch μ h Q n =
    cong₂ ℚ._+_ (cong (E μ bool→ℚ ℚ.*_) (>>=ₚ-identityˡ-cum n true h Q))
                (cong (E μ (indᵇ false) ℚ.*_) (>>=ₚ-identityˡ-cum n false h Q))

  transpose : {w₁ w₂ : ℚ} → w₁ ≡ w₂ → (x y : ℚ)
            → w₁ ℚ.* x ℚ.+ w₂ ℚ.* y ≡ w₁ ℚ.* y ℚ.+ w₂ ℚ.* x
  transpose {w₁} refl x y = ℚP.+-comm (w₁ ℚ.* x) (w₁ ℚ.* y)

-- Same budget as `coinₚ-cum`: the junction consumes the step the branch's
-- `returnₚ` leaf would have.
coin-bind-cum : (μ : Dist-ℚ Bool) (f : Bool → Dₚ A) (n : ℕ) (P : A → ℚ)
              → cum (suc (suc n)) (coinₚ μ >>=ₚ f) P ≡ E μ (λ c → cum n (f c) P)
coin-bind-cum μ f n P =
  trans (branch μ f P n)
        (trans (sym (cong₂ ℚ._+_ (cong (E μ bool→ℚ ℚ.*_) (returnₚ-cum n true Q))
                                 (cong (E μ (indᵇ false) ℚ.*_) (returnₚ-cum n false Q))))
               (coinₚ-cum μ n Q))
  where Q : Bool → ℚ
        Q c = cum n (f c) P

coin-not : (μ : Dist-ℚ Bool) → E μ bool→ℚ ≡ E μ (indᵇ false) → (f : Bool → Dₚ A)
         → (coinₚ μ >>=ₚ (f ∘′ not)) ≈ₚ (coinₚ μ >>=ₚ f)
coin-not {A = A} μ eq f = exact⇒≈ₚ _ _ agree
  where
  agree : (Q : A → ℚ) (n : ℕ) → cum n (coinₚ μ >>=ₚ (f ∘′ not)) Q ≡ cum n (coinₚ μ >>=ₚ f) Q
  agree Q zero          = refl
  agree Q (suc zero)    = trans (cum-1-bind (coinₚ μ) (f ∘′ not) Q)
                                (sym (cum-1-bind (coinₚ μ) f Q))
  agree Q (suc (suc n)) = trans (branch μ (f ∘′ not) Q n)
                                (trans (transpose eq (cum n (f false) Q) (cum n (f true) Q))
                                       (sym (branch μ f Q n)))

-- The one-time pad in `Dₚ`: under a balanced coin the branches need only agree
-- after the flip.
coin-flip : (μ : Dist-ℚ Bool) → E μ bool→ℚ ≡ E μ (indᵇ false) → {f g : Bool → Dₚ A}
          → ((x : Bool) → f x ≈ₚ g (not x))
          → (coinₚ μ >>=ₚ f) ≈ₚ (coinₚ μ >>=ₚ g)
coin-flip μ eq {f} {g} h =
  ≈ₚ-trans _ _ _ (>>=ₚ-cong (coinₚ μ) (coinₚ μ) f (g ∘′ not) (≈ₚ-refl _) h)
                 (coin-not μ eq g)

uniform-balanced : E uniform-Bool bool→ℚ ≡ E uniform-Bool (indᵇ false)
uniform-balanced = refl

------------------------------------------------------------------------
-- A coin is affine

private
  const-cum : (μ : Dist-ℚ Bool) (e : Dₚ A) (Q : A → ℚ) (n : ℕ)
            → cum (suc (suc n)) (coinₚ μ >>=ₚ (λ _ → e)) Q ≡ cum n e Q
  const-cum μ e Q n =
    trans (branch μ (λ _ → e) Q n)
          (trans (sym (ℚP.*-distribʳ-+ (cum n e Q) (E μ bool→ℚ) (E μ (indᵇ false))))
                 (trans (cong (ℚ._* cum n e Q) (masses-1 μ))
                        (ℚP.*-identityˡ (cum n e Q))))

-- Not true of every `d` (`botₚ` annihilates any continuation), but a coin has
-- total mass one.
coinₚ-const : (μ : Dist-ℚ Bool) (e : Dₚ A) → (coinₚ μ >>=ₚ (λ _ → e)) ≈ₚ e
coinₚ-const μ e = below , above
  where
  below : (coinₚ μ >>=ₚ (λ _ → e)) ≼ₚ e
  below Q nn zero          = 0 , ℚP.≤-refl
  below Q nn (suc zero)    = 0 , ℚP.≤-reflexive (cum-1-bind (coinₚ μ) (λ _ → e) Q)
  below Q nn (suc (suc n)) = n , ℚP.≤-reflexive (const-cum μ e Q n)

  above : e ≼ₚ (coinₚ μ >>=ₚ (λ _ → e))
  above Q nn n = suc (suc n) , ℚP.≤-reflexive (sym (const-cum μ e Q n))

-- `Protocol.uniformVec`'s cascade in `Dₚ`: one fair coin per bit.
uniformₚ : (n : ℕ) → Dₚ (Vec Bool n)
uniformₚ zero    = returnₚ Vec.[]
uniformₚ (suc n) = coinₚ uniform-Bool >>=ₚ λ b → mapₚ (b Vec.∷_) (uniformₚ n)
