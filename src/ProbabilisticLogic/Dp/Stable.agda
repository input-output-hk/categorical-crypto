{-# OPTIONS --safe --without-K --guardedness #-}

-- When a `cum` family has stopped moving: `Stable P d u` says every budget past
-- some witness scores `u`.  `Dₚ`'s probability is the supremum of that family,
-- which is never formed (`Dp`'s header); an eventually-constant value is the
-- `cum`-level reading of the same thing, and it is closed under exactly the four
-- ways a run is built — a value, a divergence, a bind junction, a coin node.
--
-- The bound is `n ≤ m` rather than `n + m` so that raising a witness costs
-- nothing; `Stable⇒Σ+` converts once, at the consumer.

open import Data.Bool.Base using (Bool; true; false)
open import Data.Nat.Base
open import Data.Nat.Properties
open import Data.Product.Base
open import Data.Rational as ℚ using (ℚ; 0ℚ)
open import Level using (Level)
open import Relation.Binary.PropositionalEquality

open import ProbabilisticLogic.Distribution.RationalDist
open import ProbabilisticLogic.Distribution.RationalDist.Expectation
open import ProbabilisticLogic.Distribution.Uniform
open import ProbabilisticLogic.Dp
open import ProbabilisticLogic.Dp.Coin

module ProbabilisticLogic.Dp.Stable where

private variable
  a : Level
  A B C : Set a
  P : A → ℚ
  d : Dₚ A
  u : ℚ

Stable : (A → ℚ) → Dₚ A → ℚ → Set
Stable P d u = Σ[ n ∈ ℕ ] ((m : ℕ) → n ≤ m → cum m d P ≡ u)

Stable⇒Σ+ : Stable P d u → Σ[ n ∈ ℕ ] ((m : ℕ) → cum (n + m) d P ≡ u)
Stable⇒Σ+ (n , h) = n , λ m → h (n + m) (m≤m+n n m)

------------------------------------------------------------------------
-- Closure properties

Stable-return : (p : A) (P : A → ℚ) → Stable P (returnₚ p) (P p)
Stable-return p P = 1 , λ where
  zero    ()
  (suc m) _ → returnₚ-cum m p P

Stable-bot : (P : A → ℚ) → Stable P (botₚ {A = A}) 0ℚ
Stable-bot P = 0 , λ m _ → botₚ-cum m P

-- A junction on a divergence diverges: `botₚ >>=ₚ f` is not a `dirac`, but its
-- weights are, so the same two-term arithmetic settles it.
bot-bind-cum : (n : ℕ) (f : A → Dₚ B) (P : B → ℚ) → cum n (botₚ >>=ₚ f) P ≡ 0ℚ
bot-bind-cum zero    f P = refl
bot-bind-cum (suc n) f P =
  trans (node-dirac (cum n (botₚ >>=ₚ f) P) (cum n (botₚ >>=ₚ f) P)) (bot-bind-cum n f P)

Stable-bot-bind : (f : A → Dₚ B) (P : B → ℚ) → Stable P (botₚ >>=ₚ f) 0ℚ
Stable-bot-bind f P = 0 , λ m _ → bot-bind-cum m f P

Stable-bind-return : (p : A) (f : A → Dₚ B) (P : B → ℚ)
                   → Stable P (f p) u → Stable P (returnₚ p >>=ₚ f) u
Stable-bind-return p f P (n , h) = suc n , λ where
  zero    ()
  (suc m) (s≤s le) → trans (>>=ₚ-identityˡ-cum m p f P) (h m le)

Stable-assoc : (d : Dₚ A) (f : A → Dₚ B) (g : B → Dₚ C) (P : C → ℚ)
             → Stable P (d >>=ₚ λ p → f p >>=ₚ g) u → Stable P ((d >>=ₚ f) >>=ₚ g) u
Stable-assoc d f g P (n , h) = n , λ m le → trans (>>=ₚ-assoc-cum m d f g P) (h m le)

-- Same budget as `coinₚ-cum`: the junction consumes the step the branch's
-- `returnₚ` leaf would have.
coin-bind-cum : (μ : Dist-ℚ Bool) (f : Bool → Dₚ A) (n : ℕ) (P : A → ℚ)
              → cum (suc (suc n)) (coinₚ μ >>=ₚ f) P ≡ E μ (λ c → cum n (f c) P)
coin-bind-cum μ f n P =
  trans (cong₂ ℚ._+_ (cong (E μ bool→ℚ ℚ.*_) (>>=ₚ-identityˡ-cum n true f P))
                     (cong (E μ ind˘ ℚ.*_) (>>=ₚ-identityˡ-cum n false f P)))
        (trans (sym (cong₂ ℚ._+_ (cong (E μ bool→ℚ ℚ.*_) (returnₚ-cum n true Q))
                                 (cong (E μ ind˘ ℚ.*_) (returnₚ-cum n false Q))))
               (coinₚ-cum μ n Q))
  where Q : Bool → ℚ
        Q c = cum n (f c) P

Stable-coin : (μ : Dist-ℚ Bool) (f : Bool → Dₚ A) (F : Bool → ℚ) (P : A → ℚ)
            → ((c : Bool) → Stable P (f c) (F c)) → Stable P (coinₚ μ >>=ₚ f) (E μ F)
Stable-coin μ f F P st = suc (suc (n true ⊔ n false)) , go
  where
    n : Bool → ℕ
    n c = proj₁ (st c)

    go : (m : ℕ) → suc (suc (n true ⊔ n false)) ≤ m → cum m (coinₚ μ >>=ₚ f) P ≡ E μ F
    go (suc (suc k)) (s≤s (s≤s le)) =
      trans (coin-bind-cum μ f k P) (lookupᴰℚ-cong-P (entries μ) pt)
      where pt : (c : Bool) → cum k (f c) P ≡ F c
            pt true  = proj₂ (st true) k (≤-trans (m≤m⊔n (n true) (n false)) le)
            pt false = proj₂ (st false) k (≤-trans (m≤n⊔m (n true) (n false)) le)
