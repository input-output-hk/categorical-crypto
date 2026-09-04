{-# OPTIONS --safe --without-K --guardedness #-}

-- `Dₚ` is a commutative monad up to `_≈ₚ_`.
--
-- `cum n (d >>=ₚ f) P` is NOT a product of a `cum` of `d` and a `cum` of `f`: the
-- budget is shared between the two factors, so the two orders of a pair are not
-- exactly equal at any fixed budget, only cofinally.  What IS exact is Fubini for
-- two INDEPENDENT budgets (`cum-fubini`), and `Dp`'s bind sandwich converts that
-- into the domination both ways.  `cum-fubini` in turn needs `cum m e` to be a
-- linear functional in its test (`cum-test-+`, `cum-test-*`) — the `Dₚ` analogue of
-- `ProbabilisticLogic.Distribution.RationalDist.lookupᴰℚ-swap` and its linearity
-- family.

open import Data.Bool.Base
open import Data.Nat.Base renaming (_+_ to _+ℕ_)
open import Data.Nat.Properties using (n≤1+n)
open import Data.Product.Base
open import Data.Rational as ℚ
open import Data.Rational.Properties
open import Data.Sum.Base
open import Function.Base
open import Level using (Level)
open import Relation.Binary.PropositionalEquality

open import Algebra.Bundles using (CommutativeMonoid)

-- `Distribution.Linearity` spends the same two rearrangements on the list carrier.
open import Algebra.Properties.CommutativeSemigroup
  (CommutativeMonoid.commutativeSemigroup +-0-commutativeMonoid)
  using () renaming (interchange to +-interchange)
open import Algebra.Properties.CommutativeSemigroup
  (CommutativeMonoid.commutativeSemigroup *-1-commutativeMonoid)
  using (x∙yz≈y∙xz)

open import ProbabilisticLogic.Dp
open import ProbabilisticLogic.Dp.Iter

module ProbabilisticLogic.Dp.Commutative where

private variable
  a : Level
  A B : Set a

------------------------------------------------------------------------
-- The `ℚ` rearrangements the two-branch node needs

private
  node-+ : ∀ w₁ w₂ x₁ y₁ x₂ y₂
         → w₁ ℚ.* (x₁ ℚ.+ y₁) ℚ.+ w₂ ℚ.* (x₂ ℚ.+ y₂)
         ≡ (w₁ ℚ.* x₁ ℚ.+ w₂ ℚ.* x₂) ℚ.+ (w₁ ℚ.* y₁ ℚ.+ w₂ ℚ.* y₂)
  node-+ w₁ w₂ x₁ y₁ x₂ y₂ =
    trans (cong₂ ℚ._+_ (*-distribˡ-+ w₁ x₁ y₁) (*-distribˡ-+ w₂ x₂ y₂))
          (+-interchange (w₁ ℚ.* x₁) (w₁ ℚ.* y₁) (w₂ ℚ.* x₂) (w₂ ℚ.* y₂))

  node-* : ∀ w₁ w₂ c x₁ x₂
         → w₁ ℚ.* (c ℚ.* x₁) ℚ.+ w₂ ℚ.* (c ℚ.* x₂) ≡ c ℚ.* (w₁ ℚ.* x₁ ℚ.+ w₂ ℚ.* x₂)
  node-* w₁ w₂ c x₁ x₂ =
    trans (cong₂ ℚ._+_ (x∙yz≈y∙xz w₁ c x₁) (x∙yz≈y∙xz w₂ c x₂))
          (sym (*-distribˡ-+ c (w₁ ℚ.* x₁) (w₂ ℚ.* x₂)))

------------------------------------------------------------------------
-- `cum n d` is a linear functional in its test

mutual
  cum-test-0 : (n : ℕ) (d : Dₚ A) → cum n d (λ _ → 0ℚ) ≡ 0ℚ
  cum-test-0 zero    d = refl
  cum-test-0 (suc n) d =
    trans (cong₂ ℚ._+_ (cong (wt d true ℚ.*_) (leafₚ-test-0 n (br d true)))
                       (cong (wt d false ℚ.*_) (leafₚ-test-0 n (br d false))))
          (node-zero (wt d true) (wt d false))

  leafₚ-test-0 : (n : ℕ) (x : A ⊎ Dₚ A) → leafₚ n x (λ _ → 0ℚ) ≡ 0ℚ
  leafₚ-test-0 n (inj₁ p)  = refl
  leafₚ-test-0 n (inj₂ d′) = cum-test-0 n d′

mutual
  cum-test-+ : (n : ℕ) (d : Dₚ A) (F G : A → ℚ)
             → cum n d (λ p → F p ℚ.+ G p) ≡ cum n d F ℚ.+ cum n d G
  cum-test-+ zero    d F G = sym (+-identityʳ 0ℚ)
  cum-test-+ (suc n) d F G =
    trans (cong₂ ℚ._+_ (cong (wt d true ℚ.*_) (leafₚ-test-+ n (br d true) F G))
                       (cong (wt d false ℚ.*_) (leafₚ-test-+ n (br d false) F G)))
          (node-+ (wt d true) (wt d false)
                  (leafₚ n (br d true) F) (leafₚ n (br d true) G)
                  (leafₚ n (br d false) F) (leafₚ n (br d false) G))

  leafₚ-test-+ : (n : ℕ) (x : A ⊎ Dₚ A) (F G : A → ℚ)
               → leafₚ n x (λ p → F p ℚ.+ G p) ≡ leafₚ n x F ℚ.+ leafₚ n x G
  leafₚ-test-+ n (inj₁ p)  F G = refl
  leafₚ-test-+ n (inj₂ d′) F G = cum-test-+ n d′ F G

mutual
  cum-test-* : (n : ℕ) (d : Dₚ A) (c : ℚ) (F : A → ℚ) → cum n d (λ p → c ℚ.* F p) ≡ c ℚ.* cum n d F
  cum-test-* zero    d c F = sym (*-zeroʳ c)
  cum-test-* (suc n) d c F =
    trans (cong₂ ℚ._+_ (cong (wt d true ℚ.*_) (leafₚ-test-* n (br d true) c F))
                       (cong (wt d false ℚ.*_) (leafₚ-test-* n (br d false) c F)))
          (node-* (wt d true) (wt d false) c
                  (leafₚ n (br d true) F) (leafₚ n (br d false) F))

  leafₚ-test-* : (n : ℕ) (x : A ⊎ Dₚ A) (c : ℚ) (F : A → ℚ)
               → leafₚ n x (λ p → c ℚ.* F p) ≡ c ℚ.* leafₚ n x F
  leafₚ-test-* n (inj₁ p)  c F = refl
  leafₚ-test-* n (inj₂ d′) c F = cum-test-* n d′ c F

------------------------------------------------------------------------
-- Fubini at two independent budgets — exact

mutual
  cum-fubini : (n m : ℕ) (d : Dₚ A) (e : Dₚ B) (P : A → B → ℚ)
             → cum n d (λ p → cum m e (P p)) ≡ cum m e (λ q → cum n d (λ p → P p q))
  cum-fubini zero    m d e P = sym (cum-test-0 m e)
  cum-fubini (suc n) m d e P =
    trans (cong₂ ℚ._+_ (cong (wt d true ℚ.*_) (leafₚ-fubini n m (br d true) e P))
                       (cong (wt d false ℚ.*_) (leafₚ-fubini n m (br d false) e P)))
          (sym (trans (cum-test-+ m e (λ q → wt d true ℚ.* leafₚ n (br d true) (λ p → P p q))
                                      (λ q → wt d false ℚ.* leafₚ n (br d false) (λ p → P p q)))
                      (cong₂ ℚ._+_
                        (cum-test-* m e (wt d true) (λ q → leafₚ n (br d true) (λ p → P p q)))
                        (cum-test-* m e (wt d false) (λ q → leafₚ n (br d false) (λ p → P p q))))))

  leafₚ-fubini : (n m : ℕ) (x : A ⊎ Dₚ A) (e : Dₚ B) (P : A → B → ℚ)
               → leafₚ n x (λ p → cum m e (P p)) ≡ cum m e (λ q → leafₚ n x (λ p → P p q))
  leafₚ-fubini n m (inj₁ p)  e P = refl
  leafₚ-fubini n m (inj₂ d′) e P = cum-fubini n m d′ e P

------------------------------------------------------------------------
-- Commutativity

mapₚ-≤ : (n : ℕ) (h : A → B) (d : Dₚ A) (P : B → ℚ) → NNF P
       → cum n (mapₚ h d) P ℚ.≤ cum n d (P ∘′ h)
mapₚ-≤ zero    h d P nn = ≤-refl
mapₚ-≤ (suc n) h d P nn =
  ≤-trans (≤-reflexive (mapₚ-cum n h d P)) (cum-mono (n≤1+n n) d (P ∘′ h) λ p → nn (h p))

pairₚ : Dₚ A → Dₚ B → Dₚ (A × B)
pairₚ d e = d >>=ₚ λ p → mapₚ (p ,_) e

pairₚ′ : Dₚ A → Dₚ B → Dₚ (A × B)
pairₚ′ d e = e >>=ₚ λ q → mapₚ (_, q) d

pairₚ-≼ : (d : Dₚ A) (e : Dₚ B) → pairₚ d e ≼ₚ pairₚ′ d e
pairₚ-≼ d e P nn n = n +ℕ suc n ,
  ≤-trans (>>=ₚ-boundA n d (λ p → mapₚ (p ,_) e) P nn)
  (≤-trans (cum-mono-P n d (λ p → cum n (mapₚ (p ,_) e) P) (λ p → cum n e (λ q → P (p , q)))
                       (λ p → mapₚ-≤ n (p ,_) e P nn))
  (≤-trans (≤-reflexive (cum-fubini n n d e (λ p q → P (p , q))))
  (≤-trans (≤-reflexive (cum-cong-P n e (λ q → cum n d (λ p → P (p , q)))
                                        (λ q → cum (suc n) (mapₚ (_, q) d) P)
                                        (λ q → sym (mapₚ-cum n (_, q) d P))))
           (>>=ₚ-boundB n (suc n) e (λ q → mapₚ (_, q) d) P nn))))

pairₚ′-≼ : (d : Dₚ A) (e : Dₚ B) → pairₚ′ d e ≼ₚ pairₚ d e
pairₚ′-≼ d e P nn n = n +ℕ suc n ,
  ≤-trans (>>=ₚ-boundA n e (λ q → mapₚ (_, q) d) P nn)
  (≤-trans (cum-mono-P n e (λ q → cum n (mapₚ (_, q) d) P) (λ q → cum n d (λ p → P (p , q)))
                       (λ q → mapₚ-≤ n (_, q) d P nn))
  (≤-trans (≤-reflexive (sym (cum-fubini n n d e (λ p q → P (p , q)))))
  (≤-trans (≤-reflexive (cum-cong-P n d (λ p → cum n e (λ q → P (p , q)))
                                        (λ p → cum (suc n) (mapₚ (p ,_) e) P)
                                        (λ p → sym (mapₚ-cum n (p ,_) e P))))
           (>>=ₚ-boundB n (suc n) d (λ p → mapₚ (p ,_) e) P nn))))

>>=ₚ-comm : (d : Dₚ A) (e : Dₚ B)
          → (d >>=ₚ λ p → e >>=ₚ λ q → returnₚ (p , q))
          ≈ₚ (e >>=ₚ λ q → d >>=ₚ λ p → returnₚ (p , q))
>>=ₚ-comm d e = pairₚ-≼ d e , pairₚ′-≼ d e
