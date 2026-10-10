{-# OPTIONS --safe --without-K --guardedness #-}

-- `attach d p` is `d` with the support proof `p` attached at every leaf: same
-- weights and shape, so `mapₚ proj₁` recovers `d` (`attach-proj`).  A fact
-- assumed only on the support is total on `Σ A P`, where the total bind
-- congruence applies (`>>=ₚ-congˢ`).  The detour lets the hypothesis live at
-- any level; `uniformizeˢ` would need it in `Set`.

open import Data.Bool.Base
open import Data.Nat.Base
open import Data.Product.Base
open import Data.Rational as ℚ
open import Data.Sum.Base
open import Function.Base
open import Level using (Level)
open import Relation.Binary.PropositionalEquality

open import ProbabilisticLogic.Dp
open import ProbabilisticLogic.Dp.Reasoning

module ProbabilisticLogic.Dp.Attach where

private variable
  a b c : Level
  A : Set a
  B : Set b
  P : A → Set c

mutual
  attach : (d : Dₚ A) → (∀ n → Supp n d P) → Dₚ (Σ A P)
  wt    (attach d p)       = wt d
  wt-nn (attach d p)       = wt-nn d
  wt-1  (attach d p)       = wt-1 d
  br    (attach d p) true  = attachL (br d true)  λ n → proj₁ (p (suc n))
  br    (attach d p) false = attachL (br d false) λ n → proj₂ (p (suc n))

  attachL : (x : A ⊎ Dₚ A) → (∀ n → SuppL n x P) → Σ A P ⊎ Dₚ (Σ A P)
  attachL (inj₁ y)  p = inj₁ (y , p 0)
  attachL (inj₂ d′) p = inj₂ (attach d′ p)

mutual
  attach-cum : (n : ℕ) (d : Dₚ A) (p : ∀ i → Supp i d P) (Q : A → ℚ)
             → cum n (attach d p) (Q ∘′ proj₁) ≡ cum n d Q
  attach-cum zero    d p Q = refl
  attach-cum (suc n) d p Q =
    cong₂ ℚ._+_ (cong (wt d true ℚ.*_) (attachL-cum n (br d true) (λ i → proj₁ (p (suc i))) Q))
                (cong (wt d false ℚ.*_) (attachL-cum n (br d false) (λ i → proj₂ (p (suc i))) Q))

  attachL-cum : (n : ℕ) (x : A ⊎ Dₚ A) (p : ∀ i → SuppL i x P) (Q : A → ℚ)
              → leafₚ n (attachL x p) (Q ∘′ proj₁) ≡ leafₚ n x Q
  attachL-cum n (inj₁ y)  p Q = refl
  attachL-cum n (inj₂ d′) p Q = attach-cum n d′ p Q

attach-proj : (d : Dₚ A) (p : ∀ n → Supp n d P) → mapₚ proj₁ (attach d p) ≈ₚ d
attach-proj d p = shift⇒≈ₚ (mapₚ proj₁ (attach d p)) d λ Q n →
  trans (mapₚ-cum n proj₁ (attach d p) Q) (attach-cum n d p Q)

>>=ₚ-attach : (d : Dₚ A) (p : ∀ n → Supp n d P) (f : A → Dₚ B)
            → (d >>=ₚ f) ≈ₚ (attach d p >>=ₚ f ∘′ proj₁)
>>=ₚ-attach d p f = bindˣ (≈sym (attach-proj d p)) ⟨≈⟩ bind-map (attach d p) proj₁ f

>>=ₚ-congˢᵖ : (d : Dₚ A) (f g : A → Dₚ B) → (∀ n → Supp n d (λ x → f x ≼ₚ g x))
            → (d >>=ₚ f) ≼ₚ (d >>=ₚ g)
>>=ₚ-congˢᵖ d f g p =
  ≼ₚ-trans (d >>=ₚ f) (e >>=ₚ f ∘′ proj₁) (d >>=ₚ g) (proj₁ (>>=ₚ-attach d p f))
    (≼ₚ-trans (e >>=ₚ f ∘′ proj₁) (e >>=ₚ g ∘′ proj₁) (d >>=ₚ g)
      (>>=ₚ-congᵖ e e (f ∘′ proj₁) (g ∘′ proj₁) (≼ₚ-refl e) proj₂) (proj₂ (>>=ₚ-attach d p g)))
  where e = attach d p

>>=ₚ-congˢ : (d : Dₚ A) (f g : A → Dₚ B) → (∀ n → Supp n d (λ x → f x ≈ₚ g x))
           → (d >>=ₚ f) ≈ₚ (d >>=ₚ g)
>>=ₚ-congˢ d f g p =
    >>=ₚ-congˢᵖ d f g (λ n → Supp-map _ _ (λ _ → proj₁) n d (p n))
  , >>=ₚ-congˢᵖ d g f (λ n → Supp-map _ _ (λ _ → proj₂) n d (p n))
