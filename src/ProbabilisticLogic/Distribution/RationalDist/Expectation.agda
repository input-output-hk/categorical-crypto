{-# OPTIONS --safe --without-K #-}

-- Expectation of a ℚ-valued observable under a `Dist-ℚ`, the probability of
-- `true`, and their algebra.  Everything here is proven EXCEPT monotonicity,
-- which is not a theorem of this carrier: `Dist-ℚ`'s only invariant is
-- mass ≡ 1, so weights are unconstrained in sign and `E-Mono-On` is in fact
-- refutable for `Dist-ℚ` as it stands.  It is therefore stated as a named
-- hypothesis (`module Monotone`) rather than assumed: fixing it means adding a
-- non-negativity invariant to `Dist-ℚ`, which is this layer's business, not its
-- consumers'.

open import categorical-crypto.Prelude hiding (_>>=_; _*_; _/_)

open import Data.List.NonEmpty as NE using ()
open import Data.List.Relation.Unary.All as ListAll using ()
open import Data.Rational using (ℚ; 0ℚ; 1ℚ)
  renaming (_*_ to _*ℚ_; _+_ to _+ℚ_; _-_ to _-ℚ_; -_ to -ℚ_; ∣_∣ to ∣_∣ℚ; _≤_ to _≤ℚ_)
open import Data.Rational.Properties using
  (≤-refl; ≤-reflexive; ≤-trans; *-identityˡ; ∣-p∣≡∣p∣)
open import Data.Rational.Properties.Ext

open import ProbabilisticLogic.Distribution.RationalDist
open import ProbabilisticLogic.Distribution.RationalDist.Partial
open import ProbabilisticLogic.Distribution.Uniform using (bool→ℚ)

module ProbabilisticLogic.Distribution.RationalDist.Expectation where

private variable A B : Type

-- Expectation (= `lookupᴰℚ` over the entries) and the probability of `true`.
E : Dist-ℚ A → (A → ℚ) → ℚ
E μ f = lookupᴰℚ (entries μ) f

Pr₁ : Dist-ℚ Bool → ℚ
Pr₁ μ = E μ bool→ℚ

------------------------------------------------------------------------
-- The expectation algebra

E-add : (μ : Dist-ℚ A) (f g : A → ℚ) → E μ (λ a → f a +ℚ g a) ≡ E μ f +ℚ E μ g
E-add μ = lookupᴰℚ-+ (entries μ)

E-const : (μ : Dist-ℚ A) (c : ℚ) → E μ (λ _ → c) ≡ c
E-const μ c = trans (mass-as-const (entries μ) c)
                    (trans (cong (_*ℚ c) (mass-1 μ)) (*-identityˡ c))

E-sub : (μ : Dist-ℚ A) (a b : A → ℚ) → E μ (λ x → a x -ℚ b x) ≡ E μ a -ℚ E μ b
E-sub μ a b = trans (sym (+-−-cancel (E μ (λ x → a x -ℚ b x)) (E μ b)))
                    (cong (_-ℚ E μ b) eq)
  where eq : E μ (λ x → a x -ℚ b x) +ℚ E μ b ≡ E μ a
        eq = trans (sym (E-add μ (λ x → a x -ℚ b x) b))
                   (lookupᴰℚ-cong-P (entries μ) (λ x → −-+-cancel (a x) (b x)))

E-bind : (μ : Dist-ℚ A) (h : A → Dist-ℚ B) (P : B → ℚ)
       → E (μ >>=ᴹ h) P ≡ E μ (λ a → E (h a) P)
E-bind μ h P = lookupᴰℚ-bind (entries μ) (λ a → entries (h a)) P

Pr₁-bind : (μ : Dist-ℚ A) (k : A → Dist-ℚ Bool) → Pr₁ (μ >>=ᴹ k) ≡ E μ (λ a → Pr₁ (k a))
Pr₁-bind μ k = lookupᴰℚ-bind (entries μ) (λ a → entries (k a)) bool→ℚ

0≤bool : ∀ b → 0ℚ ≤ℚ bool→ℚ b
0≤bool true  = 0≤1ℚ
0≤bool false = ≤-refl

------------------------------------------------------------------------
-- The partial (`Dist⊥`) reading: the divergence sink `nothing` scores `0`.

mb : Maybe Bool → ℚ
mb (just b) = bool→ℚ b
mb nothing  = 0ℚ

Pr₁⊥ : Dist⊥ Bool → ℚ
Pr₁⊥ μ = E μ mb

Pr₁⊥-just : (μ : Dist-ℚ Bool) → Pr₁⊥ (Dmap just μ) ≡ Pr₁ μ
Pr₁⊥-just μ = lookupᴰℚ-Dmap just μ mb

Pr₁⊥-cong : (μ ν : Dist⊥ Bool) → μ ≈Mℚ ν → Pr₁⊥ μ ≡ Pr₁⊥ ν
Pr₁⊥-cong μ ν μ≈ν = μ≈ν mb

------------------------------------------------------------------------
-- Monotonicity, and what it buys
--
-- `E-Mono-On` is the support-level statement; global monotonicity, the
-- [0,1]-boundedness of `Pr₁` and the expectation triangle inequality all follow
-- from it and nothing else.

E-Mono-On : Type₁
E-Mono-On = ∀ {A : Type} (μ : Dist-ℚ A) (f g : A → ℚ)
          → OnSupport (λ a → f a ≤ℚ g a) μ → E μ f ≤ℚ E μ g

module Monotone (E-mono-on : E-Mono-On) where

  E-mono : (μ : Dist-ℚ A) (f g : A → ℚ) → (∀ a → f a ≤ℚ g a) → E μ f ≤ℚ E μ g
  E-mono μ f g pt = E-mono-on μ f g
    (ListAll.universal (λ e → pt (proj₂ e)) (NE.toList (entries μ)))

  Pr₁≤1 : (μ : Dist-ℚ Bool) → Pr₁ μ ≤ℚ 1ℚ
  Pr₁≤1 μ = ≤-trans (E-mono μ bool→ℚ (λ _ → 1ℚ) b≤1) (≤-reflexive (E-const μ 1ℚ))
    where b≤1 : ∀ b → bool→ℚ b ≤ℚ 1ℚ
          b≤1 true  = ≤-refl
          b≤1 false = 0≤1ℚ

  Pr₁≥0 : (μ : Dist-ℚ Bool) → 0ℚ ≤ℚ Pr₁ μ
  Pr₁≥0 μ = ≤-trans (≤-reflexive (sym (E-const μ 0ℚ))) (E-mono μ (λ _ → 0ℚ) bool→ℚ 0≤bool)

  -- expectation triangle inequality:  ∣E a − E b∣ ≤ E ∣a − b∣
  E-abs-diff : (μ : Dist-ℚ A) (a b : A → ℚ)
             → ∣ E μ a -ℚ E μ b ∣ℚ ≤ℚ E μ (λ x → ∣ a x -ℚ b x ∣ℚ)
  E-abs-diff μ a b = ∣∣≤ upper lower
    where
      H = λ x → ∣ a x -ℚ b x ∣ℚ
      upper : (E μ a -ℚ E μ b) ≤ℚ E μ H
      upper = subst (_≤ℚ E μ H) (E-sub μ a b)
                    (E-mono μ (λ x → a x -ℚ b x) H (λ x → p≤∣p∣ (a x -ℚ b x)))
      lower : (-ℚ (E μ a -ℚ E μ b)) ≤ℚ E μ H
      lower = subst (_≤ℚ E μ H) negEq (E-mono μ (λ x → b x -ℚ a x) H bnd)
        where
          negEq : E μ (λ x → b x -ℚ a x) ≡ -ℚ (E μ a -ℚ E μ b)
          negEq = trans (E-sub μ b a) (neg-sub (E μ b) (E μ a))
          bnd : ∀ x → (b x -ℚ a x) ≤ℚ H x
          bnd x = subst ((b x -ℚ a x) ≤ℚ_) absEq (p≤∣p∣ (b x -ℚ a x))
            where absEq : ∣ b x -ℚ a x ∣ℚ ≡ H x
                  absEq = trans (cong ∣_∣ℚ (neg-sub (b x) (a x))) (∣-p∣≡∣p∣ (a x -ℚ b x))

  ∣Pr-Pr∣≤1 : (μ ν : Dist-ℚ Bool) → ∣ Pr₁ μ -ℚ Pr₁ ν ∣ℚ ≤ℚ 1ℚ
  ∣Pr-Pr∣≤1 μ ν = ∣diff∣≤1 (Pr₁≥0 μ) (Pr₁≤1 μ) (Pr₁≥0 ν) (Pr₁≤1 ν)
