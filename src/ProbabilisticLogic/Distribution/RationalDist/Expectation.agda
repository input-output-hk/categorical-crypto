{-# OPTIONS --safe --without-K #-}

-- Expectation of a ℚ-valued observable under a `Dist-ℚ`, the probability of
-- `true`, and their algebra.

open import categorical-crypto.Prelude hiding (_>>=_; _*_; _/_)

open import Data.List.NonEmpty as NE using ()
open import Data.List.Relation.Unary.All as ListAll using ()
open import Data.Rational using (ℚ; 0ℚ; 1ℚ)
  renaming (_*_ to _*ℚ_; _+_ to _+ℚ_; _-_ to _-ℚ_; -_ to -ℚ_; ∣_∣ to ∣_∣ℚ; _≤_ to _≤ℚ_)
open import Data.Rational.Properties using
  (≤-antisym; ≤-refl; ≤-reflexive; ≤-trans; *-identityˡ; +-inverseʳ; 0≤p⇒∣p∣≡p; ∣-p∣≡∣p∣)
open import Data.Rational.Properties.Ext

open import ProbabilisticLogic.Distribution.RationalDist
open import ProbabilisticLogic.Distribution.RationalDist.Partial
open import ProbabilisticLogic.Distribution.Uniform using (bool→ℚ; indᵇ)

module ProbabilisticLogic.Distribution.RationalDist.Expectation where

private variable
  ℓ : Level
  A B C : Type

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

-- Two independent draws and a function of both — the shape a reactive
-- kernel's step takes, read at an arbitrary observable.
E-bind₂ : (μ : Dist-ℚ A) (ν : Dist-ℚ B) (κ : A → B → C) (G : C → ℚ)
        → E (μ >>=ᴹ λ a → ν >>=ᴹ λ b → return-ℚ (κ a b)) G ≡ E μ (λ a → E ν (λ b → G (κ a b)))
E-bind₂ μ ν κ G = trans (E-bind μ (λ a → ν >>=ᴹ λ b → return-ℚ (κ a b)) G)
  (lookupᴰℚ-cong-P (entries μ) (λ a → trans (E-bind ν (λ b → return-ℚ (κ a b)) G)
    (lookupᴰℚ-cong-P (entries ν) (λ b → lookupᴰℚ-return (κ a b) G))))

-- Fubini: independent expectations commute.  Two `Dist-ℚ`s never share a
-- sample, so nesting them in either order weighs the same integrand.
E-swap : (μ : Dist-ℚ A) (ν : Dist-ℚ B) (P : A → B → ℚ)
       → E μ (λ a → E ν (P a)) ≡ E ν (λ b → E μ (λ a → P a b))
E-swap μ ν = lookupᴰℚ-swap (entries μ) (entries ν)

0≤bool : ∀ b → 0ℚ ≤ℚ bool→ℚ b
0≤bool true  = 0≤1ℚ
0≤bool false = ≤-refl

------------------------------------------------------------------------
-- The partial (`Dist⊥`) reading: the divergence sink `nothing` scores `0`.

maybeℚ : {A : Type ℓ} → (A → ℚ) → Maybe A → ℚ
maybeℚ P (just a) = P a
maybeℚ P nothing  = 0ℚ

E⊥ : {A : Type ℓ} → Dist⊥ A → (A → ℚ) → ℚ
E⊥ μ P = lookupᴰℚ (entries μ) (maybeℚ P)

-- The `nothing` sink is absorbing, so the bind law survives the Maybe layer.
E⊥-bind : (μ : Dist⊥ A) (h : A → Dist⊥ B) (P : B → ℚ)
        → E⊥ (μ >>=⊥ h) P ≡ E⊥ μ (λ a → E⊥ (h a) P)
E⊥-bind μ h P = trans (E-bind μ (kmaybe h) (maybeℚ P)) (lookupᴰℚ-cong-P (entries μ) λ where
  (just a) → refl
  nothing  → lookupᴰℚ-return nothing (maybeℚ P))

E⊥-return : (a : A) (P : A → ℚ) → E⊥ (return⊥ a) P ≡ P a
E⊥-return a P = lookupᴰℚ-return (just a) (maybeℚ P)

Eⱼ : (μ : Dist-ℚ A) (Q : A → ℚ) → E⊥ (Dmap just μ) Q ≡ E μ Q
Eⱼ μ Q = lookupᴰℚ-Dmap just μ (maybeℚ Q)

E⊥-cong-P : (ν : Dist⊥ A) (F G : A → ℚ) → (∀ a → F a ≡ G a) → E⊥ ν F ≡ E⊥ ν G
E⊥-cong-P ν F G eq = lookupᴰℚ-cong-P (entries ν) λ where
  (just a) → eq a
  nothing  → refl

E⊥-map : (f : A → B) (ν : Dist⊥ A) (G : B → ℚ)
       → E⊥ (Dmap⊥ f ν) G ≡ E⊥ ν (λ p → G (f p))
E⊥-map f ν G =
  trans (E⊥-bind ν (λ p → return⊥ (f p)) G)
        (lookupᴰℚ-cong-P (entries ν) λ where
          (just p) → E⊥-return (f p) G
          nothing  → refl)

E⊥-map-bind : (f : A → B) (ν : Dist⊥ A) (κ : B → Dist⊥ C) (G : C → ℚ)
            → E⊥ (Dmap⊥ f ν >>=⊥ κ) G ≡ E⊥ (ν >>=⊥ λ p → κ (f p)) G
E⊥-map-bind f ν κ G =
  trans (E⊥-bind (Dmap⊥ f ν) κ G)
        (trans (E⊥-map f ν (λ p → E⊥ (κ p) G))
               (sym (E⊥-bind ν (λ p → κ (f p)) G)))

mb : Maybe Bool → ℚ
mb = maybeℚ bool→ℚ

-- The mass of verdict `b`, with `nothing` scoring 0 for EITHER indicator: that
-- is what keeps a diverging experiment distinct from one answering `false`
-- (`ProbabilisticLogic.Dp.Advantage`'s header).
Prᵇ⊥ : Bool → Dist⊥ Bool → ℚ
Prᵇ⊥ b μ = E μ (maybeℚ (indᵇ b))

-- `Pr₁⊥` is `E⊥` at the verdict indicator, on the nose.
Pr₁⊥ : Dist⊥ Bool → ℚ
Pr₁⊥ = Prᵇ⊥ true

Pr₁⊥-just : (μ : Dist-ℚ Bool) → Pr₁⊥ (Dmap just μ) ≡ Pr₁ μ
Pr₁⊥-just μ = lookupᴰℚ-Dmap just μ mb

Pr₁⊥-cong : (μ ν : Dist⊥ Bool) → μ ≈Mℚ ν → Pr₁⊥ μ ≡ Pr₁⊥ ν
Pr₁⊥-cong μ ν μ≈ν = μ≈ν mb

------------------------------------------------------------------------
-- Monotonicity, and what it buys
--
-- `E-mono-on` is where `Dist-ℚ`'s non-negativity invariant is spent; global
-- monotonicity, the [0,1]-boundedness of `Pr₁` and the expectation triangle
-- inequality all follow from it and nothing else.

E-mono-on : (μ : Dist-ℚ A) (f g : A → ℚ)
          → OnSupport (λ a → f a ≤ℚ g a) μ → E μ f ≤ℚ E μ g
E-mono-on μ f g = lookupᴰℚ-mono (entries μ) (weights-nn μ)

E-mono : (μ : Dist-ℚ A) (f g : A → ℚ) → (∀ a → f a ≤ℚ g a) → E μ f ≤ℚ E μ g
E-mono μ f g pt = E-mono-on μ f g
  (ListAll.universal (λ e → pt (proj₂ e)) (NE.toList (entries μ)))

-- Congruence off the support is free, so `lookupᴰℚ-cong-P`'s pointwise
-- hypothesis is more than an expectation needs.
E-cong-on : (μ : Dist-ℚ A) (f g : A → ℚ) → OnSupport (λ a → f a ≡ g a) μ → E μ f ≡ E μ g
E-cong-on μ f g sp = ≤-antisym (E-mono-on μ f g (ListAll.map ≤-reflexive sp))
                               (E-mono-on μ g f (ListAll.map (≤-reflexive ∘ sym) sp))

Pr₁≤1 : (μ : Dist-ℚ Bool) → Pr₁ μ ≤ℚ 1ℚ
Pr₁≤1 μ = ≤-trans (E-mono μ bool→ℚ (λ _ → 1ℚ) b≤1) (≤-reflexive (E-const μ 1ℚ))
  where b≤1 : ∀ b → bool→ℚ b ≤ℚ 1ℚ
        b≤1 true  = ≤-refl
        b≤1 false = 0≤1ℚ

Pr₁≥0 : (μ : Dist-ℚ Bool) → 0ℚ ≤ℚ Pr₁ μ
Pr₁≥0 μ = ≤-trans (≤-reflexive (sym (E-const μ 0ℚ))) (E-mono μ (λ _ → 0ℚ) bool→ℚ 0≤bool)

-- The same through the Maybe layer: the divergence sink scores 0 either way.
E⊥-mono : (μ : Dist⊥ A) (F G : A → ℚ) → (∀ a → F a ≤ℚ G a) → E⊥ μ F ≤ℚ E⊥ μ G
E⊥-mono μ F G pt = E-mono μ (maybeℚ F) (maybeℚ G) λ where
  (just a) → pt a
  nothing  → ≤-refl

Pr₁⊥≤1 : (μ : Dist⊥ Bool) → Pr₁⊥ μ ≤ℚ 1ℚ
Pr₁⊥≤1 μ = ≤-trans (E-mono μ mb (λ _ → 1ℚ) bd) (≤-reflexive (E-const μ 1ℚ))
  where bd : ∀ x → mb x ≤ℚ 1ℚ
        bd (just true)  = ≤-refl
        bd (just false) = 0≤1ℚ
        bd nothing      = 0≤1ℚ

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

------------------------------------------------------------------------
-- …and the same four facts through the Maybe layer
--
-- Every one of them is its total counterpart at `maybeℚ`, the sink obligation
-- being `0ℚ ≤ 0ℚ` or `∣ 0ℚ -ℚ 0ℚ ∣ℚ ≡ 0ℚ`.  `GamePlaying.Partial` is what
-- spends them.

-- A predicate on the values, read through the sink: divergence constrains
-- nothing, which is what makes the partial invariant weaker than the total one.
Mb : (A → Type) → Maybe A → Type
Mb P (just a) = P a
Mb P nothing  = ⊤

OnSupport⊥ : (A → Type) → Dist⊥ A → Type
OnSupport⊥ P = OnSupport (Mb P)

E⊥-mono-on : (μ : Dist⊥ A) (F G : A → ℚ)
           → OnSupport⊥ (λ a → F a ≤ℚ G a) μ → E⊥ μ F ≤ℚ E⊥ μ G
E⊥-mono-on μ F G sp = E-mono-on μ (maybeℚ F) (maybeℚ G)
  (ListAll.map (λ {e} → sink (proj₂ e)) sp)
  where sink : (x : Maybe _) → Mb (λ a → F a ≤ℚ G a) x → maybeℚ F x ≤ℚ maybeℚ G x
        sink (just a) le = le
        sink nothing  _  = ≤-refl

Pr₁⊥≥0 : (μ : Dist⊥ Bool) → 0ℚ ≤ℚ Pr₁⊥ μ
Pr₁⊥≥0 μ = ≤-trans (≤-reflexive (sym (E-const μ 0ℚ))) (E-mono μ (λ _ → 0ℚ) mb bd)
  where bd : ∀ x → 0ℚ ≤ℚ mb x
        bd (just b) = 0≤bool b
        bd nothing  = ≤-refl

∣Pr⊥-Pr⊥∣≤1 : (μ ν : Dist⊥ Bool) → ∣ Pr₁⊥ μ -ℚ Pr₁⊥ ν ∣ℚ ≤ℚ 1ℚ
∣Pr⊥-Pr⊥∣≤1 μ ν = ∣diff∣≤1 (Pr₁⊥≥0 μ) (Pr₁⊥≤1 μ) (Pr₁⊥≥0 ν) (Pr₁⊥≤1 ν)

E⊥-abs-diff : (μ : Dist⊥ A) (a b : A → ℚ)
            → ∣ E⊥ μ a -ℚ E⊥ μ b ∣ℚ ≤ℚ E⊥ μ (λ x → ∣ a x -ℚ b x ∣ℚ)
E⊥-abs-diff μ a b =
  ≤-trans (E-abs-diff μ (maybeℚ a) (maybeℚ b))
          (≤-reflexive (lookupᴰℚ-cong-P (entries μ) λ where
            (just p) → refl
            nothing  → trans (cong ∣_∣ℚ (+-inverseʳ 0ℚ)) (0≤p⇒∣p∣≡p ≤-refl)))
