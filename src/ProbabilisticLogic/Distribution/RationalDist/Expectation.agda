{-# OPTIONS --safe --without-K #-}

open import categorical-crypto.Prelude hiding (_>>=_; _*_; _/_)

open import Data.List.NonEmpty as NE using ()
open import Data.List.Relation.Unary.All as ListAll using ()
open import Data.Rational
  renaming (_*_ to _*ℚ_; _+_ to _+ℚ_; _-_ to _-ℚ_; -_ to -ℚ_; ∣_∣ to ∣_∣ℚ; _≤_ to _≤ℚ_)
open import Data.Rational.Properties
open import Data.Rational.Properties.Ext

open import ProbabilisticLogic.Distribution.RationalDist
open import ProbabilisticLogic.Distribution.RationalDist.Partial
open import ProbabilisticLogic.Distribution.Uniform

module ProbabilisticLogic.Distribution.RationalDist.Expectation where

private variable
  ℓ : Level
  A B C : Type

E : Dist-ℚ A → (A → ℚ) → ℚ
E μ f = lookupᴰℚ (entries μ) f

Pr₁ : Dist-ℚ Bool → ℚ
Pr₁ μ = E μ bool→ℚ

------------------------------------------------------------------------
-- The expectation algebra

E-add : (μ : Dist-ℚ A) (f g : A → ℚ) → E μ (λ a → f a +ℚ g a) ≡ E μ f +ℚ E μ g
E-add μ = lookupᴰℚ-+ (entries μ)

E-const : (μ : Dist-ℚ A) (c : ℚ) → E μ (λ _ → c) ≡ c
E-const = lookupᴰℚ-const

E-+const : (μ : Dist-ℚ A) (f : A → ℚ) (c : ℚ) → E μ (λ a → f a +ℚ c) ≡ E μ f +ℚ c
E-+const μ f c = trans (E-add μ f (λ _ → c)) (cong (E μ f +ℚ_) (E-const μ c))

E-const+ : (μ : Dist-ℚ A) (c : ℚ) (f : A → ℚ) → E μ (λ a → c +ℚ f a) ≡ c +ℚ E μ f
E-const+ μ c f = trans (E-add μ (λ _ → c) f) (cong (_+ℚ E μ f) (E-const μ c))

E-sub : (μ : Dist-ℚ A) (a b : A → ℚ) → E μ (λ x → a x -ℚ b x) ≡ E μ a -ℚ E μ b
E-sub μ a b = trans (sym (+-−-cancel (E μ (λ x → a x -ℚ b x)) (E μ b)))
                    (cong (_-ℚ E μ b) eq)
  where eq : E μ (λ x → a x -ℚ b x) +ℚ E μ b ≡ E μ a
        eq = trans (sym (E-add μ (λ x → a x -ℚ b x) b))
                   (lookupᴰℚ-cong-P (entries μ) (λ x → −-+-cancel (a x) (b x)))

E-bind : (μ : Dist-ℚ A) (h : A → Dist-ℚ B) (P : B → ℚ)
       → E (μ >>=ᴹ h) P ≡ E μ (λ a → E (h a) P)
E-bind μ h P = lookupᴰℚ-bind (entries μ) (λ a → entries (h a)) P

E-return-cong : (a : A) (b : B) (F : A → ℚ) (G : B → ℚ) → F a ≡ G b
              → E (return-ℚ a) F ≡ E (return-ℚ b) G
E-return-cong a b F G eq = trans (lookupᴰℚ-return a F) (trans eq (sym (lookupᴰℚ-return b G)))

Pr₁-bind : (μ : Dist-ℚ A) (k : A → Dist-ℚ Bool) → Pr₁ (μ >>=ᴹ k) ≡ E μ (λ a → Pr₁ (k a))
Pr₁-bind μ k = lookupᴰℚ-bind (entries μ) (λ a → entries (k a)) bool→ℚ

E-bind₂ : (μ : Dist-ℚ A) (ν : Dist-ℚ B) (κ : A → B → C) (G : C → ℚ)
        → E (μ >>=ᴹ λ a → ν >>=ᴹ λ b → return-ℚ (κ a b)) G ≡ E μ (λ a → E ν (λ b → G (κ a b)))
E-bind₂ μ ν κ G = trans (E-bind μ (λ a → ν >>=ᴹ λ b → return-ℚ (κ a b)) G)
  (lookupᴰℚ-cong-P (entries μ) (λ a → trans (E-bind ν (λ b → return-ℚ (κ a b)) G)
    (lookupᴰℚ-cong-P (entries ν) (λ b → lookupᴰℚ-return (κ a b) G))))

E-swap : (μ : Dist-ℚ A) (ν : Dist-ℚ B) (P : A → B → ℚ)
       → E μ (λ a → E ν (P a)) ≡ E ν (λ b → E μ (λ a → P a b))
E-swap μ ν = lookupᴰℚ-swap (entries μ) (entries ν)

------------------------------------------------------------------------
-- The partial (`Dist⊥`) reading

maybeℚ : {A : Type ℓ} → (A → ℚ) → Maybe A → ℚ
maybeℚ P (just a) = P a
maybeℚ P nothing  = 0ℚ

E⊥ : {A : Type ℓ} → Dist⊥ A → (A → ℚ) → ℚ
E⊥ μ P = lookupᴰℚ (entries μ) (maybeℚ P)

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

E⊥-map : (f : A → B) (ν : Dist⊥ A) (G : B → ℚ) → E⊥ (Dmap⊥ f ν) G ≡ E⊥ ν (λ p → G (f p))
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

E⊥-coin : (μ : Dist-ℚ Bool) (κ : Bool → Dist⊥ A) (G : A → ℚ)
        → E⊥ (Dmap just μ >>=⊥ κ) G ≡ E⊥ (μ >>=ᴹ κ) G
E⊥-coin μ κ G =
  trans (E⊥-bind (Dmap just μ) κ G)
        (trans (lookupᴰℚ-Dmap just μ (maybeℚ λ c → E⊥ (κ c) G))
               (sym (E-bind μ κ (maybeℚ G))))

mb : Maybe Bool → ℚ
mb = maybeℚ bool→ℚ

Prᵇ⊥ : Bool → Dist⊥ Bool → ℚ
Prᵇ⊥ b μ = E μ (maybeℚ (indᵇ b))

Pr₁⊥ : Dist⊥ Bool → ℚ
Pr₁⊥ = Prᵇ⊥ true

Pr₁⊥-just : (μ : Dist-ℚ Bool) → Pr₁⊥ (Dmap just μ) ≡ Pr₁ μ
Pr₁⊥-just μ = Eⱼ μ bool→ℚ

Pr₁⊥-cong : (μ ν : Dist⊥ Bool) → μ ≈Mℚ ν → Pr₁⊥ μ ≡ Pr₁⊥ ν
Pr₁⊥-cong μ ν μ≈ν = μ≈ν mb

-- A verdict read after a kernel that samples first: constant on every sample,
-- constant after the average.
Pr₁⊥-bind-const : (μ : Dist⊥ A) (D : Dist-ℚ B) (ν : B → Dist⊥ A) (K : A → Dist⊥ Bool) (c : ℚ)
                → μ ≈Mℚ (D >>=ᴹ ν) → (∀ b → Pr₁⊥ (ν b >>=⊥ K) ≡ c) → Pr₁⊥ (μ >>=⊥ K) ≡ c
Pr₁⊥-bind-const μ D ν K c eq hit =
  trans (>>=⊥-congʳ K μ (D >>=ᴹ ν) eq mb)
 (trans (>>=ᴹ-assoc D ν (kmaybe K) mb)
 (trans (E-bind D (λ b → ν b >>=⊥ K) mb)
        (trans (lookupᴰℚ-cong-P (entries D) hit) (E-const D c))))

------------------------------------------------------------------------
-- Monotonicity

E-mono-on : (μ : Dist-ℚ A) (f g : A → ℚ) → OnSupport (λ a → f a ≤ℚ g a) μ → E μ f ≤ℚ E μ g
E-mono-on μ f g = lookupᴰℚ-mono (entries μ) (weights-nn μ)

E-mono : (μ : Dist-ℚ A) (f g : A → ℚ) → (∀ a → f a ≤ℚ g a) → E μ f ≤ℚ E μ g
E-mono μ f g pt = E-mono-on μ f g
  (ListAll.universal (λ e → pt (proj₂ e)) (NE.toList (entries μ)))

E-nn : (μ : Dist-ℚ A) (f : A → ℚ) → (∀ a → 0ℚ ≤ℚ f a) → 0ℚ ≤ℚ E μ f
E-nn μ f nn = ≤-trans (≤-reflexive (sym (E-const μ 0ℚ))) (E-mono μ (λ _ → 0ℚ) f nn)

E-cong-on : (μ : Dist-ℚ A) (f g : A → ℚ) → OnSupport (λ a → f a ≡ g a) μ → E μ f ≡ E μ g
E-cong-on μ f g sp = ≤-antisym (E-mono-on μ f g (ListAll.map ≤-reflexive sp))
                               (E-mono-on μ g f (ListAll.map (≤-reflexive ∘ sym) sp))

Pr₁≤1 : (μ : Dist-ℚ Bool) → Pr₁ μ ≤ℚ 1ℚ
Pr₁≤1 μ = ≤-trans (E-mono μ bool→ℚ (λ _ → 1ℚ) bool≤1) (≤-reflexive (E-const μ 1ℚ))

Pr₁≥0 : (μ : Dist-ℚ Bool) → 0ℚ ≤ℚ Pr₁ μ
Pr₁≥0 μ = ≤-trans (≤-reflexive (sym (E-const μ 0ℚ))) (E-mono μ (λ _ → 0ℚ) bool→ℚ 0≤bool)

-- The complement rule on a total verdict; `Dp.Mass.verdict-mass` is its `Dₚ` analogue.
E-not : (μ : Dist-ℚ Bool) → E μ (indᵇ false) ≡ 1ℚ -ℚ Pr₁ μ
E-not μ = trans (lookupᴰℚ-cong-P (entries μ) pt)
         (trans (E-sub μ (λ _ → 1ℚ) bool→ℚ) (cong (_-ℚ Pr₁ μ) (E-const μ 1ℚ)))
  where pt : ∀ x → bool→ℚ (not x) ≡ 1ℚ -ℚ bool→ℚ x
        pt true  = sym (+-inverseʳ 1ℚ)
        pt false = sym (+-identityʳ 1ℚ)

E⊥-mono : (μ : Dist⊥ A) (F G : A → ℚ) → (∀ a → F a ≤ℚ G a) → E⊥ μ F ≤ℚ E⊥ μ G
E⊥-mono μ F G pt = E-mono μ (maybeℚ F) (maybeℚ G) λ where
  (just a) → pt a
  nothing  → ≤-refl

Pr₁⊥-bindᴹ-mono : (μ : Dist-ℚ A) (L R : A → Dist⊥ Bool)
                → (∀ a → Pr₁⊥ (L a) ≤ℚ Pr₁⊥ (R a)) → Pr₁⊥ (μ >>=ᴹ L) ≤ℚ Pr₁⊥ (μ >>=ᴹ R)
Pr₁⊥-bindᴹ-mono μ L R pt = ≤-trans (≤-reflexive (E-bind μ L mb))
  (≤-trans (E-mono μ (λ a → Pr₁⊥ (L a)) (λ a → Pr₁⊥ (R a)) pt) (≤-reflexive (sym (E-bind μ R mb))))

Pr₁⊥-bind-mono : (μ : Dist⊥ A) (L R : A → Dist⊥ Bool)
               → (∀ a → Pr₁⊥ (L a) ≤ℚ Pr₁⊥ (R a)) → Pr₁⊥ (μ >>=⊥ L) ≤ℚ Pr₁⊥ (μ >>=⊥ R)
Pr₁⊥-bind-mono μ L R pt = ≤-trans (≤-reflexive (E⊥-bind μ L bool→ℚ))
  (≤-trans (E⊥-mono μ (λ a → Pr₁⊥ (L a)) (λ a → Pr₁⊥ (R a)) pt)
           (≤-reflexive (sym (E⊥-bind μ R bool→ℚ))))

Pr₁⊥≤1 : (μ : Dist⊥ Bool) → Pr₁⊥ μ ≤ℚ 1ℚ
Pr₁⊥≤1 μ = ≤-trans (E-mono μ mb (λ _ → 1ℚ) bd) (≤-reflexive (E-const μ 1ℚ))
  where bd : ∀ x → mb x ≤ℚ 1ℚ
        bd (just b) = bool≤1 b
        bd nothing  = 0≤1ℚ

E-abs-diff : (μ : Dist-ℚ A) (a b : A → ℚ) → ∣ E μ a -ℚ E μ b ∣ℚ ≤ℚ E μ (λ x → ∣ a x -ℚ b x ∣ℚ)
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
        bnd x = subst ((b x -ℚ a x) ≤ℚ_) (∣-∣-comm (b x) (a x)) (p≤∣p∣ (b x -ℚ a x))

∣Pr-Pr∣≤1 : (μ ν : Dist-ℚ Bool) → ∣ Pr₁ μ -ℚ Pr₁ ν ∣ℚ ≤ℚ 1ℚ
∣Pr-Pr∣≤1 μ ν = ∣diff∣≤1 (Pr₁≥0 μ) (Pr₁≤1 μ) (Pr₁≥0 ν) (Pr₁≤1 ν)

------------------------------------------------------------------------
-- The same through the Maybe layer

Mb : (A → Type) → Maybe A → Type
Mb P (just a) = P a
Mb P nothing  = ⊤

OnSupport⊥ : (A → Type) → Dist⊥ A → Type
OnSupport⊥ P = OnSupport (Mb P)

E⊥-mono-on : (μ : Dist⊥ A) (F G : A → ℚ) → OnSupport⊥ (λ a → F a ≤ℚ G a) μ → E⊥ μ F ≤ℚ E⊥ μ G
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
            nothing  → ∣x-x∣≡0 0ℚ))
