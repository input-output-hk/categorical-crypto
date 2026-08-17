{-# OPTIONS --safe --without-K #-}

-- Generic linearity for weighted assoc-lists, parametric in the
-- weight semiring.

open import Algebra using (CommutativeSemiring)

module ProbabilisticLogic.Distribution.Linearity {c ℓ} (R : CommutativeSemiring c ℓ) where

open import Level
open import Data.Product
import Relation.Binary.Reasoning.Setoid as ≈-Reasoning
open import Data.List as L
import Data.List.Properties as LP
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Relation.Unary.All as All using (All)
open import Data.List.Relation.Unary.AllPairs using ([]; _∷_)
open import Data.List.Relation.Unary.Unique.Propositional using (Unique)
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_; _≢_)

open CommutativeSemiring R renaming (Carrier to W)
open ≈-Reasoning setoid

open import Algebra.Properties.CommutativeSemigroup +-commutativeSemigroup
  using () renaming (interchange to +-swap-middle)

open import Algebra.Properties.CommutativeSemigroup *-commutativeSemigroup
  using (x∙yz≈y∙xz)

private
  variable
    ℓ₁ ℓ₂ ℓ₃ : Level
    A : Set ℓ₁
    B : Set ℓ₂

------------------------------------------------------------------------
-- Lookup on assoc lists: `Σᵢ wᵢ · P(aᵢ)`.
--
-- This is a little trick to avoid requiring decidable equality

lookup-L : List (W × A) → (A → W) → W
lookup-L []             _ = 0#
lookup-L ((w , a) ∷ xs) P = w * P a + lookup-L xs P

------------------------------------------------------------------------
-- Pointwise weight scaling.

scaleL : W → List (W × A) → List (W × A)
scaleL w = L.map (λ (w′ , a) → (w * w′ , a))

scaleL-++ : ∀ (w : W) (xs ys : List (W × A))
          → scaleL w (xs ++ ys) ≡ scaleL w xs ++ scaleL w ys
scaleL-++ w xs ys = LP.map-++ _ xs ys

------------------------------------------------------------------------
-- Linearity lemmas.

lookup-L-++ : (xs ys : List (W × A)) (P : A → W)
            → lookup-L (xs ++ ys) P ≈ lookup-L xs P + lookup-L ys P
lookup-L-++ []             ys P = sym (+-identityˡ _)
lookup-L-++ ((w , a) ∷ xs) ys P = begin
  w * P a + lookup-L (xs ++ ys) P
    ≈⟨ +-congˡ (lookup-L-++ xs ys P) ⟩
  w * P a + (lookup-L xs P + lookup-L ys P)
    ≈⟨ sym (+-assoc _ _ _) ⟩
  (w * P a + lookup-L xs P) + lookup-L ys P ∎

lookup-L-scaleL : (w : W) (xs : List (W × A)) (P : A → W)
                → lookup-L (scaleL w xs) P ≈ w * lookup-L xs P
lookup-L-scaleL w []              P = sym (zeroʳ w)
lookup-L-scaleL w ((w′ , a) ∷ xs) P = begin
  (w * w′) * P a + lookup-L (scaleL w xs) P
    ≈⟨ +-cong (*-assoc w w′ (P a)) (lookup-L-scaleL w xs P) ⟩
  w * (w′ * P a) + w * lookup-L xs P
    ≈⟨ sym (distribˡ w _ _) ⟩
  w * (w′ * P a + lookup-L xs P) ∎

lookup-L-cong-P : (xs : List (W × A)) {P Q : A → W}
                → (∀ a → P a ≈ Q a) → lookup-L xs P ≈ lookup-L xs Q
lookup-L-cong-P []             P≈Q = refl
lookup-L-cong-P ((w , a) ∷ xs) P≈Q =
  +-cong (*-congˡ (P≈Q a)) (lookup-L-cong-P xs P≈Q)

lookup-L-zero : (xs : List (W × A)) → lookup-L xs (λ _ → 0#) ≈ 0#
lookup-L-zero []             = refl
lookup-L-zero ((w , a) ∷ xs) = begin
  w * 0# + lookup-L xs (λ _ → 0#)
    ≈⟨ +-cong (zeroʳ w) (lookup-L-zero xs) ⟩
  0# + 0#
    ≈⟨ +-identityˡ _ ⟩
  0# ∎

lookup-L-+ : (xs : List (W × A)) (P Q : A → W)
           → lookup-L xs (λ a → P a + Q a) ≈ lookup-L xs P + lookup-L xs Q
lookup-L-+ []             P Q = sym (+-identityˡ _)
lookup-L-+ ((w , a) ∷ xs) P Q = begin
  w * (P a + Q a) + lookup-L xs (λ a′ → P a′ + Q a′)
    ≈⟨ +-cong (distribˡ w _ _) (lookup-L-+ xs P Q) ⟩
  (w * P a + w * Q a) + (lookup-L xs P + lookup-L xs Q)
    ≈⟨ +-swap-middle _ _ _ _ ⟩
  (w * P a + lookup-L xs P) + (w * Q a + lookup-L xs Q) ∎

lookup-L-*ₗ : (c′ : W) (xs : List (W × A)) (P : A → W)
            → lookup-L xs (λ a → c′ * P a) ≈ c′ * lookup-L xs P
lookup-L-*ₗ c′ []             P = sym (zeroʳ c′)
lookup-L-*ₗ c′ ((w , a) ∷ xs) P = begin
  w * (c′ * P a) + lookup-L xs (λ a′ → c′ * P a′)
    ≈⟨ +-cong (x∙yz≈y∙xz w c′ (P a)) (lookup-L-*ₗ c′ xs P) ⟩
  c′ * (w * P a) + c′ * lookup-L xs P
    ≈⟨ sym (distribˡ c′ _ _) ⟩
  c′ * (w * P a + lookup-L xs P) ∎

------------------------------------------------------------------------
-- Total mass of a list.

mass-L : List (W × A) → W
mass-L xs = lookup-L xs (λ _ → 1#)

mass-L-++ : (xs ys : List (W × A))
          → mass-L (xs ++ ys) ≈ mass-L xs + mass-L ys
mass-L-++ xs ys = lookup-L-++ xs ys (λ _ → 1#)

mass-L-scale : (w : W) (xs : List (W × A))
             → mass-L (scaleL w xs) ≈ w * mass-L xs
mass-L-scale w xs = lookup-L-scaleL w xs (λ _ → 1#)

-- `lookup-L` against a constant test `λ _ → c` factors as `mass-L * c`.
-- Used by callers that need to discharge `discard`-style identities
-- where the kernel value is independent of the sample.
lookup-L-const : (xs : List (W × A)) (c : W)
               → lookup-L xs (λ _ → c) ≈ mass-L xs * c
lookup-L-const []             c = sym (zeroˡ c)
lookup-L-const ((w , a) ∷ xs) c = begin
  w * c + lookup-L xs (λ _ → c)
    ≈⟨ +-congˡ (lookup-L-const xs c) ⟩
  w * c + mass-L xs * c
    ≈⟨ +-congʳ (*-congʳ (sym (*-identityʳ w))) ⟩
  (w * 1#) * c + mass-L xs * c
    ≈⟨ sym (distribʳ c (w * 1#) (mass-L xs)) ⟩
  (w * 1# + mass-L xs) * c ∎

------------------------------------------------------------------------
-- Bind / Fubini.
--
-- We don't depend on `NE.List⁺`'s monad structure here; the concrete
-- modules unfold `NE.concatMap` into `L.concatMap` via the
-- `toList-concatMap-NE` lemma local to each, and feed us the resulting
-- `List`-level expression.

lookup-L-concatMap-scaleL :
    (k : A → List (W × B)) (P : B → W) (xs : List (W × A))
  → lookup-L (L.concatMap (λ (w , a) → scaleL w (k a)) xs) P
  ≈ lookup-L xs (λ a → lookup-L (k a) P)
lookup-L-concatMap-scaleL k P []             = refl
lookup-L-concatMap-scaleL k P ((w , a) ∷ xs) = begin
  lookup-L (scaleL w (k a) ++ L.concatMap _ xs) P
    ≈⟨ lookup-L-++ (scaleL w (k a)) _ P ⟩
  lookup-L (scaleL w (k a)) P + lookup-L (L.concatMap _ xs) P
    ≈⟨ +-cong (lookup-L-scaleL w (k a) P)
              (lookup-L-concatMap-scaleL k P xs) ⟩
  w * lookup-L (k a) P + lookup-L xs (λ a′ → lookup-L (k a′) P) ∎

-- Fubini on lists: swap the order of two nested `lookup-L`s.
lookup-L-swap : (xs : List (W × A)) (ys : List (W × B))
                (P : A → B → W)
              → lookup-L xs (λ x → lookup-L ys (P x))
              ≈ lookup-L ys (λ y → lookup-L xs (λ x → P x y))
lookup-L-swap []             ys P = sym (lookup-L-zero ys)
lookup-L-swap ((w , x) ∷ xs) ys P = begin
  w * lookup-L ys (P x) + lookup-L xs (λ x′ → lookup-L ys (P x′))
    ≈⟨ +-congˡ (lookup-L-swap xs ys P) ⟩
  w * lookup-L ys (P x) + lookup-L ys (λ y → lookup-L xs (λ x′ → P x′ y))
    ≈⟨ +-congʳ (sym (lookup-L-*ₗ w ys (P x))) ⟩
  lookup-L ys (λ y → w * P x y) + lookup-L ys (λ y → lookup-L xs (λ x′ → P x′ y))
    ≈⟨ sym (lookup-L-+ ys (λ y → w * P x y) (λ y → lookup-L xs (λ x′ → P x′ y))) ⟩
  lookup-L ys (λ y → w * P x y + lookup-L xs (λ x′ → P x′ y)) ∎

------------------------------------------------------------------------
-- Regrouping by distinct points.
--
-- `lookup-L es f` can be regrouped as a sum over any duplicate-free
-- list `sup` covering the points of `es`: each support point
-- contributes its total weight times the test value.  This is the
-- bridge between the multiplicity-bearing entry-list presentation and
-- the point-mass ("measure") presentation of a weighted list.
--
-- The module is parametric in an abstract "singleton indicator" `δ`
-- (with `δ b b ≈ 1#` and `δ b a ≈ 0#` off the diagonal), so the caller
-- can supply whichever concrete indicator it already reasons about
-- (e.g. a decidable-predicate `1[_]`) rather than a fixed `_≟_`-based
-- one.

module Regroup {ℓ₁} {A : Set ℓ₁}
  (δ : A → A → W)
  (δ-self  : ∀ b → δ b b ≈ 1#)
  (δ-other : ∀ {b a} → b ≢ a → δ b a ≈ 0#)
  where

  -- Total weight of `es` at the point `a`.
  wt : List (W × A) → A → W
  wt es a = lookup-L es (λ b → δ b a)

  private
    -- Entries `w · δ b _` contribute nothing over points distinct
    -- from `b`.
    δ-zero-sum : ∀ (w : W) b (f : A → W) {rest : List A} → All (b ≢_) rest
               → lookup-L (L.map (λ a → (w * δ b a , a)) rest) f ≈ 0#
    δ-zero-sum w b f All.[] = refl
    δ-zero-sum w b f {a ∷ rest} (b≢a All.∷ pf) = begin
      (w * δ b a) * f a + lookup-L (L.map (λ a′ → (w * δ b a′ , a′)) rest) f
        ≈⟨ +-cong (*-congʳ (*-congˡ (δ-other b≢a))) (δ-zero-sum w b f pf) ⟩
      (w * 0#) * f a + 0#
        ≈⟨ +-identityʳ _ ⟩
      (w * 0#) * f a
        ≈⟨ *-congʳ (zeroʳ w) ⟩
      0# * f a
        ≈⟨ zeroˡ (f a) ⟩
      0# ∎

    -- Over a duplicate-free support containing `b`, the entries
    -- `w · δ b _` sum to exactly `w · f b`.
    δ-collapse : ∀ (w : W) b (f : A → W) {sup : List A} → Unique sup → b ∈ sup
               → lookup-L (L.map (λ a → (w * δ b a , a)) sup) f ≈ w * f b
    δ-collapse w b f {b′ ∷ sup} (b∉sup ∷ u) (here ≡.refl) = begin
      (w * δ b b) * f b + lookup-L (L.map (λ a → (w * δ b a , a)) sup) f
        ≈⟨ +-cong (*-congʳ (trans (*-congˡ (δ-self b)) (*-identityʳ w)))
                  (δ-zero-sum w b f b∉sup) ⟩
      w * f b + 0#
        ≈⟨ +-identityʳ _ ⟩
      w * f b ∎
    δ-collapse w b f {a ∷ sup} (a∉sup ∷ u) (there b∈sup) = begin
      (w * δ b a) * f a + lookup-L (L.map (λ a′ → (w * δ b a′ , a′)) sup) f
        ≈⟨ +-cong (trans (*-congʳ (trans (*-congˡ (δ-other b≢a)) (zeroʳ w))) (zeroˡ (f a)))
                  (δ-collapse w b f u b∈sup) ⟩
      0# + w * f b
        ≈⟨ +-identityˡ _ ⟩
      w * f b ∎
      where
        b≢a : b ≢ a
        b≢a b≡a = All.lookup a∉sup b∈sup (≡.sym b≡a)

    -- Splitting a pointwise sum of weights over a mapped support.
    lookup-L-map-+ : (g h : A → W) (sup : List A) (f : A → W)
      → lookup-L (L.map (λ a → (g a + h a , a)) sup) f
      ≈ lookup-L (L.map (λ a → (g a , a)) sup) f
        + lookup-L (L.map (λ a → (h a , a)) sup) f
    lookup-L-map-+ g h []        f = sym (+-identityˡ _)
    lookup-L-map-+ g h (a ∷ sup) f = begin
      (g a + h a) * f a + lookup-L (L.map (λ a′ → (g a′ + h a′ , a′)) sup) f
        ≈⟨ +-cong (distribʳ (f a) (g a) (h a)) (lookup-L-map-+ g h sup f) ⟩
      (g a * f a + h a * f a)
        + (lookup-L (L.map (λ a′ → (g a′ , a′)) sup) f
           + lookup-L (L.map (λ a′ → (h a′ , a′)) sup) f)
        ≈⟨ +-swap-middle _ _ _ _ ⟩
      (g a * f a + lookup-L (L.map (λ a′ → (g a′ , a′)) sup) f)
        + (h a * f a + lookup-L (L.map (λ a′ → (h a′ , a′)) sup) f) ∎

    zero-weights : (f : A → W) (sup : List A)
                 → lookup-L (L.map (λ a → (0# , a)) sup) f ≈ 0#
    zero-weights f []        = refl
    zero-weights f (a ∷ sup) = begin
      0# * f a + lookup-L (L.map (λ a′ → (0# , a′)) sup) f
        ≈⟨ +-cong (zeroˡ (f a)) (zero-weights f sup) ⟩
      0# + 0#
        ≈⟨ +-identityˡ _ ⟩
      0# ∎

  -- Pointwise-≈ congruence in the weights of a mapped support.
  lookup-L-map-cong : (g h : A → W) → (∀ a → g a ≈ h a)
                    → (sup : List A) (f : A → W)
                    → lookup-L (L.map (λ a → (g a , a)) sup) f
                    ≈ lookup-L (L.map (λ a → (h a , a)) sup) f
  lookup-L-map-cong g h g≈h []        f = refl
  lookup-L-map-cong g h g≈h (a ∷ sup) f =
    +-cong (*-congʳ (g≈h a)) (lookup-L-map-cong g h g≈h sup f)

  -- The regrouping theorem.
  lookup-L-regroup : (es : List (W × A)) {sup : List A} → Unique sup
                   → (∀ {w b} → (w , b) ∈ es → b ∈ sup)
                   → (f : A → W)
                   → lookup-L es f ≈ lookup-L (L.map (λ a → (wt es a , a)) sup) f
  lookup-L-regroup [] {sup} u cov f = sym (zero-weights f sup)
  lookup-L-regroup ((w , b) ∷ es) {sup} u cov f = begin
    w * f b + lookup-L es f
      ≈⟨ +-cong (sym (δ-collapse w b f u (cov (here ≡.refl))))
                (lookup-L-regroup es u (λ e∈ → cov (there e∈)) f) ⟩
    lookup-L (L.map (λ a → (w * δ b a , a)) sup) f
      + lookup-L (L.map (λ a → (wt es a , a)) sup) f
      ≈⟨ sym (lookup-L-map-+ (λ a → w * δ b a) (wt es) sup f) ⟩
    lookup-L (L.map (λ a → (w * δ b a + wt es a , a)) sup) f ∎
