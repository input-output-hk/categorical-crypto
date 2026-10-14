{-# OPTIONS --safe --without-K #-}

module ProbabilisticLogic.Distribution.RationalDist.Product where

open import Data.Product.Base as Pair
open import Data.Rational.Base using (ℚ)
open import Function.Base using (_∘_)
open import Relation.Binary.PropositionalEquality

open import ProbabilisticLogic.Distribution.RationalDist

independent : ∀ {A B : Set} → Dist-ℚ A → Dist-ℚ B → Dist-ℚ (A × B)
independent μ ν = μ >>=ᴹ λ a → Dmap (a ,_) ν

private variable A B C D : Set

map-cong : (f : A → B) (μ ν : Dist-ℚ A) → μ ≈Mℚ ν → Dmap f μ ≈Mℚ Dmap f ν
map-cong f μ ν e P = trans (lookupᴰℚ-Dmap f μ P)
  (trans (e (P ∘ f)) (sym (lookupᴰℚ-Dmap f ν P)))

map-return : ∀ (f : A → B) a → Dmap f (return-ℚ a) ≈Mℚ return-ℚ (f a)
map-return f a = >>=ᴹ-identityˡ a (return-ℚ ∘ f)

mapped-bind : (f : A → B) (μ : Dist-ℚ A) (ν : Dist-ℚ B)
  (k : A → Dist-ℚ C) (l : B → Dist-ℚ C)
  → Dmap f μ ≈Mℚ ν → (∀ a → k a ≈Mℚ l (f a)) → (μ >>=ᴹ k) ≈Mℚ (ν >>=ᴹ l)
mapped-bind f μ ν k l e h P = trans
  (>>=ᴹ-cong {μ = μ} {ν = μ} {f = k} {g = l ∘ f} (λ _ → refl) h P)
  (trans (sym (Dmap->>= f μ l P))
    (>>=ᴹ-cong {μ = Dmap f μ} {ν = ν} {f = l} {g = l} e (λ _ _ → refl) P))

independent-eval : (μ : Dist-ℚ A) (ν : Dist-ℚ B) (P : A × B → ℚ)
  → lookupᴰℚ (entries (independent μ ν)) P
    ≡ lookupᴰℚ (entries μ) (λ a → lookupᴰℚ (entries ν) (λ b → P (a , b)))
independent-eval μ ν P = trans (lookupᴰℚ-bind (entries μ) _ P)
  (lookupᴰℚ-cong-P (entries μ) λ a → lookupᴰℚ-Dmap (a ,_) ν P)

map-independent : (f : A → C) (g : B → D) (μ : Dist-ℚ A) (ν : Dist-ℚ B)
  → Dmap (Pair.map f g) (independent μ ν) ≈Mℚ independent (Dmap f μ) (Dmap g ν)
map-independent f g μ ν P = begin
  lookupᴰℚ (entries (Dmap (Pair.map f g) (independent μ ν))) P
    ≡⟨ lookupᴰℚ-Dmap (Pair.map f g) (independent μ ν) P ⟩
  lookupᴰℚ (entries (independent μ ν)) (P ∘ Pair.map f g)
    ≡⟨ independent-eval μ ν (P ∘ Pair.map f g) ⟩
  lookupᴰℚ (entries μ) (λ a → lookupᴰℚ (entries ν) (λ b → P (f a , g b)))
    ≡⟨ sym (lookupᴰℚ-cong-P (entries μ) λ a → lookupᴰℚ-Dmap g ν (λ d → P (f a , d))) ⟩
  lookupᴰℚ (entries μ) (λ a → lookupᴰℚ (entries (Dmap g ν)) (λ d → P (f a , d)))
    ≡⟨ sym (lookupᴰℚ-Dmap f μ (λ c → lookupᴰℚ (entries (Dmap g ν)) (λ d → P (c , d)))) ⟩
  lookupᴰℚ (entries (Dmap f μ)) (λ c → lookupᴰℚ (entries (Dmap g ν)) (λ d → P (c , d)))
    ≡⟨ sym (independent-eval (Dmap f μ) (Dmap g ν) P) ⟩
  lookupᴰℚ (entries (independent (Dmap f μ) (Dmap g ν))) P ∎
  where open ≡-Reasoning

independent-cong : (μ μ′ : Dist-ℚ A) (ν ν′ : Dist-ℚ B)
  → μ ≈Mℚ μ′ → ν ≈Mℚ ν′ → independent μ ν ≈Mℚ independent μ′ ν′
independent-cong μ μ′ ν ν′ e h = >>=ᴹ-cong {μ = μ} {ν = μ′}
  {f = λ a → Dmap (a ,_) ν} {g = λ a → Dmap (a ,_) ν′}
  e (λ a → map-cong (a ,_) ν ν′ h)

