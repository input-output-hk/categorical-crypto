{-# OPTIONS --safe --without-K --guardedness #-}

module CategoricalCrypto.Symbolic.RunFollowing.Supply where

open import Data.Empty using (⊥-elim)
open import Data.Nat.Base using (ℕ; zero; suc; _≤_; _⊔_)
import Data.Nat.Properties as Nat
open import Data.Sum.Base
open import Data.Unit.Base
open import Function.Base hiding (_∘_)
open import Function.Definitions using (Injective)
open import Relation.Binary.PropositionalEquality
open import CategoricalCrypto.Symbolic.Term.PairEnc
open import CategoricalCrypto.Symbolic.Fine Σ₀
open import CategoricalCrypto.Symbolic.Semantics Σ₀ E₀ using (Occ)

private variable A B : ObjTerm

bound : (c : HomTerm A B) → (Occ c → ℕ) → ℕ
bound (var _) ι = ι tt
bound id _ = zero
bound (g ∘ f) ι = bound g (ι ∘′ inj₁) ⊔ bound f (ι ∘′ inj₂)
bound (f ⊗₁ g) ι = bound f (ι ∘′ inj₁) ⊔ bound g (ι ∘′ inj₂)
bound λ⇒ _ = zero
bound λ⇐ _ = zero
bound ρ⇒ _ = zero
bound ρ⇐ _ = zero
bound α⇒ _ = zero
bound α⇐ _ = zero
bound (σ ⦃ () ⦄)

bounded : ∀ (c : HomTerm A B) ι o → ι o ≤ bound c ι
bounded (var _) ι tt = Nat.≤-refl
bounded id ι ()
bounded (g ∘ f) ι (inj₁ o) = Nat.≤-trans (bounded g (ι ∘′ inj₁) o) (Nat.m≤m⊔n _ _)
bounded (g ∘ f) ι (inj₂ o) = Nat.≤-trans (bounded f (ι ∘′ inj₂) o) (Nat.m≤n⊔m _ _)
bounded (f ⊗₁ g) ι (inj₁ o) = Nat.≤-trans (bounded f (ι ∘′ inj₁) o) (Nat.m≤m⊔n _ _)
bounded (f ⊗₁ g) ι (inj₂ o) = Nat.≤-trans (bounded g (ι ∘′ inj₂) o) (Nat.m≤n⊔m _ _)
bounded λ⇒ ι ()
bounded λ⇐ ι ()
bounded ρ⇒ ι ()
bounded ρ⇐ ι ()
bounded α⇒ ι ()
bounded α⇐ ι ()
bounded (σ ⦃ () ⦄)

unused : ∀ (c : HomTerm A B) ι o → ι o ≢ suc (bound c ι)
unused c ι o e = Nat.1+n≰n (subst (_≤ bound c ι) e (bounded c ι o))

extend : ∀ {X : Set} → ℕ → (X → ℕ) → X ⊎ ⊤ → ℕ
extend n ι (inj₁ x) = ι x
extend n ι (inj₂ _) = n

extend-injective : ∀ {X : Set} {n} {ι : X → ℕ}
  → Injective _≡_ _≡_ ι → (∀ x → ι x ≢ n) → Injective _≡_ _≡_ (extend n ι)
extend-injective injective fresh {inj₁ x} {inj₁ y} e = cong inj₁ (injective e)
extend-injective injective fresh {inj₁ x} {inj₂ _} e = ⊥-elim (fresh x e)
extend-injective injective fresh {inj₂ _} {inj₁ y} e = ⊥-elim (fresh y (sym e))
extend-injective injective fresh {inj₂ tt} {inj₂ tt} _ = refl
