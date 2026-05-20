{-# OPTIONS --safe --without-K #-}

-- Setoid variants of the monad laws

open import categorical-crypto.Prelude

open import Level
open import Class.Core
open import Class.Monad
open import Class.Prelude using (Typeω)
open import Relation.Binary using (IsEquivalence)

module Class.Monad.Ext.Setoid where

private variable ℓ ℓ′ ℓ″ : Level
                 A B : Type ℓ

record MonadSetoid (M : Type↑) ⦃ _ : Monad M ⦄ : Typeω where
  infix 4 _≈ᴹ_
  field
    _≈ᴹ_ : {A : Type ℓ} → M A → M A → Type ℓ

    ≈ᴹ-isEquivalence : {A : Type ℓ} → IsEquivalence (_≈ᴹ_ {A = A})

    >>=-cong : {A : Type ℓ} {B : Type ℓ′} {x y : M A} {f g : A → M B}
             → x ≈ᴹ y → (∀ a → f a ≈ᴹ g a) → (x >>= f) ≈ᴹ (y >>= g)

  module ≈ᴹ {ℓ} {A : Type ℓ} = IsEquivalence (≈ᴹ-isEquivalence {A = A})

  >>=-cong-f : {A : Type ℓ} {B : Type ℓ′} {x : M A} {f g : A → M B}
             → (∀ a → f a ≈ᴹ g a) → (x >>= f) ≈ᴹ (x >>= g)
  >>=-cong-f = >>=-cong ≈ᴹ.refl

  >>=-cong-x : {A : Type ℓ} {B : Type ℓ′} {x y : M A} {f : A → M B}
             → x ≈ᴹ y → (x >>= f) ≈ᴹ (y >>= f)
  >>=-cong-x x≈y = >>=-cong x≈y (λ _ → ≈ᴹ.refl)

open MonadSetoid ⦃...⦄ public

------------------------------------------------------------------------
-- The three monad laws, stated up to the setoid equivalence.

record MonadLawsSetoid (M : Type↑) ⦃ _ : Monad M ⦄ ⦃ _ : MonadSetoid M ⦄ : Typeω where
  field
    >>=-identityˡ-≈ : {A : Type ℓ} {B : Type ℓ′} {a : A} {h : A → M B}
                    → (return a >>= h) ≈ᴹ h a
    >>=-identityʳ-≈ : {A : Type ℓ} (m : M A) → (m >>= return) ≈ᴹ m
    >>=-assoc-≈     : {A : Type ℓ} {B : Type ℓ′} {C : Type ℓ″}
                      (m : M A) {g : A → M B} {h : B → M C}
                    → ((m >>= g) >>= h) ≈ᴹ (m >>= λ x → g x >>= h)
open MonadLawsSetoid ⦃...⦄ public

------------------------------------------------------------------------
-- Commutativity, stated up to the setoid equivalence.

record CommutativeMonadSetoid (M : Type↑) ⦃ _ : Monad M ⦄ ⦃ _ : MonadSetoid M ⦄ : Typeω where
  field
    >>=-comm-≈ : {X : Type ℓ} {Y : Type ℓ′} {x : M X} {y : M Y}
               → (x >>= λ x′ → y >>= λ y′ → return (x′ ,′ y′))
               ≈ᴹ (y >>= λ y′ → x >>= λ x′ → return (x′ , y′))
open CommutativeMonadSetoid ⦃...⦄ public
