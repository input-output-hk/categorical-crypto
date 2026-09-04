{-# OPTIONS --safe --without-K #-}

-- A commutative monad presented elementwise: the raw `return`/`_>>=_` a
-- consumer computes with, and the triple's laws up to `_≈ᴹ_`, the monad's own
-- equality at each type.
--
-- The interface is a record of elements rather than a `KleisliTriple (Setoids
-- ℓ ℓ)` because a monad whose equality quantifies over arbitrary tests on the
-- carrier has no `unit` congruence at a non-discrete setoid, while every
-- consumer below only ever applies the monad at `≡-setoid A`.
-- `Categories.Monad.Setoids.Discrete` derives the same vocabulary from a full
-- triple.

open import Level
open import Data.Product
open import Function.Base
open import Relation.Binary.Bundles
import Relation.Binary.Reasoning.Setoid as R-Setoid

module Categories.Monad.Discrete where

record DiscreteMonad (ℓ : Level) : Set (suc ℓ) where
  infix  4 _≈ᴹ_
  infixl 1 _>>=_
  infixr 1 _<=<_
  infixl 4 _<$>ᴹ_
  field
    ≈ᴹ-setoid : Set ℓ → Setoid ℓ ℓ

  M : Set ℓ → Set ℓ
  M A = Setoid.Carrier (≈ᴹ-setoid A)

  module ≈ᴹ {A : Set ℓ} = Setoid (≈ᴹ-setoid A)

  module ≈ᴹ-Reasoning {A : Set ℓ} = R-Setoid (≈ᴹ-setoid A)

  _≈ᴹ_ : {A : Set ℓ} → M A → M A → Set ℓ
  _≈ᴹ_ {A} = Setoid._≈_ (≈ᴹ-setoid A)

  field
    return : {A : Set ℓ} → A → M A
    _>>=_  : {A B : Set ℓ} → M A → (A → M B) → M B

    >>=-cong : {A B : Set ℓ} {x y : M A} {f g : A → M B}
             → x ≈ᴹ y → (∀ a → f a ≈ᴹ g a) → (x >>= f) ≈ᴹ (y >>= g)
    >>=-identityˡ-≈ : {A B : Set ℓ} {a : A} {h : A → M B} → (return a >>= h) ≈ᴹ h a
    >>=-identityʳ-≈ : {A : Set ℓ} (m : M A) → (m >>= return) ≈ᴹ m
    >>=-assoc-≈ : {A B C : Set ℓ} (m : M A) {g : A → M B} {h : B → M C}
                → ((m >>= g) >>= h) ≈ᴹ (m >>= λ x → g x >>= h)

    -- Commutativity at the *discrete* objects: what a cartesian tensor over
    -- this monad needs and what every instance proves.  The general-setoid
    -- form is strictly stronger, and upstream's `Categories.Monad.Commutative`
    -- needs a strength.
    >>=-comm : {A B : Set ℓ} {x : M A} {y : M B}
             → (x >>= λ a → y >>= λ b → return (a , b))
             ≈ᴹ (y >>= λ b → x >>= λ a → return (a , b))

  _<=<_ : {A B C : Set ℓ} → (B → M C) → (A → M B) → A → M C
  (g <=< f) a = f a >>= g

  _<$>ᴹ_ : {A B : Set ℓ} → (A → B) → M A → M B
  h <$>ᴹ m = m >>= (return ∘ h)

  >>=-cong-f : {A B : Set ℓ} {x : M A} {f g : A → M B}
             → (∀ a → f a ≈ᴹ g a) → (x >>= f) ≈ᴹ (x >>= g)
  >>=-cong-f = >>=-cong ≈ᴹ.refl

  >>=-cong-x : {A B : Set ℓ} {x y : M A} {f : A → M B} → x ≈ᴹ y → (x >>= f) ≈ᴹ (y >>= f)
  >>=-cong-x x≈y = >>=-cong x≈y λ _ → ≈ᴹ.refl

  <$>ᴹ-cong : {A B : Set ℓ} {h : A → B} {m n : M A} → m ≈ᴹ n → (h <$>ᴹ m) ≈ᴹ (h <$>ᴹ n)
  <$>ᴹ-cong = >>=-cong-x

  <$>ᴹ->>= : {A B C : Set ℓ} (h : A → B) (m : M A) (g : B → M C)
           → ((h <$>ᴹ m) >>= g) ≈ᴹ (m >>= (g ∘ h))
  <$>ᴹ->>= h m g = ≈ᴹ.trans (>>=-assoc-≈ m) (>>=-cong-f λ _ → >>=-identityˡ-≈)

  <$>ᴹ-∘ : {A B C : Set ℓ} (k : B → C) (h : A → B) (m : M A)
         → (k <$>ᴹ (h <$>ᴹ m)) ≈ᴹ ((k ∘ h) <$>ᴹ m)
  <$>ᴹ-∘ k h m = <$>ᴹ->>= h m (return ∘ k)

  >>=-<$>ᴹ : {A B C : Set ℓ} (h : B → C) (m : M A) (g : A → M B)
           → (h <$>ᴹ (m >>= g)) ≈ᴹ (m >>= λ a → h <$>ᴹ g a)
  >>=-<$>ᴹ h m g = >>=-assoc-≈ m

  -- Yoneda variant of `>>=-comm`
  >>=-comm-y : {A B C : Set ℓ} {x : M A} {y : M B} (f : A → B → M C)
             → (x >>= λ a → y >>= f a) ≈ᴹ (y >>= λ b → x >>= λ a → f a b)
  >>=-comm-y {x = x} {y} f = begin
    (x >>= λ a → y >>= λ b → f a b)
      ≈⟨ >>=-cong-f (λ _ → >>=-cong-f λ _ → ≈ᴹ.sym >>=-identityˡ-≈) ⟩
    (x >>= λ a → y >>= λ b → return (a ,′ b) >>= λ (a , b) → f a b)
      ≈⟨ >>=-cong-f (λ _ → ≈ᴹ.sym (>>=-assoc-≈ y)) ⟩
    (x >>= λ a → (y >>= λ b → return (a ,′ b)) >>= λ (a , b) → f a b)
      ≈⟨ ≈ᴹ.sym (>>=-assoc-≈ x) ⟩
    ((x >>= λ a → y >>= λ b → return (a ,′ b)) >>= λ (a , b) → f a b)
      ≈⟨ >>=-cong-x >>=-comm ⟩
    ((y >>= λ b → x >>= λ a → return (a ,′ b)) >>= λ (a , b) → f a b)
      ≈⟨ >>=-assoc-≈ y ⟩
    (y >>= λ b → (x >>= λ a → return (a ,′ b)) >>= λ (a , b) → f a b)
      ≈⟨ >>=-cong-f (λ _ → >>=-assoc-≈ x) ⟩
    (y >>= λ b → x >>= λ a → return (a ,′ b) >>= λ (a , b) → f a b)
      ≈⟨ >>=-cong-f (λ _ → >>=-cong-f λ _ → >>=-identityˡ-≈) ⟩
    (y >>= λ b → x >>= λ a → f a b) ∎
    where open ≈ᴹ-Reasoning
