{-# OPTIONS --safe --without-K #-}

-- Setoid variants of the monad laws

open import categorical-crypto.Prelude

open import Level
open import Class.Core
open import Class.Monad
open import Class.Monad.Ext
open import Class.Prelude using (Typeω)
open import Relation.Binary using (IsEquivalence; Setoid)
import Relation.Binary.Reasoning.Setoid as R-Setoid

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

  ≈ᴹ-setoid : ∀ {ℓ} {A : Type ℓ} → Setoid _ _
  ≈ᴹ-setoid {A = A} = record
    { Carrier       = M A
    ; _≈_           = _≈ᴹ_
    ; isEquivalence = ≈ᴹ-isEquivalence
    }

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

  -- Yoneda variant: with both laws and commutativity in scope.
  >>=-comm-y-≈ : ⦃ MonadLawsSetoid M ⦄
    → {X : Type ℓ} {Y : Type ℓ′} {Z : Type ℓ″}
      {x : M X} {y : M Y} (f : X → Y → M Z)
    → (x >>= λ x′ → y >>= λ y′ → f x′ y′)
    ≈ᴹ (y >>= λ y′ → x >>= λ x′ → f x′ y′)
  >>=-comm-y-≈ {x = x} {y} f = begin
    (x >>= λ x → y >>= λ y → f x y)
      ≈⟨ >>=-cong-f (λ x → >>=-cong-f λ y → ≈ᴹ.sym >>=-identityˡ-≈) ⟩
    (x >>= λ x → y >>= λ y → return (x ,′ y) >>= λ (x , y) → f x y)
      ≈⟨ >>=-cong-f (λ x → ≈ᴹ.sym (>>=-assoc-≈ y)) ⟩
    (x >>= λ x → (y >>= λ y → return (x ,′ y)) >>= λ (x , y) → f x y)
      ≈⟨ ≈ᴹ.sym (>>=-assoc-≈ x) ⟩
    ((x >>= λ x → y >>= λ y → return (x ,′ y)) >>= λ (x , y) → f x y)
      ≈⟨ >>=-cong-x >>=-comm-≈ ⟩
    ((y >>= λ y → x >>= λ x → return (x ,′ y)) >>= λ (x , y) → f x y)
      ≈⟨ >>=-assoc-≈ y ⟩
    (y >>= λ y → (x >>= λ x → return (x ,′ y)) >>= λ (x , y) → f x y)
      ≈⟨ >>=-cong-f (λ y → >>=-assoc-≈ x) ⟩
    (y >>= λ y → x >>= λ x → return (x ,′ y) >>= λ (x , y) → f x y)
      ≈⟨ >>=-cong-f (λ y → >>=-cong-f λ x → >>=-identityˡ-≈) ⟩
    (y >>= λ y → x >>= λ x → f x y) ∎
    where open R-Setoid ≈ᴹ-setoid

open CommutativeMonadSetoid ⦃...⦄ public

------------------------------------------------------------------------
-- Bridge: any monad with propositional MonadLaws + ExtensionalMonad
-- gets a "trivial" setoid (equality is propositional equality), and
-- with CommutativeMonad we get the setoid-commutativity for free.
--
-- This lets users keep using the propositional-equality monads
-- (Maybe, List, …) with code parameterised by MonadSetoid.

module FromPropositional {M : Type↑}
  ⦃ Monad-M       : Monad M            ⦄
  ⦃ M-Laws        : MonadLaws M        ⦄
  ⦃ M-Extensional : ExtensionalMonad M ⦄ where

  open import Relation.Binary.PropositionalEquality
    using (_≡_; refl; isEquivalence)

  Propositional-MonadSetoid : MonadSetoid M
  Propositional-MonadSetoid = record
    { _≈ᴹ_             = _≡_
    ; ≈ᴹ-isEquivalence = isEquivalence
    ; >>=-cong         = _⟩>>=⟨_
    }

  private instance
    Default-MonadSetoid = Propositional-MonadSetoid

  Propositional-MonadLawsSetoid : MonadLawsSetoid M
  Propositional-MonadLawsSetoid = record
    { >>=-identityˡ-≈ = >>=-identityˡ
    ; >>=-identityʳ-≈ = >>=-identityʳ
    ; >>=-assoc-≈     = >>=-assoc
    }

  module _ ⦃ M-Comm : CommutativeMonad M ⦄ where
    Propositional-CommutativeMonadSetoid : CommutativeMonadSetoid M
    Propositional-CommutativeMonadSetoid = record { >>=-comm-≈ = >>=-comm }
