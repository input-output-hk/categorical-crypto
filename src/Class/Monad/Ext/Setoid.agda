{-# OPTIONS --safe --without-K #-}

open import categorical-crypto.Prelude

open import Class.Core
open import Class.Monad
open import Class.Monad.Ext
open import Class.Prelude using (Typeω)
open import Relation.Binary
import Relation.Binary.Reasoning.Setoid as R-Setoid

module Class.Monad.Ext.Setoid where

private variable ℓ ℓ′ ℓ″ : Level
                 A B : Type ℓ

record MonadSetoid (M : Type↑) ⦃ _ : Monad M ⦄ : Typeω where
  infix  4 _≈ᴹ_
  infixl 4 _<$>ᴹ_
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

  _<$>ᴹ_ : {A : Type ℓ} {B : Type ℓ′} → (A → B) → M A → M B
  h <$>ᴹ m = m >>= (return ∘ h)

  <$>ᴹ-cong : {A : Type ℓ} {B : Type ℓ′} {h : A → B} {m n : M A}
            → m ≈ᴹ n → (h <$>ᴹ m) ≈ᴹ (h <$>ᴹ n)
  <$>ᴹ-cong = >>=-cong-x

  <$>ᴹ-congˡ : {A : Type ℓ} {B : Type ℓ′} {h k : A → B} (m : M A)
             → h ≗ k → (h <$>ᴹ m) ≈ᴹ (k <$>ᴹ m)
  <$>ᴹ-congˡ m h≗k = >>=-cong-f λ a → ≈ᴹ.reflexive (cong return (h≗k a))

open MonadSetoid ⦃...⦄ public

record MonadLawsSetoid (M : Type↑) ⦃ _ : Monad M ⦄ ⦃ _ : MonadSetoid M ⦄ : Typeω where
  field
    >>=-identityˡ-≈ : {A : Type ℓ} {B : Type ℓ′} {a : A} {h : A → M B}
                    → (return a >>= h) ≈ᴹ h a
    >>=-identityʳ-≈ : {A : Type ℓ} (m : M A) → (m >>= return) ≈ᴹ m
    >>=-assoc-≈     : {A : Type ℓ} {B : Type ℓ′} {C : Type ℓ″}
                      (m : M A) {g : A → M B} {h : B → M C}
                    → ((m >>= g) >>= h) ≈ᴹ (m >>= λ x → g x >>= h)

  <$>ᴹ->>= : {A : Type ℓ} {B : Type ℓ′} {C : Type ℓ″}
             (h : A → B) (m : M A) (g : B → M C)
           → ((h <$>ᴹ m) >>= g) ≈ᴹ (m >>= (g ∘ h))
  <$>ᴹ->>= h m g = ≈ᴹ.trans (>>=-assoc-≈ m) (>>=-cong-f λ _ → >>=-identityˡ-≈)

  <$>ᴹ-∘ : {A : Type ℓ} {B : Type ℓ′} {C : Type ℓ″}
           (k : B → C) (h : A → B) (m : M A)
         → (k <$>ᴹ (h <$>ᴹ m)) ≈ᴹ ((k ∘ h) <$>ᴹ m)
  <$>ᴹ-∘ k h m = <$>ᴹ->>= h m (return ∘ k)

  >>=-<$>ᴹ : {A : Type ℓ} {B : Type ℓ′} {C : Type ℓ″}
             (h : B → C) (m : M A) (g : A → M B)
           → (h <$>ᴹ (m >>= g)) ≈ᴹ (m >>= λ a → h <$>ᴹ g a)
  >>=-<$>ᴹ h m g = >>=-assoc-≈ m
open MonadLawsSetoid ⦃...⦄ public

record CommutativeMonadSetoid (M : Type↑) ⦃ _ : Monad M ⦄ ⦃ _ : MonadSetoid M ⦄ : Typeω where
  field
    >>=-comm-≈ : {X : Type ℓ} {Y : Type ℓ′} {x : M X} {y : M Y}
               → (x >>= λ x′ → y >>= λ y′ → return (x′ ,′ y′))
               ≈ᴹ (y >>= λ y′ → x >>= λ x′ → return (x′ , y′))

  -- Yoneda variant
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

-- `Categories.Monad.Morphism.Monad⇒-id` is this notion for a `Categories.Monad`
-- on a category, i.e. in the (η , μ)-presentation; there is no bridge from a
-- `Type↑` with a `_≈ᴹ_` to that, so state it in the presentation used here.
record MonadMorphismSetoid (M N : Type↑)
  ⦃ _ : Monad M ⦄ ⦃ _ : MonadSetoid M ⦄
  ⦃ _ : Monad N ⦄ ⦃ MS-N : MonadSetoid N ⦄ : Typeω where
  field
    θ        : {A : Type ℓ} → M A → N A
    θ-cong   : {A : Type ℓ} {x y : M A} → x ≈ᴹ y → θ x ≈ᴹ θ y
    θ-return : {A : Type ℓ} (a : A) → θ (return {A = A} a) ≈ᴹ return a
    θ-bind   : {A : Type ℓ} {B : Type ℓ′} (m : M A) (k : A → M B)
             → θ (m >>= k) ≈ᴹ (θ m >>= λ a → θ (k a))

  private module N≈ = MonadSetoid MS-N

  θ-<$>ᴹ : {A : Type ℓ} {B : Type ℓ′} (h : A → B) (m : M A)
         → θ (h <$>ᴹ m) ≈ᴹ (h N≈.<$>ᴹ θ m)
  θ-<$>ᴹ h m = N≈.≈ᴹ.trans (θ-bind m _) (N≈.>>=-cong-f λ _ → θ-return _)

module FromPropositional {M : Type↑}
  ⦃ Monad-M       : Monad M            ⦄
  ⦃ M-Laws        : MonadLaws M        ⦄
  ⦃ M-Extensional : ExtensionalMonad M ⦄ where

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
