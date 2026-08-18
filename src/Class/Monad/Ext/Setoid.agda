{-# OPTIONS --safe --without-K #-}

open import categorical-crypto.Prelude

open import Class.Core
open import Class.Monad
open import Class.Monad.Ext
open import Class.Prelude using (Typeω)
open import Data.Maybe.Relation.Binary.Pointwise as Pw using (Pointwise)
open import Data.Product.Relation.Binary.Pointwise.NonDependent using (×-setoid)
open import Function.Bundles using (Func; _⟨$⟩_)
open import Relation.Binary
open import Relation.Binary.Bundles.Ext
open import Relation.Binary.PropositionalEquality.Properties using () renaming (setoid to ≡-setoid)
import Relation.Binary.Reasoning.Setoid as R-Setoid

module Class.Monad.Ext.Setoid where

open Setoid using (Carrier)

private variable ℓ ℓ′ ℓ″ : Level
                 A B : Type ℓ

infixl 4 _<$>ᴹ_
_<$>ᴹ_ : {M : Type↑} ⦃ _ : Monad M ⦄ {A : Type ℓ} {B : Type ℓ′} → (A → B) → M A → M B
h <$>ᴹ m = m >>= (return ∘ h)

record MonadSetoid (M : Type↑) ⦃ _ : Monad M ⦄ : Typeω where
  infix  4 _≈ᴹ_
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

-- Not a `GradedMonadMorphism`: that presupposes a `GradedMonad`, i.e. an honest
-- endofunctor, which `M` is not — its laws hold only up to `_≈ᴹ_`, never up to
-- an equality on functions as `Sets` needs, and `_≈ᴹ_` is fixed by the carrier
-- alone, so `_<$>ᴹ_` cannot respect a `Setoids` object's own equality either.
-- `SetoidMonadMorphism` below is the same notion over the setoid-indexed
-- equality, and `Class.Monad.Ext.Setoid.Graded` does exhibit *it* as one.
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

  θ-<$>ᴹ : {A : Type ℓ} {B : Type ℓ′} (h : A → B) (m : M A) → θ (h <$>ᴹ m) ≈ᴹ (h <$>ᴹ θ m)
  θ-<$>ᴹ h m = N≈.≈ᴹ.trans (θ-bind m _) (N≈.>>=-cong-f λ _ → θ-return _)

-- Propositional monads can be turned into setoid monads
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

------------------------------------------------------------------------
-- Setoid-indexed monads
------------------------------------------------------------------------

-- `MonadSetoid`'s `_≈ᴹ_` is fixed by the carrier of `A`, so it has no equality
-- on `B` to compare `h` and `k` up to: `<$>ᴹ-congˡ` can only ask them to agree
-- propositionally, and the map-congruence proper is not even statable.  Indexing
-- the equality by a setoid *on* `A` states it as `<$>ᴹ-congˢˡ`, and makes `M` an
-- honest monad on `Setoids`; `Class.Monad.Ext.Setoid.Graded` builds it.
record SetoidMonad (M : Type↑) ⦃ _ : Monad M ⦄ : Typeω where
  infix 4 _⟨_≈ˢ_⟩
  field
    _⟨_≈ˢ_⟩ : (S : Setoid ℓ ℓ) → Rel (M (Carrier S)) ℓ

    ≈ˢ-isEquivalence : {S : Setoid ℓ ℓ} → IsEquivalence (S ⟨_≈ˢ_⟩)

    -- `return` is a setoid function …
    return-congˢ : {S : Setoid ℓ ℓ} {a b : Carrier S} → S ⟨ a ≈ b ⟩ → S ⟨ return a ≈ˢ return b ⟩

    -- … and `_>>=_` is congruent in both of its arguments at once.
    >>=-congˢ : {S : Setoid ℓ ℓ} {S′ : Setoid ℓ′ ℓ′}
                {x y : M (Carrier S)} {f g : Carrier S → M (Carrier S′)}
              → S ⟨ x ≈ˢ y ⟩ → (∀ {a b} → S ⟨ a ≈ b ⟩ → S′ ⟨ f a ≈ˢ g b ⟩)
              → S′ ⟨ (x >>= f) ≈ˢ (y >>= g) ⟩

  module ≈ˢ {ℓ} {S : Setoid ℓ ℓ} = IsEquivalence (≈ˢ-isEquivalence {S = S})

  ≈ˢ-setoid : Setoid ℓ ℓ → Setoid ℓ ℓ
  ≈ˢ-setoid S = record
    { Carrier       = M (Carrier S)
    ; _≈_           = S ⟨_≈ˢ_⟩
    ; isEquivalence = ≈ˢ-isEquivalence {S = S}
    }

  -- `Carrier` and `Setoid._≈_` pin down neither the setoid nor its level, so
  -- every setoid argument below is passed by name rather than left to unify.
  returnˢ : {S : Setoid ℓ ℓ} → Func S (≈ˢ-setoid S)
  returnˢ {S = S} = record { to = return ; cong = return-congˢ {S = S} }

  bindˢ : {S : Setoid ℓ ℓ} {S′ : Setoid ℓ′ ℓ′}
        → Func S (≈ˢ-setoid S′) → Func (≈ˢ-setoid S) (≈ˢ-setoid S′)
  bindˢ {S = S} {S′ = S′} f = record
    { to   = _>>= (f ⟨$⟩_)
    ; cong = λ x≈y → >>=-congˢ {S = S} {S′ = S′} x≈y (Func.cong f)
    }

  -- Congruence of `bindˢ` in both arguments at once: in the value argument alone
  -- it is `bindˢ f`'s own `cong`.
  bindˢ-cong : {S : Setoid ℓ ℓ} {S′ : Setoid ℓ′ ℓ′} {f g : Func S (≈ˢ-setoid S′)}
             → (∀ a → S′ ⟨ f ⟨$⟩ a ≈ˢ g ⟨$⟩ a ⟩)
             → {x y : M (Carrier S)} → S ⟨ x ≈ˢ y ⟩
             → S′ ⟨ (bindˢ f ⟨$⟩ x) ≈ˢ (bindˢ g ⟨$⟩ y) ⟩
  bindˢ-cong {S = S} {S′ = S′} {f = f} f≈g x≈y =
    >>=-congˢ {S = S} {S′ = S′} x≈y λ {_} {b} a≈b →
      ≈ˢ.trans {S = S′} (Func.cong f a≈b) (f≈g b)

  -- The law `MonadSetoid` cannot state: `_<$>ᴹ_` respects `S′`'s own equality,
  -- not just `_≗_`.  It is the endofunctor's `F-resp-≈`.
  <$>ᴹ-congˢˡ : {S : Setoid ℓ ℓ} {S′ : Setoid ℓ′ ℓ′} {h k : Carrier S → Carrier S′}
               → (∀ {a b} → S ⟨ a ≈ b ⟩ → S′ ⟨ h a ≈ k b ⟩)
               → (x : M (Carrier S)) → S′ ⟨ (h <$>ᴹ x) ≈ˢ (k <$>ᴹ x) ⟩
  <$>ᴹ-congˢˡ {S = S} {S′ = S′} h≈k _ =
    >>=-congˢ {S = S} {S′ = S′} (≈ˢ.refl {S = S}) (return-congˢ ∘ h≈k)

  <$>ᴹ-congˢ : {S : Setoid ℓ ℓ} {S′ : Setoid ℓ′ ℓ′} {h : Carrier S → Carrier S′}
               {x y : M (Carrier S)}
             → (∀ {a b} → S ⟨ a ≈ b ⟩ → S′ ⟨ h a ≈ h b ⟩)
             → S ⟨ x ≈ˢ y ⟩ → S′ ⟨ (h <$>ᴹ x) ≈ˢ (h <$>ᴹ y) ⟩
  <$>ᴹ-congˢ {S = S} {S′ = S′} h-cong x≈y =
    >>=-congˢ {S = S} {S′ = S′} x≈y (return-congˢ ∘ h-cong)

open SetoidMonad ⦃...⦄ public

record SetoidMonadLaws (M : Type↑) ⦃ _ : Monad M ⦄ ⦃ _ : SetoidMonad M ⦄ : Typeω where
  field
    >>=-identityˡ-≈ˢ : {S : Setoid ℓ ℓ} {S′ : Setoid ℓ′ ℓ′}
                       {a : Carrier S} {h : Carrier S → M (Carrier S′)}
                     → S′ ⟨ (return a >>= h) ≈ˢ h a ⟩
    >>=-identityʳ-≈ˢ : {S : Setoid ℓ ℓ} (m : M (Carrier S)) → S ⟨ (m >>= return) ≈ˢ m ⟩
    >>=-assoc-≈ˢ     : {S : Setoid ℓ ℓ} {S′ : Setoid ℓ′ ℓ′} {S″ : Setoid ℓ″ ℓ″}
                       (m : M (Carrier S)) {g : Carrier S → M (Carrier S′)}
                       {h : Carrier S′ → M (Carrier S″)}
                     → S″ ⟨ ((m >>= g) >>= h) ≈ˢ (m >>= λ x → g x >>= h) ⟩
open SetoidMonadLaws ⦃...⦄ public

record CommutativeSetoidMonad (M : Type↑) ⦃ _ : Monad M ⦄ ⦃ _ : SetoidMonad M ⦄ : Typeω where
  field
    -- Taken in the Yoneda form, which names the setoid the two sides are
    -- compared at; in the pair form `>>=-comm-pairˢ` that setoid is forced to
    -- be a product, which is not what the ≡-discrete case needs.
    >>=-comm-≈ˢ : {S : Setoid ℓ ℓ} {S′ : Setoid ℓ′ ℓ′} {S″ : Setoid ℓ″ ℓ″}
                  {x : M (Carrier S)} {y : M (Carrier S′)}
                  {f : Carrier S → Carrier S′ → M (Carrier S″)}
                → (∀ {a a′ b b′} → S ⟨ a ≈ a′ ⟩ → S′ ⟨ b ≈ b′ ⟩ → S″ ⟨ f a b ≈ˢ f a′ b′ ⟩)
                → S″ ⟨ (x >>= λ a → y >>= f a) ≈ˢ (y >>= λ b → x >>= λ a → f a b) ⟩

  >>=-comm-pairˢ : {S : Setoid ℓ ℓ} {S′ : Setoid ℓ′ ℓ′}
                   {x : M (Carrier S)} {y : M (Carrier S′)}
                 → ×-setoid S S′ ⟨ (x >>= λ a → y >>= λ b → return (a ,′ b))
                                ≈ˢ (y >>= λ b → x >>= λ a → return (a , b)) ⟩
  >>=-comm-pairˢ {S = S} {S′ = S′} =
    >>=-comm-≈ˢ {S = S} {S′ = S′} {S″ = ×-setoid S S′} λ a≈a′ b≈b′ →
      return-congˢ (a≈a′ , b≈b′)
open CommutativeSetoidMonad ⦃...⦄ public

record SetoidMonadMorphism (M N : Type↑)
  ⦃ _ : Monad M ⦄ ⦃ SM-M : SetoidMonad M ⦄
  ⦃ _ : Monad N ⦄ ⦃ SM-N : SetoidMonad N ⦄ : Typeω where
  field
    θ        : {A : Type ℓ} → M A → N A
    θ-congˢ  : {S : Setoid ℓ ℓ} {x y : M (Carrier S)} → S ⟨ x ≈ˢ y ⟩ → S ⟨ θ x ≈ˢ θ y ⟩
    θ-return : {S : Setoid ℓ ℓ} (a : Carrier S) → S ⟨ θ (return a) ≈ˢ return a ⟩
    θ-bind   : {S : Setoid ℓ ℓ} {S′ : Setoid ℓ′ ℓ′}
               (m : M (Carrier S)) (k : Carrier S → M (Carrier S′))
             → S′ ⟨ θ (m >>= k) ≈ˢ (θ m >>= (θ ∘ k)) ⟩

  private
    module M≈ = SetoidMonad SM-M
    module N≈ = SetoidMonad SM-N

  θˢ : {S : Setoid ℓ ℓ} → Func (M≈.≈ˢ-setoid S) (N≈.≈ˢ-setoid S)
  θˢ {S = S} = record { to = θ ; cong = θ-congˢ {S = S} }

-- `MonadSetoid` is `SetoidMonad` with the index pinned to `≡-setoid`: pinning it
-- loses nothing, and there is no way back, since an equality fixed by the
-- carrier of `A` cannot see an equality on `A` it was never given.
module Discrete {M : Type↑} ⦃ _ : Monad M ⦄ ⦃ SM : SetoidMonad M ⦄ where

  Discrete-MonadSetoid : MonadSetoid M
  Discrete-MonadSetoid = record
    { _≈ᴹ_             = λ {A = A} → _⟨_≈ˢ_⟩ (≡-setoid A)
    ; ≈ᴹ-isEquivalence = λ {A = A} → ≈ˢ-isEquivalence {S = ≡-setoid A}
    ; >>=-cong         = λ {A = A} {B = B} x≈y f≈g →
        >>=-congˢ {S = ≡-setoid A} {S′ = ≡-setoid B} x≈y λ where refl → f≈g _
    }

  private instance
    Default-MonadSetoid = Discrete-MonadSetoid

  Discrete-MonadLawsSetoid : ⦃ SetoidMonadLaws M ⦄ → MonadLawsSetoid M
  Discrete-MonadLawsSetoid = record
    { >>=-identityˡ-≈ = λ {A = A} {B = B} → >>=-identityˡ-≈ˢ {S = ≡-setoid A} {≡-setoid B}
    ; >>=-identityʳ-≈ = λ {A = A} → >>=-identityʳ-≈ˢ {S = ≡-setoid A}
    ; >>=-assoc-≈     = λ {A = A} {B = B} {C = C} →
        >>=-assoc-≈ˢ {S = ≡-setoid A} {≡-setoid B} {≡-setoid C}
    }

  Discrete-CommutativeMonadSetoid : ⦃ CommutativeSetoidMonad M ⦄ → CommutativeMonadSetoid M
  Discrete-CommutativeMonadSetoid = record
    { >>=-comm-≈ = λ {X = X} {Y = Y} →
        >>=-comm-≈ˢ {S = ≡-setoid X} {≡-setoid Y} {≡-setoid (X × Y)}
                    (λ where refl refl → ≈ˢ.refl)
    }

-- `Maybe` up to the element setoid: the interface's second instance, and what
-- `Class.Monad.Ext.Setoid.Test`'s monad morphism goes out of.  Left for the
-- consumer to declare as an instance, as `FromPropositional` is: a `SetoidMonad`
-- in scope for a concrete `M` competes with the parameter of every module that
-- abstracts over one.
module PointwiseMaybe where

  private
    ≈ᴹᵇ : (S : Setoid ℓ ℓ) → Rel (Maybe (Carrier S)) ℓ
    ≈ᴹᵇ S = Pointwise (Setoid._≈_ S)

    >>=-congᴹᵇ : {S : Setoid ℓ ℓ} {S′ : Setoid ℓ′ ℓ′}
                 {x y : Maybe (Carrier S)} {f g : Carrier S → Maybe (Carrier S′)}
               → ≈ᴹᵇ S x y → (∀ {a b} → S ⟨ a ≈ b ⟩ → ≈ᴹᵇ S′ (f a) (g b))
               → ≈ᴹᵇ S′ (x >>= f) (y >>= g)
    >>=-congᴹᵇ (Pw.just a≈b) f≈g = f≈g a≈b
    >>=-congᴹᵇ Pw.nothing    _   = Pw.nothing

    >>=-commᴹᵇ : {S : Setoid ℓ ℓ} {S′ : Setoid ℓ′ ℓ′} {S″ : Setoid ℓ″ ℓ″}
                 (x : Maybe (Carrier S)) (y : Maybe (Carrier S′))
                 (f : Carrier S → Carrier S′ → Maybe (Carrier S″))
               → ≈ᴹᵇ S″ (x >>= λ a → y >>= f a) (y >>= λ b → x >>= λ a → f a b)
    >>=-commᴹᵇ {S″ = S″} (just _) (just _) _ = Pw.refl (Setoid.refl S″)
    >>=-commᴹᵇ (just _)  nothing  _ = Pw.nothing
    >>=-commᴹᵇ nothing   (just _) _ = Pw.nothing
    >>=-commᴹᵇ nothing   nothing  _ = Pw.nothing

  Pointwise-SetoidMonad : SetoidMonad Maybe
  Pointwise-SetoidMonad = record
    { _⟨_≈ˢ_⟩          = ≈ᴹᵇ
    ; ≈ˢ-isEquivalence = λ {S = S} → Pw.isEquivalence (Setoid.isEquivalence S)
    ; return-congˢ     = Pw.just
    ; >>=-congˢ        = λ {S = S} {S′ = S′} → >>=-congᴹᵇ {S = S} {S′ = S′}
    }

  private instance
    Default-SetoidMonad = Pointwise-SetoidMonad

  Pointwise-SetoidMonadLaws : SetoidMonadLaws Maybe
  Pointwise-SetoidMonadLaws = record
    { >>=-identityˡ-≈ˢ = λ {S′ = S′} → Pw.refl (Setoid.refl S′)
    ; >>=-identityʳ-≈ˢ = λ {S = S} → λ where
        (just _) → Pw.just (Setoid.refl S)
        nothing  → Pw.nothing
    ; >>=-assoc-≈ˢ     = λ {S″ = S″} → λ where
        (just _) → Pw.refl (Setoid.refl S″)
        nothing  → Pw.nothing
    }

  Pointwise-CommutativeSetoidMonad : CommutativeSetoidMonad Maybe
  Pointwise-CommutativeSetoidMonad = record
    { >>=-comm-≈ˢ = λ {S = S} {S′ = S′} {S″ = S″} {x = x} {y = y} {f = f} _ →
        >>=-commᴹᵇ {S = S} {S′ = S′} {S″ = S″} x y f
    }
