{-# OPTIONS --safe --without-K #-}

-- A monad on `Setoids` viewed elementwise at the discrete setoids: the raw
-- `return`/`_>>=_` the machine layer computes with, and the triple's laws up to
-- `_≈ᴹ_`, the monad's own equality at `≡-setoid A`.  Everything here is a
-- rearrangement of a `KleisliTriple` field; the notion itself is upstream.

open import Level

open import Categories.Category
open import Categories.Category.Construction.Kleisli
open import Categories.Category.Instance.Setoids
open import Categories.Category.SubCategory
open import Categories.Monad.Construction.Kleisli
open import Categories.Monad.Construction.Kleisli.Ext
open import Categories.Monad.Relative using () renaming (Monad to RMonad)

open import Data.Product
open import Function.Base
open import Function.Bundles
open import Function.Bundles.Ext
open import Relation.Binary.Bundles
open import Relation.Binary.PropositionalEquality.Properties using () renaming (setoid to ≡-setoid)
import Relation.Binary.Reasoning.Setoid as R-Setoid

module Categories.Monad.Setoids.Discrete {ℓ} (K : KleisliTriple (Setoids ℓ ℓ)) where

private
  module K = RMonad K

  variable A B C : Set ℓ

≈ᴹ-setoid : Set ℓ → Setoid ℓ ℓ
≈ᴹ-setoid A = K.F₀ (≡-setoid A)

module ≈ᴹ {A : Set ℓ} = Setoid (≈ᴹ-setoid A)

module ≈ᴹ-Reasoning {A : Set ℓ} = R-Setoid (≈ᴹ-setoid A)

M : Set ℓ → Set ℓ
M A = Setoid.Carrier (≈ᴹ-setoid A)

infix  4 _≈ᴹ_
infixl 1 _>>=_
infixr 1 _<=<_
infixl 4 _<$>ᴹ_

_≈ᴹ_ : M A → M A → Set ℓ
_≈ᴹ_ {A} = Setoid._≈_ (≈ᴹ-setoid A)

return : A → M A
return = K.unit ⟨$⟩_

_>>=_ : M A → (A → M B) → M B
x >>= f = K.extend (discreteFunc f) ⟨$⟩ x

_<=<_ : (B → M C) → (A → M B) → A → M C
(g <=< f) a = f a >>= g

_<$>ᴹ_ : (A → B) → M A → M B
h <$>ᴹ m = m >>= (return ∘ h)

------------------------------------------------------------------------
-- The laws
------------------------------------------------------------------------

>>=-cong : {x y : M A} {f g : A → M B}
         → x ≈ᴹ y → (∀ a → f a ≈ᴹ g a) → (x >>= f) ≈ᴹ (y >>= g)
>>=-cong {f = f} x≈y f≈g =
  ≈ᴹ.trans (Func.cong (K.extend (discreteFunc f)) x≈y) (K.extend-≈ λ {a} → f≈g a)

>>=-cong-f : {x : M A} {f g : A → M B} → (∀ a → f a ≈ᴹ g a) → (x >>= f) ≈ᴹ (x >>= g)
>>=-cong-f = >>=-cong ≈ᴹ.refl

>>=-cong-x : {x y : M A} {f : A → M B} → x ≈ᴹ y → (x >>= f) ≈ᴹ (y >>= f)
>>=-cong-x x≈y = >>=-cong x≈y λ _ → ≈ᴹ.refl

<$>ᴹ-cong : {h : A → B} {m n : M A} → m ≈ᴹ n → (h <$>ᴹ m) ≈ᴹ (h <$>ᴹ n)
<$>ᴹ-cong = >>=-cong-x

>>=-identityˡ-≈ : {a : A} {h : A → M B} → (return a >>= h) ≈ᴹ h a
>>=-identityˡ-≈ = K.identityʳ

-- `extend` is applied to `discreteFunc return` here and to the triple's own
-- `unit` in `identityˡ`: the two agree pointwise, not as records.
>>=-identityʳ-≈ : (m : M A) → (m >>= return) ≈ᴹ m
>>=-identityʳ-≈ _ = ≈ᴹ.trans (K.extend-≈ {h = K.unit} ≈ᴹ.refl) K.identityˡ

>>=-assoc-≈ : (m : M A) {g : A → M B} {h : B → M C}
            → ((m >>= g) >>= h) ≈ᴹ (m >>= λ x → g x >>= h)
>>=-assoc-≈ _ = ≈ᴹ.trans K.sym-assoc (K.extend-≈ ≈ᴹ.refl)

<$>ᴹ->>= : (h : A → B) (m : M A) (g : B → M C) → ((h <$>ᴹ m) >>= g) ≈ᴹ (m >>= (g ∘ h))
<$>ᴹ->>= h m g = ≈ᴹ.trans (>>=-assoc-≈ m) (>>=-cong-f λ _ → >>=-identityˡ-≈)

<$>ᴹ-∘ : (k : B → C) (h : A → B) (m : M A) → (k <$>ᴹ (h <$>ᴹ m)) ≈ᴹ ((k ∘ h) <$>ᴹ m)
<$>ᴹ-∘ k h m = <$>ᴹ->>= h m (return ∘ k)

>>=-<$>ᴹ : (h : B → C) (m : M A) (g : A → M B)
         → (h <$>ᴹ (m >>= g)) ≈ᴹ (m >>= λ a → h <$>ᴹ g a)
>>=-<$>ᴹ h m g = >>=-assoc-≈ m

-- Commutativity at the *discrete* setoids: what the machine layer needs and what every
-- instance proves.  The general-setoid form is strictly stronger (nothing makes `F₀ S`
-- reachable from `F₀ (≡-setoid ⟦S⟧)`), so assuming it would narrow every law that runs
-- through `trace-∘`; upstream's `Categories.Monad.Commutative` needs a strength.
record Commutative : Set (suc ℓ) where
  field
    >>=-comm : {A B : Set ℓ} {x : M A} {y : M B}
             → (x >>= λ a → y >>= λ b → return (a ,′ b))
             ≈ᴹ (y >>= λ b → x >>= λ a → return (a , b))

  -- Yoneda variant
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

------------------------------------------------------------------------
-- The Kleisli category
------------------------------------------------------------------------

-- The discrete objects of `Kleisli`: `A ⇒ B` is a map `A → M B`, up to `_≈ᴹ_`.
Kleisliᴹ : Category (suc ℓ) ℓ ℓ
Kleisliᴹ = FullSubCategory (Kleisli (Kleisli⇒Monad (Setoids ℓ ℓ) K)) ≡-setoid

private module Kl = Category Kleisliᴹ

-- `Kleisliᴹ` composes through `μ ∘ F₁ g`, which is `_>>=_` only up to `_≈ᴹ_`.
∘ᴹ-bind : {f : Kleisliᴹ [ A , B ]} {g : Kleisliᴹ [ B , C ]} (a : A)
        → ((g Kl.∘ f) ⟨$⟩ a) ≈ᴹ ((f ⟨$⟩ a) >>= (g ⟨$⟩_))
∘ᴹ-bind {g = g} _ = ≈ᴹ.trans (extend-μ (Setoids ℓ ℓ) K g) (K.extend-≈ ≈ᴹ.refl)

