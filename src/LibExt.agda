{-# OPTIONS --safe --without-K #-}

module LibExt where

open import categorical-crypto.Prelude hiding (take ; _++_ ; _/_)
open import Relation.Binary
open import Data.Vec
open import Categories.Category
open import Categories.Category.Helper
import Relation.Binary.Reasoning.Setoid as SetoidReasoning

------------------------------------------------------------------------
-- Arithmetic: lemmas about ℕ, ℤ and ℚ that are missing from std-lib.

module Arith where
  import Data.Nat as ℕ
  open import Data.Nat.Divisibility using (∣-antisym; ∣-refl)
  open import Data.Nat.GCD using (gcd[m,n]∣m; gcd-greatest)
    renaming (gcd to ℕgcd)
  open import Data.Integer using (ℤ; +_)
    renaming (_*_ to _*ℤ_; ≢-nonZero to ℤ-≢-nonZero)
  open import Data.Integer.GCD using () renaming (gcd to ℤgcd)
  import Data.Integer.Properties as ℤP
  open import Data.Rational using (ℚ; _/_; ↥_; ↧_; *≡*; 1ℚ)
  open import Data.Rational.Properties using (≃⇒≡; ↥-/; ↧-/)

  gcd-self-ℕ : ∀ n → ℕgcd n n ≡ n
  gcd-self-ℕ n = ∣-antisym (gcd[m,n]∣m n n) (gcd-greatest ∣-refl ∣-refl)

  gcd-self-ℤ : ∀ n → ℤgcd (+ n) (+ n) ≡ + n
  gcd-self-ℤ n = cong +_ (gcd-self-ℕ n)

  gcd[+n,+n]≢0 : ∀ n .{{_ : ℕ.NonZero n}} → ℤgcd (+ n) (+ n) ≢ + 0
  gcd[+n,+n]≢0 n@(suc _) eq with () ← trans (sym (gcd-self-ℤ n)) eq

  n/n≡1ℚ : ∀ n .{{_ : ℕ.NonZero n}} → ((+ n) / n) ≡ 1ℚ
  n/n≡1ℚ n@(suc _) = ≃⇒≡ (*≡* eq)
    where
      g = ℤgcd (+ n) (+ n)

      ↥g≡↧g : (↥ ((+ n) / n)) *ℤ g ≡ (↧ ((+ n) / n)) *ℤ g
      ↥g≡↧g = trans (↥-/ (+ n) n) (sym (↧-/ (+ n) n))

      ↥≡↧ : ↥ ((+ n) / n) ≡ ↧ ((+ n) / n)
      ↥≡↧ = ℤP.*-cancelʳ-≡ _ _ g {{ℤ-≢-nonZero (gcd[+n,+n]≢0 n)}} ↥g≡↧g

      eq : (↥ ((+ n) / n)) *ℤ (↧ 1ℚ) ≡ (↥ 1ℚ) *ℤ (↧ ((+ n) / n))
      eq = trans (ℤP.*-identityʳ _) (trans ↥≡↧ (sym (ℤP.*-identityˡ _)))

-- Equivalence and Setoid structure for the extentional equality

IsEquivalence-≗ : ∀ {a b} {A : Set a} {B : Set b}
  → IsEquivalence (_≗_ {A = A} {B = B})
IsEquivalence-≗ = record
   { refl = λ _ → refl
   ; sym = λ x≗y → sym ∘ x≗y
   ; trans = λ i≗j j≗k l → trans (i≗j l) (j≗k l)
   }

≗-setoid : ∀ {a b} {A : Set a} {B : Set b} → Setoid _ _
≗-setoid {A = A} {B} = record
  { Carrier = A → B
  ; _≈_ = _
  ; isEquivalence = IsEquivalence-≗ }

-- Take on subvector

take-++ : ∀ {m n} {a} {A : Set a} {as : Vec A n} {as' : Vec A m}
  → take n (as ++ as') ≡ as
take-++ {as = []} = refl
take-++ {as = _ ∷ _} = cong (_ ∷_) take-++

-- A variant of case that remembers the equality proof

case_of-≡_ : ∀ {ℓ ℓ₁} {A : Set ℓ} {B : Set ℓ₁}
  → (a : A) → ((a' : A) → a ≡ a' → B) → B
case a of-≡ f = f a refl

-- Pulling back a categorical structure from an isomorphism

module _ {a b b' c c' : Level} (C : Category a b c) where
  module C = Category C

  module _ (hom' : C.Obj → C.Obj → Setoid b' c') (inv : ∀ A B → Inverse (C.hom-setoid {A} {B}) (hom' A B)) where
    module hom' A B = Setoid (hom' A B)
    module inv {A} {B} = Inverse (inv A B)
    open C.HomReasoning using (_⟩∘⟨refl; refl⟩∘⟨_)

    Pullback : Category a b' c'
    Pullback = categoryHelper record
      { Obj = C.Obj
      ; _⇒_ = hom'.Carrier
      ; _≈_ = hom'._≈_ _ _
      ; id = inv.to C.id
      ; _∘_ = λ f g → inv.to (inv.from f C.∘ inv.from g)
      ; assoc = λ {_} {_} {_} {_} {f} {g} {h} → let open C.HomReasoning in inv.to-cong $ begin
        inv.from (inv.to (inv.from h C.∘ inv.from g)) C.∘ inv.from f
          ≈⟨ inv.strictlyInverseʳ _ ⟩∘⟨refl ⟩
        (inv.from h C.∘ inv.from g) C.∘ inv.from f
          ≈⟨ C.assoc ⟩
        inv.from h C.∘ (inv.from g C.∘ inv.from f)
          ≈⟨ refl⟩∘⟨ inv.strictlyInverseʳ _ ⟨
        inv.from h C.∘ inv.from (inv.to (inv.from g C.∘ inv.from f)) ∎
      ; identityˡ = λ {_} {_} {f} → let open SetoidReasoning (hom' _ _) in begin
        inv.to (inv.from (inv.to C.id) C.∘ inv.from f)
          ≈⟨ inv.to-cong (inv.strictlyInverseʳ _ ⟩∘⟨refl) ⟩
        inv.to (C.id C.∘ inv.from f)
          ≈⟨ inv.to-cong C.identityˡ ⟩
        inv.to (inv.from f)
          ≈⟨ inv.strictlyInverseˡ _ ⟩
        f ∎
      ; identityʳ = λ {_} {_} {f} → let open SetoidReasoning (hom' _ _) in begin
        inv.to (inv.from f C.∘ inv.from (inv.to C.id))
          ≈⟨ inv.to-cong (refl⟩∘⟨ inv.strictlyInverseʳ _) ⟩
        inv.to (inv.from f C.∘ C.id)
          ≈⟨ inv.to-cong C.identityʳ ⟩
        inv.to (inv.from f)
          ≈⟨ inv.strictlyInverseˡ _ ⟩
        f ∎
      ; equiv = hom'.isEquivalence _ _
      ; ∘-resp-≈ = λ {_} {_} {_} {f} {g} {h} {i} f≈g h≈i → let open C.HomReasoning in inv.to-cong $ begin
        inv.from f C.∘ inv.from h
          ≈⟨ inv.from-cong f≈g ⟩∘⟨ inv.from-cong h≈i ⟩
        inv.from g C.∘ inv.from i ∎
      }
