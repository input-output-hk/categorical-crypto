{-# OPTIONS --safe --without-K #-}

-- The finite POSSIBILITY monad `𝒫`: `List` under the test-extensional equality
-- `_≈𝒫_`.  This is the possibilistic shadow of `Dist-ℚ`, whose own equality
-- `_≈Mℚ_` tests a distribution against every ℚ-valued function; here a list is
-- tested against every `Bool`-valued one, so order and multiplicity are
-- quotiented away and `List` becomes a COMMUTATIVE setoid monad.

-- `Data.List`'s `any` is the deprecated alias of `Data.Bool.ListAction.any`.
open import categorical-crypto.Prelude hiding (any)

open import Class.Monad.Ext.Setoid

open import Data.Bool.ListAction
open import Data.Bool.Properties
open import Data.List.Properties
open import Relation.Binary

module ProbabilisticLogic.Distribution.Possibility where

private variable
  ℓ : Level
  A B C : Type ℓ

infix 4 _≈𝒫_

_≈𝒫_ : {A : Type ℓ} → List A → List A → Type ℓ
σ ≈𝒫 τ = ∀ P → any P σ ≡ any P τ

≈𝒫-isEquivalence : IsEquivalence (_≈𝒫_ {A = A})
≈𝒫-isEquivalence = record
  { refl  = λ _ → refl
  ; sym   = λ σ≈τ P → sym (σ≈τ P)
  ; trans = λ σ≈τ τ≈ρ P → trans (σ≈τ P) (τ≈ρ P)
  }

𝒫-setoid : (A : Type ℓ) → Setoid _ _
𝒫-setoid A = record { Carrier = List A ; _≈_ = _≈𝒫_ ; isEquivalence = ≈𝒫-isEquivalence }

module 𝒫 {ℓ} {A : Type ℓ} = Setoid (𝒫-setoid A)

------------------------------------------------------------------------
-- `any` as a homomorphism from the list structure into `_∨_`.

any-cong : {P Q : A → Bool} → (∀ a → P a ≡ Q a) → (xs : List A) → any P xs ≡ any Q xs
any-cong P≡Q []       = refl
any-cong P≡Q (x ∷ xs) = cong₂ _∨_ (P≡Q x) (any-cong P≡Q xs)

any-const-false : (xs : List A) → any (λ _ → false) xs ≡ false
any-const-false []       = refl
any-const-false (x ∷ xs) = any-const-false xs

any-++ : (P : A → Bool) (xs ys : List A) → any P (xs ++ ys) ≡ any P xs ∨ any P ys
any-++ P []       ys = refl
any-++ P (x ∷ xs) ys = trans (cong (P x ∨_) (any-++ P xs ys))
                             (sym (∨-assoc (P x) (any P xs) (any P ys)))

any-concatMap : (P : B → Bool) (f : A → List B) (xs : List A)
              → any P (concatMap f xs) ≡ any (λ a → any P (f a)) xs
any-concatMap P f []       = refl
any-concatMap P f (x ∷ xs) = trans (any-++ P (f x) (concatMap f xs))
                                   (cong (any P (f x) ∨_) (any-concatMap P f xs))

private
  ∨-middle : (a b c d : Bool) → (a ∨ b) ∨ (c ∨ d) ≡ (a ∨ c) ∨ (b ∨ d)
  ∨-middle true  b c d = refl
  ∨-middle false b c d =
    trans (sym (∨-assoc b c d)) (trans (cong (_∨ d) (∨-comm b c)) (∨-assoc c b d))

any-∨ : (P Q : A → Bool) (xs : List A) → any (λ a → P a ∨ Q a) xs ≡ any P xs ∨ any Q xs
any-∨ P Q []       = refl
any-∨ P Q (x ∷ xs) = trans (cong ((P x ∨ Q x) ∨_) (any-∨ P Q xs))
                           (∨-middle (P x) (Q x) (any P xs) (any Q xs))

-- Fubini for `any`: the reason `_≈𝒫_` makes `List` commutative.
any-pair : (Q : A × B → Bool) (xs : List A) (ys : List B)
         → any (λ a → any (λ b → Q (a , b)) ys) xs
         ≡ any (λ b → any (λ a → Q (a , b)) xs) ys
any-pair Q []       ys = sym (any-const-false ys)
any-pair Q (x ∷ xs) ys =
  trans (cong (any (λ b → Q (x , b)) ys ∨_) (any-pair Q xs ys))
        (sym (any-∨ (λ b → Q (x , b)) (λ b → any (λ a → Q (a , b)) xs) ys))

------------------------------------------------------------------------
-- Setoid monad structure on `List` (the `Monad-List` instance of
-- `Class.Monad.Instances`, whose bind is `flip concatMap`).

>>=𝒫-cong : {σ τ : List A} {f g : A → List B}
          → σ ≈𝒫 τ → (∀ a → f a ≈𝒫 g a) → concatMap f σ ≈𝒫 concatMap g τ
>>=𝒫-cong {σ = σ} {τ} {f} {g} σ≈τ f≈g P = begin
  any P (concatMap f σ)     ≡⟨ any-concatMap P f σ ⟩
  any (λ a → any P (f a)) σ ≡⟨ any-cong (λ a → f≈g a P) σ ⟩
  any (λ a → any P (g a)) σ ≡⟨ σ≈τ (λ a → any P (g a)) ⟩
  any (λ a → any P (g a)) τ ≡⟨ sym (any-concatMap P g τ) ⟩
  any P (concatMap g τ) ∎
  where open ≡-Reasoning

>>=𝒫-identityˡ : (a : A) (h : A → List B) → concatMap h (a ∷ []) ≈𝒫 h a
>>=𝒫-identityˡ a h P = cong (any P) (++-identityʳ (h a))

>>=𝒫-identityʳ : (σ : List A) → concatMap (_∷ []) σ ≈𝒫 σ
>>=𝒫-identityʳ σ P = cong (any P) (concatMap-pure σ)

>>=𝒫-assoc : (σ : List A) (g : A → List B) (h : B → List C)
           → concatMap h (concatMap g σ) ≈𝒫 concatMap (λ a → concatMap h (g a)) σ
>>=𝒫-assoc σ g h P = begin
  any P (concatMap h (concatMap g σ))         ≡⟨ any-concatMap P h (concatMap g σ) ⟩
  any (λ b → any P (h b)) (concatMap g σ)     ≡⟨ any-concatMap (λ b → any P (h b)) g σ ⟩
  any (λ a → any (λ b → any P (h b)) (g a)) σ ≡⟨ any-cong (λ a → sym (any-concatMap P h (g a))) σ ⟩
  any (λ a → any P (concatMap h (g a))) σ     ≡⟨ sym (any-concatMap P (λ a → concatMap h (g a)) σ) ⟩
  any P (concatMap (λ a → concatMap h (g a)) σ) ∎
  where open ≡-Reasoning

private
  any-⊗ : (Q : C → Bool) (p : A → B → C) (σ : List A) (τ : List B)
        → any Q (concatMap (λ a → concatMap (λ b → p a b ∷ []) τ) σ)
        ≡ any (λ a → any (λ b → Q (p a b)) τ) σ
  any-⊗ Q p σ τ = begin
    any Q (concatMap (λ a → concatMap (λ b → p a b ∷ []) τ) σ)
      ≡⟨ any-concatMap Q (λ a → concatMap (λ b → p a b ∷ []) τ) σ ⟩
    any (λ a → any Q (concatMap (λ b → p a b ∷ []) τ)) σ
      ≡⟨ any-cong (λ a → any-concatMap Q (λ b → p a b ∷ []) τ) σ ⟩
    any (λ a → any (λ b → any Q (p a b ∷ [])) τ) σ
      ≡⟨ any-cong (λ a → any-cong (λ b → ∨-identityʳ (Q (p a b))) τ) σ ⟩
    any (λ a → any (λ b → Q (p a b)) τ) σ ∎
    where open ≡-Reasoning

>>=𝒫-comm : (σ : List A) (τ : List B)
          → concatMap (λ a → concatMap (λ b → (a ,′ b) ∷ []) τ) σ
          ≈𝒫 concatMap (λ b → concatMap (λ a → (a , b) ∷ []) σ) τ
>>=𝒫-comm σ τ Q = trans (any-⊗ Q _,′_ σ τ)
                        (trans (any-pair Q σ τ) (sym (any-⊗ Q (λ b a → a , b) τ σ)))

instance
  MonadSetoid-List : MonadSetoid List
  MonadSetoid-List = record
    { _≈ᴹ_             = _≈𝒫_
    ; ≈ᴹ-isEquivalence = ≈𝒫-isEquivalence
    ; >>=-cong         = λ {x = σ} {τ} {f} {g} → >>=𝒫-cong {σ = σ} {τ} {f} {g}
    }

  MonadLawsSetoid-List : MonadLawsSetoid List
  MonadLawsSetoid-List = record
    { >>=-identityˡ-≈ = λ {a = a} {h} → >>=𝒫-identityˡ a h
    ; >>=-identityʳ-≈ = >>=𝒫-identityʳ
    ; >>=-assoc-≈     = λ m {g} {h} → >>=𝒫-assoc m g h
    }

  CommutativeMonadSetoid-List : CommutativeMonadSetoid List
  CommutativeMonadSetoid-List = record { >>=-comm-≈ = λ {x = σ} {τ} → >>=𝒫-comm σ τ }
