{-# OPTIONS --safe --without-K #-}

-- The finite possibility monad: `List` under the equality that tests it against
-- every `Bool`-valued predicate, so order and multiplicity are invisible to it.

open import categorical-crypto.Prelude hiding (any)

open import Class.Monad.Ext.Setoid

open import Data.Bool.ListAction
open import Data.Bool.ListAction.Ext
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
