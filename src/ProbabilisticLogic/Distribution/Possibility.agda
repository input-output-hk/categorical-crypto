{-# OPTIONS --safe --without-K #-}

-- The finite possibility monad: `List` under stdlib set equality, so order and
-- multiplicity are invisible to it.

open import categorical-crypto.Prelude

open import Class.Monad.Ext.Setoid

open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Properties
open import Data.List.Properties.Ext
open import Data.List.Relation.Binary.BagAndSetEquality using (_∼[_]_; set; [_]-Equality)
open import Data.List.Relation.Unary.Any using (Any)
open import Data.List.Relation.Unary.Any.Properties
  using (Any-cong; concatMap⁺; concatMap⁻; swap↔)
open import Function.Bundles using (mk⇔)
open import Function.Related.Propositional using (module EquationalReasoning)
open import Relation.Binary

module ProbabilisticLogic.Distribution.Possibility where

private variable
  ℓ : Level
  A B C : Type ℓ

module 𝒫 {ℓ} {A : Type ℓ} = Setoid ([ set ]-Equality A)

------------------------------------------------------------------------
-- Setoid monad structure

>>=𝒫-cong : {σ τ : List A} {f g : A → List B}
          → σ ∼[ set ] τ → (∀ a → f a ∼[ set ] g a)
          → concatMap f σ ∼[ set ] concatMap g τ
>>=𝒫-cong {σ = σ} {τ} {f} {g} σ≈τ f≈g {z} = begin
  z ∈ concatMap f σ      ∼⟨ mk⇔ (concatMap⁻ f) (concatMap⁺ f) ⟩
  Any (λ a → z ∈ f a) σ  ∼⟨ Any-cong (λ a → f≈g a {z}) σ≈τ ⟩
  Any (λ a → z ∈ g a) τ  ∼⟨ mk⇔ (concatMap⁺ g) (concatMap⁻ g) ⟩
  z ∈ concatMap g τ      ∎
  where open EquationalReasoning

>>=𝒫-identityˡ : (a : A) (h : A → List B) → concatMap h (a ∷ []) ∼[ set ] h a
>>=𝒫-identityˡ a h = 𝒫.reflexive (++-identityʳ (h a))

>>=𝒫-identityʳ : (σ : List A) → concatMap (_∷ []) σ ∼[ set ] σ
>>=𝒫-identityʳ σ = 𝒫.reflexive (concatMap-pure σ)

>>=𝒫-assoc : (σ : List A) (g : A → List B) (h : B → List C)
           → concatMap h (concatMap g σ)
           ∼[ set ] concatMap (λ a → concatMap h (g a)) σ
>>=𝒫-assoc σ g h = 𝒫.reflexive (concatMap-assoc σ g h)

>>=𝒫-comm : (σ : List A) (τ : List B)
          → concatMap (λ a → concatMap (λ b → (a ,′ b) ∷ []) τ) σ
          ∼[ set ] concatMap (λ b → concatMap (λ a → (a , b) ∷ []) σ) τ
>>=𝒫-comm σ τ {z} = begin
  z ∈ concatMap (λ a → concatMap (λ b → (a ,′ b) ∷ []) τ) σ
    ∼⟨ mk⇔ (concatMap⁻ _) (concatMap⁺ _) ⟩
  Any (λ a → z ∈ concatMap (λ b → (a ,′ b) ∷ []) τ) σ
    ∼⟨ Any-cong (λ _ → mk⇔ (concatMap⁻ _) (concatMap⁺ _)) 𝒫.refl ⟩
  Any (λ a → Any (λ b → z ∈ (a ,′ b) ∷ []) τ) σ
    ↔⟨ swap↔ ⟩
  Any (λ b → Any (λ a → z ∈ (a , b) ∷ []) σ) τ
    ∼⟨ Any-cong (λ _ → mk⇔ (concatMap⁺ _) (concatMap⁻ _)) 𝒫.refl ⟩
  Any (λ b → z ∈ concatMap (λ a → (a , b) ∷ []) σ) τ
    ∼⟨ mk⇔ (concatMap⁺ _) (concatMap⁻ _) ⟩
  z ∈ concatMap (λ b → concatMap (λ a → (a , b) ∷ []) σ) τ ∎
  where open EquationalReasoning

instance
  MonadSetoid-List : MonadSetoid List
  MonadSetoid-List = record
    { _≈ᴹ_             = _∼[ set ]_
    ; ≈ᴹ-isEquivalence = 𝒫.isEquivalence
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
