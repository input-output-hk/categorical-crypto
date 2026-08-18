{-# OPTIONS --safe --without-K #-}

open import categorical-crypto.Prelude hiding (any)

open import Data.Bool.ListAction
open import Data.Bool.Properties
open import Data.List.Relation.Binary.BagAndSetEquality using (_∼[_]_; set)
open import Data.List.Relation.Binary.Subset.Propositional using (_⊆_)
open import Data.List.Relation.Binary.Subset.Propositional.Properties using (any⁺)
open import Function.Bundles using (Equivalence; mk⇔)

module Data.Bool.ListAction.Ext where

private variable ℓ : Level

-- `any` only sees which of its tests some element passes, so it is blind to the
-- order and the multiplicity `set` equality quotients away.  The converse fails:
-- no `A → Bool` need separate two given elements.
any-cong : {A : Type ℓ} {σ τ : List A}
         → σ ∼[ set ] τ → (P : A → Bool) → any P σ ≡ any P τ
any-cong {A = A} σ≈τ P =
  ⇔→≡ (mk⇔ (mono (Equivalence.to σ≈τ)) (mono (Equivalence.from σ≈τ)))
  where
  mono : {σ τ : List A} → σ ⊆ τ → any P σ ≡ true → any P τ ≡ true
  mono σ⊆τ = Equivalence.to T-≡ ∘ any⁺ P σ⊆τ ∘ Equivalence.from T-≡
