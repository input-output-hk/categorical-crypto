{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- Building an `APROPSignature` from a finite, arity-tagged set of
-- generators.
--
-- A signature's generators are described by:
--   * an atom set `X` with decidable equality `_≟X_`;
--   * a count `n : ℕ` of generators;
--   * `arity : Fin n → ObjTerm × ObjTerm`, giving each generator's (source, target) pair.
--
-- The morphism family is then `FinMor A B = Σ[ i ∈ Fin n ] dom i ≡ A × cod i ≡ B`
-- (the generators whose declared arity is `A ⇒ B`).
--------------------------------------------------------------------------------

open import Categories.APROP
open import Categories.FreeMonoidal

open import Data.Fin
open import Data.Fin.Properties using () renaming (_≟_ to _≟Fin_)
open import Data.Nat
open import Data.Product
open import Relation.Binary.Definitions
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary

module Categories.APROP.Hypergraph.Solver.FinSignature
  {X : Set} (_≟X_ : DecidableEquality X)
  {n : ℕ}
  (let open FreeMonoidalHelper Symm X using (ObjTerm))
  (arity : Fin n → ObjTerm × ObjTerm)
  where

open ObjTermDec _≟X_

dom cod : Fin n → ObjTerm
dom i = proj₁ (arity i)
cod i = proj₂ (arity i)

FinMor : ObjTerm → ObjTerm → Set
FinMor A B = Σ[ i ∈ Fin n ] dom i ≡ A × cod i ≡ B

gen : (i : Fin n) → FinMor (dom i) (cod i)
gen i = i , refl , refl

genElim : ∀ {ℓ} {F : ObjTerm → ObjTerm → Set ℓ}
        → ((i : Fin n) → F (dom i) (cod i))
        → ∀ {A B} → FinMor A B → F A B
genElim t (i , refl , refl) = t i

_≟-FinMor_ : ∀ {A B} → DecidableEquality (FinMor A B)
(i , p , q) ≟-FinMor (j , p' , q') with i ≟Fin j
... | no i≢j = no λ eq → i≢j (cong proj₁ eq)
... | yes refl rewrite uip-ObjTerm p p' | uip-ObjTerm q q' = yes refl

finSig : APROPSignature
finSig = record { X = X ; mor = FinMor ; _≟X_ = _≟X_ ; _≟-mor_ = _≟-FinMor_ }
