{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- Building an `APROPSignatureDec` from a *finite, arity-tagged* set of
-- generators, instead of a hand-rolled `data` type.
--
-- A signature's generators are described by:
--   * an atom set `X` with decidable equality `_≟X_`;
--   * a count `n : ℕ` of generators;
--   * `arity : Fin n → ObjTerm × ObjTerm`, giving each generator's (source,
--     target) pair.  `dom`/`cod` are the two projections.
--
-- The morphism family is then `FinMor A B = Σ[ i ∈ Fin n ] dom i ≡ A × cod i ≡ B`
-- (the generators whose declared arity is `A ⇒ B`).  Decidable equality on
-- `FinMor A B` is *free*: compare the `Fin n` indices, and the `ObjTerm`
-- equality proofs are unique by UIP (decidable equality ⇒ UIP, no `K`).
--
-- This removes both the bespoke generator `data` declaration and its
-- `DecidableEquality` boilerplate from each use site; a generator is now just
-- `gen i` for `i : Fin n`, and an interpretation of the generators is given by
-- `genElim` from a plain `(i : Fin n) → …` table (no `refl` patterns).
--------------------------------------------------------------------------------

open import Relation.Binary.Definitions using (DecidableEquality)
open import Data.Nat using (ℕ)
open import Data.Fin using (Fin)
open import Data.Product using (_×_)
open import Categories.FreeMonoidal

module Categories.APROP.Hypergraph.Solver.FinSignature
  {X : Set} (_≟X_ : DecidableEquality X)
  {n : ℕ}
  (let open FreeMonoidalHelper Symm X using (ObjTerm))
  (arity : Fin n → ObjTerm × ObjTerm)
  where

open import Level using (Level)
open import Data.Fin.Properties using () renaming (_≟_ to _≟Fin_)
open import Data.Product using (Σ-syntax; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import Relation.Nullary using (yes; no)
open import Axiom.UniquenessOfIdentityProofs using (module Decidable⇒UIP)

open import Categories.APROP using (APROPSignature)
open import Categories.APROP.Hypergraph.Solver.Signature
  using (APROPSignatureDec; module ObjTermDec)

open ObjTermDec _≟X_ using (≟-ObjTerm)
open Decidable⇒UIP ≟-ObjTerm using (≡-irrelevant)

-- Source and target of each generator, as the projections of its arity.
dom cod : Fin n → ObjTerm
dom i = proj₁ (arity i)
cod i = proj₂ (arity i)

-- A generator of declared arity `A ⇒ B` is an index `i` together with
-- evidence that `dom i`/`cod i` are `A`/`B`.
FinMor : ObjTerm → ObjTerm → Set
FinMor A B = Σ[ i ∈ Fin n ] (dom i ≡ A × cod i ≡ B)

-- The `i`-th generator, at its declared arity.  On a concrete `i`, `dom i`
-- and `cod i` compute, so `refl` suffices and `gen i : FinMor (dom i) (cod i)`.
gen : (i : Fin n) → FinMor (dom i) (cod i)
gen i = i , refl , refl

-- Recursor: every `FinMor A B` is `gen i` for some `i`, so a map out of the
-- generators into any binary family `F` on `ObjTerm` is determined by its
-- values on the indices.  This lets an interpretation be given by a plain
-- `(i : Fin n) → F (dom i) (cod i)` table, with no `refl` patterns at the use
-- site.  (`F` is a *non-dependent* family — `F A B` rather than `P m` — so it
-- is inferred by ordinary pattern unification from the expected codomain,
-- e.g. `λ A B → ⟦ A ⟧₀ ⇒ ⟦ B ⟧₀`.)
genElim : ∀ {ℓ} {F : ObjTerm → ObjTerm → Set ℓ}
        → ((i : Fin n) → F (dom i) (cod i))
        → ∀ {A B} → FinMor A B → F A B
genElim t (i , refl , refl) = t i

-- Decidable equality: indices via `_≟Fin_`, proofs via UIP.
_≟-FinMor_ : ∀ {A B} → DecidableEquality (FinMor A B)
(i , p , q) ≟-FinMor (j , _ , _) with i ≟Fin j
... | no  i≢j  = no λ eq → i≢j (cong proj₁ eq)
(i , p , q) ≟-FinMor (.i , p' , q') | yes refl
  rewrite ≡-irrelevant p p' | ≡-irrelevant q q' = yes refl

finSig : APROPSignature
finSig = record { X = X ; mor = FinMor }

finSigDec : APROPSignatureDec
finSigDec = record { sig = finSig ; _≟X_ = _≟X_ ; _≟-mor_ = _≟-FinMor_ }
