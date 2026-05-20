{-# OPTIONS #-}

--------------------------------------------------------------------------------
-- Smoke tests for `findIso`, threaded through `completeness-full`.
--
-- Each test is of the form
--
--   test : f ≈Term g
--   test = completeness-full (from-just (findIso ⟪ f ⟫ ⟪ g ⟫))
--
-- which compels `findIso` to actually reduce to `just _` at type-check
-- time and routes the resulting hypergraph iso through the inductive
-- `decode-rel-resp-≅ᴴ-full` dispatcher to a syntactic `≈Term` equation.
--
-- IMPORTANT: `completeness-full` operates on `FromAPROP.⟪_⟫` (the
-- *unpruned* translation), whereas the legacy smoke-test file used
-- `Translation.⟪_⟫` (pruned).  Under unpruned `hCompose`, every
-- composition `g ∘ f` retains interior vertices, so most of the
-- original tests no longer admit an iso between LHS and RHS at the
-- unpruned level: e.g. `⟪ id ∘ Agen f ⟫` and `⟪ Agen f ⟫` differ in
-- vertex count.  Only the σ-free, composition-free equations survive:
--
--   - `test-≈-refl`     (same term)
--   - `test-id⊗id`      (no composition; `⟪ id {A} ⊗₁ id {B} ⟫` and
--                        `⟪ id {A ⊗₀ B} ⟫` both reduce to `hId _`)
--
-- All other original tests fail at the `from-just` step because
-- `findIso` returns `nothing`, which is the correct behaviour: the
-- iso simply doesn't exist for the unpruned hypergraphs.  See
-- REFACTORING.md for the full migration story.
--------------------------------------------------------------------------------

module Categories.APROP.Hypergraph.Solver.Tests where

open import Data.Fin using (Fin; zero; suc)
open import Data.Fin.Properties using () renaming (_≟_ to _≟F_)
open import Data.Maybe.Base using (from-just)
open import Relation.Binary.Definitions using (DecidableEquality)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (yes; no)

open import Categories.APROP using (APROPSignature; module APROP)
open import Categories.FreeMonoidal
open import Categories.APROP.Hypergraph.Solver.Signature using (APROPSignatureDec)

--------------------------------------------------------------------------------
-- Atom alphabet.

X : Set
X = Fin 3

open FreeMonoidalHelper Symm X using (ObjTerm; Var)

private
  -- Shorthand for the three atoms.
  a₀ a₁ a₂ : ObjTerm
  a₀ = Var zero
  a₁ = Var (suc zero)
  a₂ = Var (suc (suc zero))

--------------------------------------------------------------------------------
-- Generator data type.

data MyMor : ObjTerm → ObjTerm → Set where
  f : MyMor a₀ a₁
  g : MyMor a₁ a₂
  h : MyMor a₂ a₀

_≟-MyMor_ : ∀ {A B} → DecidableEquality (MyMor A B)
f ≟-MyMor f = yes refl
g ≟-MyMor g = yes refl
h ≟-MyMor h = yes refl

--------------------------------------------------------------------------------
-- Build the signature.

mySig : APROPSignature
mySig = record { X = X ; mor = MyMor }

mySigDec : APROPSignatureDec
mySigDec = record
  { sig     = mySig
  ; _≟X_    = _≟F_
  ; _≟-mor_ = _≟-MyMor_
  }

--------------------------------------------------------------------------------
-- Bring in the term language, the solver, and the completeness theorem.

open import Categories.APROP.Hypergraph.Iso using (_≅ᴴ_)
open import Categories.APROP.Hypergraph.FromAPROP mySig using (⟪_⟫)
open import Categories.APROP.Hypergraph.Solver.FindIso mySigDec using (findIso)
open import Categories.APROP.Hypergraph.CompletenessFull mySigDec
  using (completeness-full)
open APROP mySig

--------------------------------------------------------------------------------
-- Tests that survive under the unpruned translation.

test-≈-refl : Agen f ≈Term Agen f
test-≈-refl = completeness-full
  (from-just (findIso ⟪ Agen f ⟫ ⟪ Agen f ⟫))

test-id⊗id : (id {a₀} ⊗₁ id {a₁}) ≈Term id {a₀ ⊗₀ a₁}
test-id⊗id = completeness-full
  (from-just (findIso ⟪ id {a₀} ⊗₁ id {a₁} ⟫ ⟪ id {a₀ ⊗₀ a₁} ⟫))
