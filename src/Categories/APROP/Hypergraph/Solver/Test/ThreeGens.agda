{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- The shared three-generator fixture signature used by the operational gate
-- tests (`FindIsoTests`, `SubMatchTests`).
--
--   atoms      X = Fin 3, written a₀ a₁ a₂;
--   generators f : a₀ → a₁ , g : a₁ → a₂ , h : a₂ → a₀ .
--
-- The generators are a hand-rolled `data` type (not `FinSignature`): its
-- three-clause `_≟-MyMor_` is what the gates want to *reduce*, and routing them
-- through `FinSignature._≟-FinMor_` forces `uip-ObjTerm` twice per edge-label
-- comparison (measured +27..32 % on `FindIsoTests`, R54-F15).
--------------------------------------------------------------------------------

module Categories.APROP.Hypergraph.Solver.Test.ThreeGens where

open import Data.Fin using (Fin; zero; suc)
open import Data.Fin.Properties using () renaming (_≟_ to _≟F_)
open import Relation.Binary.Definitions using (DecidableEquality)
open import Relation.Binary.PropositionalEquality using (refl)
open import Relation.Nullary using (yes)

open import Categories.APROP using (APROPSignature)
open import Categories.FreeMonoidal
open import Categories.APROP.Hypergraph.Solver.Signature using (APROPSignatureDec)

X : Set
X = Fin 3

open FreeMonoidalHelper Symm X using (ObjTerm; Var) public

-- Shorthand for the three atoms.
a₀ a₁ a₂ : ObjTerm
a₀ = Var zero
a₁ = Var (suc zero)
a₂ = Var (suc (suc zero))

-- Three constructors at distinct (dom, cod), so index unification rules out
-- the cross cases and `_≟-MyMor_` need only handle the diagonal.
data MyMor : ObjTerm → ObjTerm → Set where
  f : MyMor a₀ a₁
  g : MyMor a₁ a₂
  h : MyMor a₂ a₀

_≟-MyMor_ : ∀ {A B} → DecidableEquality (MyMor A B)
f ≟-MyMor f = yes refl
g ≟-MyMor g = yes refl
h ≟-MyMor h = yes refl

mySig : APROPSignature
mySig = record { X = X ; mor = MyMor }

mySigDec : APROPSignatureDec
mySigDec = record { sig = mySig ; _≟X_ = _≟F_ ; _≟-mor_ = _≟-MyMor_ }
