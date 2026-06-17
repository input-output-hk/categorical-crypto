{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- Operational smoke tests for `subMatch`: each `refl` below forces the matcher
-- to *reduce* at type-check time, so a green file means the search genuinely
-- located (or correctly rejected) the embedding — not merely that the types
-- line up.
--
--   f : a₀ → a₁ , g : a₁ → a₂ , h : a₂ → a₀ .
--------------------------------------------------------------------------------

module Categories.APROP.Hypergraph.Solver.Test.SubMatchTests where

open import Data.Bool.Base using (Bool; true; false)
open import Data.Fin using (Fin; zero; suc)
open import Data.Fin.Properties using () renaming (_≟_ to _≟F_)
open import Data.Maybe.Base using (is-just)
open import Relation.Binary.Definitions using (DecidableEquality)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (yes; no)

open import Categories.APROP using (APROPSignature; module APROP)
open import Categories.FreeMonoidal
open import Categories.APROP.Hypergraph.Solver.Signature using (APROPSignatureDec)

X : Set
X = Fin 3

open FreeMonoidalHelper Symm X using (ObjTerm; Var)

private
  a₀ a₁ a₂ : ObjTerm
  a₀ = Var zero
  a₁ = Var (suc zero)
  a₂ = Var (suc (suc zero))

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
mySigDec = record
  { sig     = mySig
  ; _≟X_    = _≟F_
  ; _≟-mor_ = _≟-MyMor_
  }

open import Categories.APROP.Hypergraph.Model.Translation mySig using (⟪_⟫)
open import Categories.APROP.Hypergraph.Solver.Rewrite.SubMatch mySigDec using (subMatch)
open APROP mySig

--------------------------------------------------------------------------------
-- Positive: the single edge `f` embeds in the chain `h ∘ (g ∘ f)`.

found-single : is-just (subMatch ⟪ Agen f ⟫ ⟪ Agen h ∘ (Agen g ∘ Agen f) ⟫) ≡ true
found-single = refl

-- Positive: the two-edge redex `g ∘ f` embeds in the chain `h ∘ (g ∘ f)`.
found-pair : is-just (subMatch ⟪ Agen g ∘ Agen f ⟫ ⟪ Agen h ∘ (Agen g ∘ Agen f) ⟫) ≡ true
found-pair = refl

-- Positive: a redex sitting inside a tensor context, `f ⊗ id`.
found-in-tensor
  : is-just (subMatch ⟪ Agen f ⟫ ⟪ Agen f ⊗₁ id {a₁} ⟫) ≡ true
found-in-tensor = refl

--------------------------------------------------------------------------------
-- Negative: a generator absent from the target is not matched.

absent : is-just (subMatch ⟪ Agen h ⟫ ⟪ Agen g ∘ Agen f ⟫) ≡ false
absent = refl
