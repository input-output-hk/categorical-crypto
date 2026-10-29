{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- APROP (Autonomous PROP) term language, following TensorRocq
-- (arXiv:2604.17592). Thin wrapper around `Categories.FreeMonoidal`.
--------------------------------------------------------------------------------

module Categories.APROP where

open import Axiom.UniquenessOfIdentityProofs
open import Relation.Binary.Definitions

open import Categories.FreeMonoidal public
  using (Variant; Mon; Symm; _≤_; v≤v; M≤S; FreeMonoidalData;
         module FreeMonoidalHelper; module FreeMonoidal)

module ObjTermDec {X : Set} (_≟X_ : DecidableEquality X) where
  open FreeMonoidalHelper Symm X

  open Decidable⇒UIP (≟ObjTerm _≟X_) public
    using () renaming (≡-irrelevant to uip-ObjTerm)

record APROPSignature : Set₁ where
  field X : Set

  open FreeMonoidalHelper Symm X

  field mor     : ObjTerm → ObjTerm → Set
        _≟X_    : DecidableEquality X
        _≟-mor_ : ∀ {A B} → DecidableEquality (mor A B)

  open ObjTermDec _≟X_ public

  _≟-ObjTerm_ : DecidableEquality ObjTerm
  _≟-ObjTerm_ = ≟ObjTerm _≟X_

  asFreeMonoidalData : FreeMonoidalData
  asFreeMonoidalData = record { v = Symm ; X = X ; mor = mor }

module APROP (sig : APROPSignature) where
  open APROPSignature sig public
  open FreeMonoidal asFreeMonoidalData public renaming (var to Agen)

  instance
    Symm≤Symm : Symm ≤ Symm
    Symm≤Symm = v≤v
