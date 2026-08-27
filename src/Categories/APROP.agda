{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- APROP (Autonomous PROP) term language, following TensorRocq
-- (arXiv:2604.17592). Thin wrapper around `Categories.FreeMonoidal`
-- specialised to `v = Symm`: the free symmetric monoidal category over a
-- signature `(X , mor)` of atoms and generators.
--
-- Define a signature `mySig : APROPSignature` and `open APROP mySig` to
-- access the term constructors. The generator injection is exposed as
-- `Agen` to match the paper's notation (elsewhere `var`).
--------------------------------------------------------------------------------

module Categories.APROP where

open import Categories.FreeMonoidal public

-- Propositional equality for the whole APROP tree: 47 of the 53 modules that
-- blanket-open this one imported it themselves.  The hidden names are the four
-- the island prelude hides (`[_]` clashes with `Data.List`'s) plus `J`, which
-- `Strict/Embed` defines as a lemma of its own — a name this re-export would
-- otherwise make undefinable there.
open import Relation.Binary.PropositionalEquality public
  hiding (preorder; isPreorder; setoid; [_]; J)

record APROPSignature : Set₁ where
  field X : Set

  open FreeMonoidalHelper Symm X using (ObjTerm)

  field mor : ObjTerm → ObjTerm → Set

  asFreeMonoidalData : FreeMonoidalData
  asFreeMonoidalData = record { v = Symm ; X = X ; mor = mor }

module APROP (sig : APROPSignature) where
  open APROPSignature sig public
  open FreeMonoidal asFreeMonoidalData public renaming (var to Agen)

  -- `Symm ≤ Symm` for instance search, so `σ` needs no explicit `⦃ v≤v ⦄`.
  instance
    Symm≤Symm : Symm ≤ Symm
    Symm≤Symm = v≤v
