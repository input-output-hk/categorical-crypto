{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- APROP (Autonomous PROP) term language, following TensorRocq
-- (arXiv:2604.17592). Thin wrapper around `Categories.FreeMonoidal`
-- specialised to `v = Symm`: the free symmetric monoidal category over
-- a user-supplied signature `(X , mor)` of atoms and generators.
--
-- Intended use: define a signature
--
--   mySig : APROPSignature
--   mySig = record { X = ... ; mor = ... }
--
-- and then `open APROP mySig` to access the term constructors. The
-- generator injection is exposed under the name `Agen` to match the
-- paper's notation (elsewhere in this repo it is `var`).
--------------------------------------------------------------------------------

module Categories.APROP where

open import Categories.FreeMonoidal public

record APROPSignature : Set₁ where
  field X : Set

  open FreeMonoidalHelper Symm X using (ObjTerm)

  field mor : ObjTerm → ObjTerm → Set

  asFreeMonoidalData : FreeMonoidalData
  asFreeMonoidalData = record { v = Symm ; X = X ; mor = mor }

module APROP (sig : APROPSignature) where
  open APROPSignature sig public
  open FreeMonoidal asFreeMonoidalData public renaming (var to Agen)

  -- Make the `Symm ≤ Symm` witness available for instance search so
  -- the braiding constructor `σ` can be used without explicit `⦃ v≤v ⦄`.
  instance
    Symm≤Symm : Symm ≤ Symm
    Symm≤Symm = v≤v
