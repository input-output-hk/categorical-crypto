{-# OPTIONS --safe --without-K #-}

-- Two-edge interchange for the strict decoder.

open import Categories.APROP.Internal.Prelude

module Categories.APROP.Hypergraph.Soundness.Strict.Interchange.SwapCore
  (sig : APROPSignature) where

open import Categories.APROP.Hypergraph.Model.Core using (Hypergraph)
open import Categories.APROP.Hypergraph.Model.Dependency using (Dep)
open import Categories.APROP.Hypergraph.Model.FromAPROP sig using (FlatGen)
open import Categories.APROP.Hypergraph.Soundness.Strict.Decode.Decoder sig
open import Categories.APROP.Hypergraph.Soundness.Strict.Interchange.EdgeStepRel sig
  using (module EdgeStepView)

import Categories.Combinatorics.LinearExtension as LinExt
open import Data.Fin using (Fin)

module _ (H : Hypergraph FlatGen) where
  private module H = Hypergraph H

  open StrictDecoder H
  open EdgeStepView H public
  open LinExt (Fin H.nE) (Dep H) public using (Incomp)
