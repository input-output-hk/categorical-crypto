{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- Labeled directed hypergraph with ordered I/O interfaces (TensorRocq
-- §2.3). An edge is labeled by a generator whose source/target atom
-- lists agree with the vertex labels at its ordered input/output
-- pointers. The hypergraph is indexed by its boundary atom lists
-- `As`, `Bs`: two fields `dom-ok` and `cod-ok` relate the ordered Fin
-- boundary to these atom lists.
--
-- Indexing by boundary means composition has a clean type:
--   hCompose : Hypergraph Gen As Bs → Hypergraph Gen Bs Cs
--            → Hypergraph Gen As Cs
-- and the translation `⟦_⟧` from APROP terms lives in
--   Hypergraph FlatGen (flatten A) (flatten B).
--------------------------------------------------------------------------------

module Categories.APROP.Hypergraph.Core where

open import Data.Fin using (Fin)
open import Data.List using (List; map)
open import Data.Nat using (ℕ)
open import Relation.Binary.PropositionalEquality using (_≡_)

record Hypergraph {X : Set} (Gen : List X → List X → Set) (As Bs : List X) : Set where
  field
    nV : ℕ                                      -- vertex count
    vlab : Fin nV → X                           -- vertex labels

    nE : ℕ                                      -- edge count
    ein : Fin nE → List (Fin nV)                -- ordered edge sources
    eout : Fin nE → List (Fin nV)               -- ordered edge targets
    elab : (e : Fin nE)                         -- edge labels; atom lists
         → Gen (map vlab (ein e))               -- at each end agree with
               (map vlab (eout e))              -- `vlab`.

    dom : List (Fin nV)                         -- domain interface
    cod : List (Fin nV)                         -- codomain interface
    dom-ok : map vlab dom ≡ As                  -- boundary matches As
    cod-ok : map vlab cod ≡ Bs                  -- boundary matches Bs

-- Convenience: domain/codomain atom lists, derived from the type.
module _ {X : Set} {Gen : List X → List X → Set} {As Bs : List X} where
  open Hypergraph

  domL : Hypergraph Gen As Bs → List X
  domL _ = As

  codL : Hypergraph Gen As Bs → List X
  codL _ = Bs
