{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- Labeled directed hypergraph with ordered I/O interfaces (TensorRocq
-- §2.3). An edge is labeled by a generator whose source/target atom
-- lists agree with the vertex labels at its ordered input/output
-- pointers.
--
-- The hypergraph is not indexed by atom-list boundaries; the boundary
-- atom lists are *computed* by `domL`/`codL` from the underlying
-- Fin-list data.  This avoids subst₂-on-Hypergraph plumbing from
-- index-level boundary equations.
--------------------------------------------------------------------------------

module Categories.APROP.Hypergraph.Model.Core where

open import Data.Fin using (Fin)
open import Data.List using (List; map)
open import Data.Nat using (ℕ)

record Hypergraph {X : Set} (Gen : List X → List X → Set) : Set where
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

-- Derived boundary atom lists.
module _ {X : Set} {Gen : List X → List X → Set} where
  open Hypergraph

  domL : Hypergraph Gen → List X
  domL H = map (vlab H) (dom H)

  codL : Hypergraph Gen → List X
  codL H = map (vlab H) (cod H)
