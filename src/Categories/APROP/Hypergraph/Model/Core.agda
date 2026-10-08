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

open import Data.Fin
open import Data.List
open import Data.Nat

record Hypergraph {X : Set} (Gen : List X → List X → Set) : Set where
  field nV : ℕ
        vlab : Fin nV → X
        nE : ℕ
        ein eout : Fin nE → List (Fin nV)
        elab : (e : Fin nE) → Gen (map vlab (ein e)) (map vlab (eout e))
        dom cod : List (Fin nV)

module _ {X : Set} {Gen : List X → List X → Set} where
  open Hypergraph

  domL : Hypergraph Gen → List X
  domL H = map (vlab H) (dom H)

  codL : Hypergraph Gen → List X
  codL H = map (vlab H) (cod H)
