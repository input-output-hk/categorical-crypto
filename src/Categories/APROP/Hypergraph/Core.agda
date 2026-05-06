{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- Labeled directed hypergraph with ordered I/O interfaces (TensorRocq
-- §2.3). An edge is labeled by a generator whose source/target atom
-- lists agree with the vertex labels at its ordered input/output
-- pointers.
--
-- The hypergraph is no longer indexed by atom-list boundaries; the
-- boundary atom lists are *computed* by `domL`/`codL` from the
-- underlying Fin-list data.  This avoids the subst₂-on-Hypergraph
-- plumbing that previously arose from index-level boundary equations.
--
-- For backwards compatibility with code that wants to fix boundaries
-- in the type, the alias `Hypergraphᵇ Gen As Bs` packages an
-- unindexed `Hypergraph Gen` together with two propositional witnesses
-- that its `domL`/`codL` agree with `As`/`Bs`.
--
-- Composition has the form
--   hCompose : (G K : Hypergraph Gen) → codL G ≡ domL K → Hypergraph Gen
-- and the translation `⟦_⟧` from APROP terms lives in `Hypergraph FlatGen`,
-- with the boundary fact `domL ⟦f⟧ ≡ flatten A` exposed as a separate
-- propositional lemma.
--------------------------------------------------------------------------------

module Categories.APROP.Hypergraph.Core where

open import Data.Fin using (Fin)
open import Data.List using (List; map)
open import Data.Nat using (ℕ)
open import Data.Product using (Σ-syntax; _,_; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

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

--------------------------------------------------------------------------------
-- Backwards-compatible boundary-fixed wrapper.  A `Hypergraphᵇ Gen As Bs`
-- is an unindexed `Hypergraph Gen` whose `domL` is propositionally `As`
-- and `codL` is propositionally `Bs`.

record Hypergraphᵇ {X : Set} (Gen : List X → List X → Set)
                    (As Bs : List X) : Set where
  constructor mkHᵇ
  field
    H      : Hypergraph Gen
    dom-ok : domL H ≡ As
    cod-ok : codL H ≡ Bs

  open Hypergraph H public

module _ {X : Set} {Gen : List X → List X → Set} {As Bs : List X} where
  open Hypergraphᵇ

  forget : Hypergraphᵇ Gen As Bs → Hypergraph Gen
  forget = H
