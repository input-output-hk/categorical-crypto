{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- Pruning helpers for a canonical `hCompose` (TODO.org Option A).
--
-- Given `xs : List (Fin n)` (typically `K.dom` of the right operand of a
-- cospan composition), we want to identify the Fin values NOT in `xs`.
-- After composition, the positions named in `xs` have been "glued" to the
-- left operand's `cod`, so they become unreferenced and can be pruned.
--
-- This module provides:
--   * `nonMem xs`     — the list of Fin values not in `xs`.
--   * `count-non xs`  — its length (the count of "survivors").
--
-- The canonical `hCompose` will have vertex count
--   `G.nV + count-non K.dom`
-- and a `remap` that sends each K-vertex to either:
--   * a G-side position (if the vertex was in `K.dom`), or
--   * a fresh pruned-K-side position (via an index lookup in `nonMem K.dom`).
--------------------------------------------------------------------------------

module Categories.APROP.Hypergraph.Prune where

open import Data.Fin using (Fin)
open import Data.Fin.Properties using (_≟_)
open import Data.List using (List; length; filter; allFin)
open import Data.Nat using (ℕ)
open import Relation.Nullary.Decidable using (¬?)

--------------------------------------------------------------------------------
-- Non-members of a Fin list.

module _ {n : ℕ} where
  open import Data.List.Membership.DecPropositional (_≟_ {n = n}) using (_∈?_)

  -- The Fin values not present in `xs`.
  nonMem : List (Fin n) → List (Fin n)
  nonMem xs = filter (λ v → ¬? (v ∈? xs)) (allFin n)

  -- Count of Fin values not in `xs`.
  count-non : List (Fin n) → ℕ
  count-non xs = length (nonMem xs)
