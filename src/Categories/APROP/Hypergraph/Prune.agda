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
--   * `classify xs v` — cases `v : Fin n` as either a position in `xs`
--                       or a position in `nonMem xs`.
--   * `remap xs f`    — combinator that routes members of `xs` to an
--                       arbitrary target space via `f`, and non-members
--                       to the fresh pruned space of size `count-non xs`.
--
-- The canonical `hCompose` will have vertex count
--   `G.nV + count-non K.dom`
-- and a `remap` that sends each K-vertex to either:
--   * a G-side position (if the vertex was in `K.dom`), via
--     `f i = G.cod[i]` composed with `inject+`, or
--   * a fresh pruned-K-side position (via an index lookup in `nonMem K.dom`).
--------------------------------------------------------------------------------

module Categories.APROP.Hypergraph.Prune where

open import Data.Fin using (Fin; inject+; raise)
open import Data.Fin.Properties using (_≟_)
open import Data.List using (List; length; filter; allFin)
open import Data.List.Relation.Unary.Any using (index)
open import Data.Nat using (ℕ; _+_)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_]′)
open import Relation.Nullary.Decidable using (¬?; yes; no)

--------------------------------------------------------------------------------
-- Non-members of a Fin list.

module _ {n : ℕ} where
  open import Data.List.Membership.DecPropositional (_≟_ {n = n}) using (_∈?_)
  open import Data.List.Membership.Propositional using (_∈_)
  open import Data.List.Membership.Propositional.Properties
    using (∈-filter⁺; ∈-allFin)

  -- The Fin values not present in `xs`.
  nonMem : List (Fin n) → List (Fin n)
  nonMem xs = filter (λ v → ¬? (v ∈? xs)) (allFin n)

  -- Count of Fin values not in `xs`.
  count-non : List (Fin n) → ℕ
  count-non xs = length (nonMem xs)

  -- Classify `v : Fin n` as either a member of `xs` (paired with its index
  -- into `xs`) or a non-member (paired with its index into `nonMem xs`).
  classify : (xs : List (Fin n)) (v : Fin n) → Fin (length xs) ⊎ Fin (count-non xs)
  classify xs v with v ∈? xs
  ... | yes v∈xs = inj₁ (index v∈xs)
  ... | no  v∉xs =
    inj₂ (index (∈-filter⁺ (λ u → ¬? (u ∈? xs)) (∈-allFin v) v∉xs))

--------------------------------------------------------------------------------
-- Remap combinator.
--
-- Given xs ⊂ Fin n and a target map f : Fin (length xs) → Fin m for
-- members of xs, produces Fin n → Fin (m + count-non xs) by routing
-- members to `inject+ (count-non xs) (f i)` and non-members to
-- `raise m j` where j is the non-member's index in `nonMem xs`.

module _ {n m : ℕ} where
  remap : (xs : List (Fin n)) → (Fin (length xs) → Fin m)
        → Fin n → Fin (m + count-non xs)
  remap xs f v = [ (λ i → inject+ (count-non xs) (f i))
                 , (λ j → raise m j)
                 ]′ (classify xs v)
