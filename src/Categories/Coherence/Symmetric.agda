{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- Discharging free *symmetric-monoidal* coherence equations in an arbitrary
-- target SMC `C`, via the hypergraph solver.
--
-- This module is the reusable interface.  Open it as
--
--     open import Categories.Coherence.Symmetric C
--
-- to build your own diagram configurations.  It provides:
--
--   * `Setup`   — from an atom alphabet with decidable equality, an `arity`
--                 table describing the generators, an interpretation `⟦_⟧ᵖ₀` of
--                 the atoms as objects of `C`, and an index-keyed table giving
--                 each generator's interpreting morphism, it builds the
--                 `FinSignature` and opens the solver.  In scope afterwards:
--                   · `solveH!`  — discharge a free-SMC equation in `C`;
--                   · `rewriteH!` — diagrammatic *rewriting*: given a rule
--                                  `⟦ lᵗ ⟧₁ ≈ ⟦ rᵗ ⟧₁` and a position (two
--                                  context terms `pre`/`post`), rewrite `lᵗ`
--                                  to `rᵗ` inside a larger diagram, modulo SMC
--                                  structure (the `srw`/`zxrw` analogue);
--                   · `rewriteAuto!` — as `rewriteH!`, but the position is
--                                  *found* automatically (term-level focusing);
--                                  the caller supplies only the term, the rule
--                                  sides, and the rule proof (`rewriteAutoₙ!`
--                                  picks the `n`-th occurrence);
--                   · `rewriteDeep!` — as `rewriteAuto!`, but the position is
--                                  found on the *hypergraph* (subMatch →
--                                  hole-carve → decode), so the redex need
--                                  only be a connected sub-diagram of `⟪s⟫`,
--                                  not a subterm of `s` as written;
--                   · `S`        — the free-SMC term language (`S.Agen`, `S.∘`,
--                                  `S.⊗₁`, `S.σ`, `S.α⇒`, …);
--                   · `gen`      — the `i`-th generator as a free term;
--                   · `Tgt`      — `C`'s own vocabulary (`_∘_`, `id`, `_⊗₁_`,
--                                  `σ`, `α⇒`, `λ⇒`, …) and `⟦_⟧₀`/`⟦_⟧₁`.
--   * `Wiring`  — the signature/interpretation half of `Setup` on its own,
--                 exposing `dom`/`cod`/`⟦_⟧₀` and the type `GenTable` of an
--                 index-keyed generator interpretation.
--   * `C`       — `SymmetricMonoidalCategory C` opened as a module (`C.Obj`,
--                 `C.monoidal`, `C.HomReasoning`, `C.braiding`, …), and the
--                 `FreeMonoidal` vocabulary (`Symm`, `FreeMonoidalHelper`, …)
--                 a configuration typically needs.
--------------------------------------------------------------------------------

open import Level using (Level)
open import Categories.Category.Monoidal.Bundle using (SymmetricMonoidalCategory)

module Categories.Coherence.Symmetric
  {o ℓ e : Level} (C : SymmetricMonoidalCategory o ℓ e) where

open import Data.Fin using (Fin; zero; suc)
open import Data.Nat using (ℕ)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.Definitions using (DecidableEquality)

open import Categories.APROP using (module APROP)
open import Categories.FreeMonoidal public
import Categories.APROP.Hypergraph.Solver.FinSignature as FinSig
import Categories.APROP.Hypergraph.Solver.Interpret as Interp

module C = SymmetricMonoidalCategory C

--------------------------------------------------------------------------------
-- `Wiring` assembles, from an atom set with decidable equality, an `arity`
-- table describing the generators, and an interpretation `⟦_⟧ᵖ₀` of the atoms
-- as objects of `C`, the `FinSignature` and the object interpretation `⟦_⟧₀`.
-- It exposes `dom`/`cod`, the term language `S`, the `Solver`, and the type
-- `GenTable` of an index-keyed generator interpretation.

module Wiring
  {Atom : Set} (_≟A_ : DecidableEquality Atom)
  {n : ℕ}
  (let open FreeMonoidalHelper Symm Atom using (ObjTerm))
  (arity : Fin n → ObjTerm × ObjTerm)
  (⟦_⟧ᵖ₀ : Atom → C.Obj)
  where
  open FinSig _≟A_ arity public using (dom; cod; gen; genElim; finSig; finSigDec)
  module S = APROP finSig
  open Interp finSigDec public using (module Solver; module ObjInterp)
  open ObjInterp C ⟦_⟧ᵖ₀ public using (⟦_⟧₀)

  -- A generator interpretation, keyed by index: the `i`-th generator's morphism.
  GenTable : Set ℓ
  GenTable = (i : Fin n) → ⟦ dom i ⟧₀ C.⇒ ⟦ cod i ⟧₀

--------------------------------------------------------------------------------
-- `Setup` is `Wiring` plus the solver: given additionally the generator table
-- it opens the `Solver`, so a configuration has `solveH!`, the term language
-- `S`, the generator constructor `gen`, and the target vocabulary `Tgt` all in
-- scope.  The table is the last parameter, supplied inline with no
-- `⟦ dom i ⟧₀`-style annotation of its own (its type is `Wiring.GenTable`).

module Setup
  {Atom : Set} (_≟A_ : DecidableEquality Atom)
  {n : ℕ}
  (let open FreeMonoidalHelper Symm Atom using (ObjTerm))
  (arity : Fin n → ObjTerm × ObjTerm)
  (⟦_⟧ᵖ₀ : Atom → C.Obj)
  (⟦gen⟧ : Wiring.GenTable _≟A_ arity ⟦_⟧ᵖ₀)
  where
  open Wiring _≟A_ arity ⟦_⟧ᵖ₀ public
  open Solver C ⟦_⟧ᵖ₀ (genElim ⟦gen⟧) public
  open Tgt public
