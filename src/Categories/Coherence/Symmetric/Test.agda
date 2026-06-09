{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- Test suite & documentation for the string-diagram solver infrastructure
-- (`Categories.Coherence.Symmetric`).  Checking this module checks the whole
-- suite.
--
-- ARCHITECTURE.  The engine follows TensorRocq (arXiv:2604.17592): free-SMC
-- terms over a generator signature are translated to hypergraphs (`⟪_⟫`),
-- where "only connectivity matters"; a *verified* decision procedure
-- (`findIso`, sound by the postulate-free theorem `soundness-full-wired`)
-- turns a hypergraph isomorphism into an equation in any target SMC `C`.
-- All *search* (position finding, sub-hypergraph matching, context carving)
-- is deliberately UNVERIFIED: a wrong search result simply fails the final
-- `findIso` certification and the call does not type-check.  Soundness rests
-- only on the verified gate — searches fail closed.
--
-- THE TOOL PALETTE (in `Setup` scope, in increasing power):
--
--   * `solveH! f g`        — discharge a *coherence* equation: `f ≈ g` holds
--                            for free because both sides have the same string
--                            diagram.                      → `Test.Coherence`
--   * `rewriteH!`          — rewrite with a *rule* `⟦lᵗ⟧ ≈ ⟦rᵗ⟧` at a position
--                            the caller pins down with two context terms.
--                                                          → `Test.Rewrite`
--   * `rewriteAuto(ₙ)!`    — the position is found by structural focusing
--                            (`focusAt`/`focusAll`); the redex must be a
--                            *subterm* of `s` (occurrence `n` selectable).
--                                                          → `Test.Rewrite`
--   * `rewriteDeep!`       — the position is found on the *hypergraph*
--                            (`deepFoc`: sub-match → hole-carve → decode), so
--                            the redex need only be a connected sub-diagram —
--                            rewriting modulo deformation.    → `Test.Deep`
--
-- KNOWN LIMITATIONS (each demonstrated by a probe in the file cited):
--
--   * Rule LHSs with bare identity wires (`p ⊗ id`) are not matchable by the
--     edge-driven deep search — state the rule without padding, or use
--     `rewriteH!`.                       → `Test.Deep.deep-id-wire-limitation`
--   * Purely structural rule LHSs (`σ`, `id`, coherence morphisms) have
--     edge-free hypergraphs — they are coherence facts; use `solveH!`.
--                                     → `Test.Deep.deep-structural-limitation`
--   * Non-convex occurrences are rejected by the carve (correctly: no
--     pushout complement exists).      → `Test.Deep.deep-non-convex-rejected`
--   * `focusAt`'s leaf test compares the rule's interface objects `P`, `Q`
--     literally (decidable `ObjTerm` equality); inside the redex matching is
--     up to SMC structure.              → `Test.Rewrite.test-unitˡ-noisy`
--   * `deepFoc` takes the first match (no occurrence index yet); the
--     syntactic path has `rewriteAutoₙ!`.
--
-- Backend-internal smoke tests (raw `findIso`/`subMatch`/`solveH` at fixed
-- signatures) live next to their subjects in
-- `Categories.APROP.Hypergraph.Solver.{Tests, SubMatchTests, InterpretTests}`.
--------------------------------------------------------------------------------

open import Level using (Level)
open import Categories.Category.Monoidal.Bundle using (SymmetricMonoidalCategory)

module Categories.Coherence.Symmetric.Test
  {o ℓ e : Level} (C : SymmetricMonoidalCategory o ℓ e) where

import Categories.Coherence.Symmetric.Test.Coherence
import Categories.Coherence.Symmetric.Test.Rewrite
import Categories.Coherence.Symmetric.Test.Deep

module Coherence = Categories.Coherence.Symmetric.Test.Coherence C
module Rewrite   = Categories.Coherence.Symmetric.Test.Rewrite   C
module Deep      = Categories.Coherence.Symmetric.Test.Deep      C
