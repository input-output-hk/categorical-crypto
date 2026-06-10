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
--   * `rewriteDeep(ₙ)!`    — the position is found on the *hypergraph*
--                            (`deepFocₙ`: sub-match enumeration → hole-carve
--                            with retry → decode), so the redex need only be
--                            a connected sub-diagram — rewriting modulo
--                            deformation.  `n` indexes the carvable (convex)
--                            occurrences in match order.
--                                          → `Test.Deep`, `Test.DeepArity`
--   * `rewriteDeepTo!`     — `rewriteDeepₙ!` landing on a caller-stated clean
--                            term: the step form for chained derivations (it
--                            keeps the carved frame out of all exposed types,
--                            which is essential for type-checking speed).
--                                          → `Test.Deep`, `Test.Frobenius`
--   * `normalize(To)!`     — DRIVERS: fire a `List Rule` (oriented rewrites
--                            with soundness proofs) at the first applicable
--                            position, repeatedly, to fuel-bounded
--                            exhaustion.  Re-searches after every firing, so
--                            a singleton list is "rewrite everywhere"; the
--                            search carries its own proof.  → `Test.Drivers`
--
-- SHOWCASE: `Test.Frobenius` derives the two alternative formulations of the
-- Frobenius law from the standard one by chains of deep rewrites — the
-- TensorRocq §5 worked example, end-to-end.
--
-- KNOWN LIMITATIONS (each demonstrated by a probe in the file cited):
--
--   * Rule LHSs with bare identity wires (`p ⊗ id`) are not matchable by the
--     edge-driven deep search — state the rule without padding, or use
--     `rewriteH!`.                       → `Test.Deep.deep-id-wire-limitation`
--   * Purely structural rule LHSs (`σ`, `id`, coherence morphisms) have
--     edge-free hypergraphs — they are coherence facts; use `solveH!`.
--                                     → `Test.Deep.deep-structural-limitation`
--   * Occurrences overlapping themselves are rejected at the search's
--     injectivity check.                 → `Test.Deep.deep-overlap-rejected`
--   * Non-convex occurrences are rejected at the carve (correctly: no
--     pushout complement exists); the match retry skips them, so they never
--     mask a convex occurrence elsewhere.
--                            → `Test.DeepArity.deep-non-convex-rejected`,
--                              `Test.DeepArity.test-deep-retry`
--   * `focusAt`'s leaf test compares the rule's interface objects `P`, `Q`
--     literally (decidable `ObjTerm` equality); inside the redex matching is
--     up to SMC structure.              → `Test.Rewrite.test-unitˡ-noisy`
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
import Categories.Coherence.Symmetric.Test.DeepArity
import Categories.Coherence.Symmetric.Test.Drivers
import Categories.Coherence.Symmetric.Test.Frobenius

module Coherence = Categories.Coherence.Symmetric.Test.Coherence C
module Rewrite   = Categories.Coherence.Symmetric.Test.Rewrite   C
module Deep      = Categories.Coherence.Symmetric.Test.Deep      C
module DeepArity = Categories.Coherence.Symmetric.Test.DeepArity C
module Drivers   = Categories.Coherence.Symmetric.Test.Drivers   C
module Frobenius = Categories.Coherence.Symmetric.Test.Frobenius C
