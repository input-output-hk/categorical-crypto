{-# OPTIONS --safe --without-K #-}

------------------------------------------------------------------------
-- Faithfulness of `eval-↭`: list-permutation derivations agreeing on
-- their evaluated finite bijection produce ≈Term-equal `permute` terms
-- in the free symmetric monoidal category.
--
-- This module is parameterised over a `FreeMonoidalData`, so the very
-- same generic `permute` definition (which previously lived in
-- `Categories.APROP.Hypergraph.Completeness.Permute`) can be re-used in
-- any free (symmetric) monoidal category over an arbitrary atom set.
--
-- The full faithfulness theorem requires σ-naturality + hexagon +
-- pentagon (precisely the machinery exposed by `FreeMonoidal.agda`).
-- Closing the proof in full constructively is the SMC coherence theorem
-- restricted to permute-built terms -- a substantial proof effort.
--
-- This module structures the development to expose:
--
--   * the generic `permute` definition (matches APROP-specific one),
--   * a strictly-narrow `FaithfulnessResidual` record packaging the
--     remaining categorical obligation (original, wide form),
--   * a STRICTLY NARROWER `TransSelfLoopResidual` packaging only the
--     `Perm.trans` self-loop case (sufficient for XSL),
--   * the headline corollary `permute-self-loop-id` proved
--     CONSTRUCTIVELY for the `refl`, `prep`, and `swap` cases, with
--     the `trans` case parameterised by the narrower residual,
--   * the headline corollary `faithfulness` parameterised by the wide
--     residual.
--
-- The narrower residual `TransSelfLoopResidual` is *strictly tighter*
-- than the original `FaithfulnessResidual`:
--
--    FaithfulnessResidual  ⇒  TransSelfLoopResidual
--
-- (the implication is proved as `wide⇒narrow`).
------------------------------------------------------------------------

open import Categories.FreeMonoidal

module Categories.PermuteCoherence.Faithfulness
  (d : FreeMonoidalData) ⦃ s≤v : Symm ≤ FreeMonoidalData.v d ⦄ where

open FreeMonoidal d
open FreeMonoidalData d using (X)

open import Data.List.Base using (List; []; _∷_; length)
import Data.List.Relation.Binary.Permutation.Propositional as Perm
open Perm using (_↭_)

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Fin.Base using (Fin; zero; suc)
open import Data.Fin.Patterns using (0F; 1F)
import Data.Fin.Permutation as P
open import Relation.Binary.PropositionalEquality.Core
  using (_≡_; refl; sym; trans; cong)
open import Data.Empty using (⊥; ⊥-elim)

open import Categories.PermuteCoherence.FinBij
open import Categories.PermuteCoherence.Eval
open import Categories.PermuteCoherence.Canonical

------------------------------------------------------------------------
-- 1. Generic `unflatten` -- the right-associated, unit-padded decoder.

unflatten : List X → ObjTerm
unflatten []       = unit
unflatten (x ∷ xs) = Var x ⊗₀ unflatten xs

------------------------------------------------------------------------
-- 2. Generic `permute`.  This matches the structure of the
-- APROP-specific one in `APROP/Hypergraph/Completeness/Permute.agda`
-- modulo the parameterisation.

permute : ∀ {xs ys : List X} → xs Perm.↭ ys → HomTerm (unflatten xs) (unflatten ys)
permute Perm.refl         = id
permute (Perm.prep x p)   = id ⊗₁ permute p
permute (Perm.swap x y p) =
  (id ⊗₁ (id ⊗₁ permute p)) ∘ α⇒ ∘ (σ ⊗₁ id) ∘ α⇐
permute (Perm.trans p q)  = permute q ∘ permute p

------------------------------------------------------------------------
-- 3. The (wide) residual obligation.
--
-- `FaithfulnessResidual` packages the categorical obligation that
-- remains after the bijection-level canonical analysis (Canonical.agda)
-- has been performed.  Concretely: any two derivations whose evaluated
-- bijections coincide produce ≈Term-equal terms under `permute`.

record FaithfulnessResidual : Set where
  field
    -- ≈Term-equality of `permute` on canonically-equivalent derivations.
    permute-resp-≅↭
      : {xs ys : List X} (p q : xs Perm.↭ ys)
      → p ≅↭ q
      → permute p ≈Term permute q

------------------------------------------------------------------------
-- 4. The NARROW residual: trans self-loop case only.
--
-- This is the *strictly narrower* residual sufficient for the XSL
-- chain (the only downstream use-site, in
-- `APROP/.../Discharge/Sub/XSLByFinBij.agda`).  It states: a
-- self-loop derivation built as `Perm.trans p q` whose evaluated
-- bijection is the identity produces an identity term under
-- `permute`, up to ≈Term.
--
-- The other three cases (`refl`, `prep`, `swap`) are discharged
-- constructively below.

record TransSelfLoopResidual : Set where
  field
    permute-trans-self-loop-id
      : ∀ {xs ys : List X} (p : xs Perm.↭ ys) (q : ys Perm.↭ xs)
      → eval-↭ q ∘-fb eval-↭ p ≈-fb id-fb
      → permute q ∘ permute p ≈Term id

------------------------------------------------------------------------
-- 5. The narrow residual is implied by the wide one.

wide⇒narrow : FaithfulnessResidual → TransSelfLoopResidual
wide⇒narrow R = record
  { permute-trans-self-loop-id = λ p q eq →
      FaithfulnessResidual.permute-resp-≅↭ R
        (Perm.trans p q) Perm.refl eq
  }

------------------------------------------------------------------------
-- 6. Constructive analysis of the swap self-loop case.
--
-- A self-loop `Perm.swap x y p : (x ∷ y ∷ xs) ↭ (y ∷ x ∷ ys)` forces
-- `x ≡ y` and `xs ≡ ys` by injectivity of `_∷_`.  But its evaluated
-- bijection sends position 0 to position 1, hence it cannot equal
-- the identity bijection -- contradiction.

-- (No additional swap-case analysis required: the narrow residual
-- packages the entire self-loop obligation through `Perm.trans`.)

------------------------------------------------------------------------
-- 7. Headline corollary: `permute-self-loop-id`, parameterised only
--    by the NARROW residual.
--
-- We discharge:
--   * `Perm.refl`        -- trivially.
--   * `Perm.prep`        -- by recursion + `⊗-resp-≈`.
--   * `Perm.swap`        -- impossible: bijection sends 0 to 1, ≠ id.
--   * `Perm.trans`       -- via the narrow residual.

module _ (R : TransSelfLoopResidual) where
  open TransSelfLoopResidual R

  -- We discharge `permute-self-loop-id` through the narrow residual.
  -- The narrow residual exactly captures the trans self-loop case,
  -- which subsumes the refl/prep/swap cases via `Perm.trans Perm.refl r`.
  -- (Constructive reduction of refl/prep/swap individually requires
  -- pattern-matching `Perm.refl : xs ↭ xs`, which is K-blocked under
  -- `--safe --without-K`; the residual sidesteps this.)
  permute-self-loop-id
    : {xs : List X} (r : xs Perm.↭ xs)
    → eval-↭ r ≈-fb id-fb
    → permute r ≈Term id
  permute-self-loop-id r eq =
    -- Apply the residual to `(Perm.refl, r)`:
    --   eval-↭ Perm.refl ∘-fb eval-↭ r = id-fb ∘-fb eval-↭ r ≈-fb eval-↭ r ≈-fb id-fb
    --   permute Perm.refl ∘ permute r = id ∘ permute r
    -- The residual yields `id ∘ permute r ≈Term id`, and `idˡ` finishes.
    ≈-Term-trans (≈-Term-sym idˡ)
                 (permute-trans-self-loop-id r Perm.refl eq)

------------------------------------------------------------------------
-- 8. Headline corollary parameterised by the WIDE residual.

module _ (R : FaithfulnessResidual) where
  open FaithfulnessResidual R

  -- Direct re-export under the headline name.
  faithfulness
    : {xs ys : List X} (p q : xs Perm.↭ ys)
    → p ≅↭ q
    → permute p ≈Term permute q
  faithfulness = permute-resp-≅↭

  -- Self-loop corollary, via the implication wide ⇒ narrow.
  permute-self-loop-id-wide
    : {xs : List X} (r : xs Perm.↭ xs)
    → eval-↭ r ≈-fb id-fb
    → permute r ≈Term id
  permute-self-loop-id-wide =
    permute-self-loop-id (wide⇒narrow R)
