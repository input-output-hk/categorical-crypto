{-# OPTIONS --safe --without-K #-}

------------------------------------------------------------------------
-- Faithfulness of `eval-↭`: list-permutation derivations agreeing on
-- their evaluated finite bijection produce ≈Term-equal `permute` terms
-- in the free symmetric monoidal category.
--
-- Parameterised over `FreeMonoidalData`, so the generic `permute` is
-- reusable in any free (symmetric) monoidal category.  This module
-- exposes:
--
--   * the generic `permute` definition,
--   * the wide `FaithfulnessResidual` (the remaining categorical
--     obligation) and the strictly narrower `TransSelfLoopResidual`
--     (the `Perm.trans` self-loop case, sufficient for XSL; implied by
--     the wide one via `wide⇒narrow`),
--   * `permute-self-loop-id` (parameterised by the narrow residual) and
--     `permute-self-loop-id-wide` (parameterised by the wide one).
------------------------------------------------------------------------

open import Categories.FreeMonoidal

module Categories.PermuteCoherence.Faithfulness
  (d : FreeMonoidalData) ⦃ s≤v : Symm ≤ FreeMonoidalData.v d ⦄ where

open FreeMonoidal d
open FreeMonoidalData d using (X)

open import Data.List.Base using (List; []; _∷_; _++_; length)
import Data.List.Relation.Binary.Permutation.Propositional as Perm
open Perm using (_↭_)

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Fin.Base using (Fin; zero; suc)
open import Data.Fin.Patterns using (0F; 1F)
import Data.Fin.Permutation as P
open import Relation.Binary.PropositionalEquality.Core
  using (_≡_; refl; sym; trans; cong)
open import Data.Empty using (⊥; ⊥-elim)

open import Categories.Category.Monoidal using (Monoidal)
open import Categories.Category.Monoidal.Utilities Monoidal-FreeMonoidal
  using (_⊗ᵢ_)
open import Categories.Morphism FreeMonoidal using (_≅_; module ≅)
open Monoidal Monoidal-FreeMonoidal using (unitorˡ; associator)

open import Categories.PermuteCoherence.FinBij
open import Categories.PermuteCoherence.Eval
open import Categories.PermuteCoherence.Canonical

------------------------------------------------------------------------
-- 0. Dual associator commutativity, derived from `α-comm`:
--    α⇐ ∘ (h ⊗₁ (i ⊗₁ j)) ≈Term ((h ⊗₁ i) ⊗₁ j) ∘ α⇐.

α⇐-comm
  : ∀ {a b c a′ b′ c′ : ObjTerm}
      {h : HomTerm a a′} {i : HomTerm b b′} {j : HomTerm c c′}
  → α⇐ ∘ (h ⊗₁ (i ⊗₁ j)) ≈Term ((h ⊗₁ i) ⊗₁ j) ∘ α⇐
α⇐-comm {h = h} {i} {j} =
  ≈-Term-trans (≈-Term-sym idʳ)
  (≈-Term-trans (∘-resp-≈ ≈-Term-refl (≈-Term-sym α⇒∘α⇐≈id))
  (≈-Term-trans assoc
  (≈-Term-trans (∘-resp-≈ ≈-Term-refl (≈-Term-sym assoc))
  (≈-Term-trans (∘-resp-≈ ≈-Term-refl (∘-resp-≈ (≈-Term-sym α-comm) ≈-Term-refl))
  (≈-Term-trans (∘-resp-≈ ≈-Term-refl assoc)
  (≈-Term-trans (≈-Term-sym assoc)
  (≈-Term-trans (∘-resp-≈ α⇐∘α⇒≈id ≈-Term-refl)
                 idˡ)))))))

------------------------------------------------------------------------
-- 1. Generic `unflatten` -- the right-associated, unit-padded decoder.

unflatten : List X → ObjTerm
unflatten []       = unit
unflatten (x ∷ xs) = Var x ⊗₀ unflatten xs

------------------------------------------------------------------------
-- 1b. `unflatten` distributes over `_++_` up to a coherence iso.

unflatten-++-≅
  : ∀ (xs ys : List X)
  → unflatten (xs ++ ys) ≅ unflatten xs ⊗₀ unflatten ys
unflatten-++-≅ []       ys = ≅.sym unitorˡ
unflatten-++-≅ (x ∷ xs) ys =
  ≅.trans (≅.refl ⊗ᵢ unflatten-++-≅ xs ys) (≅.sym associator)

------------------------------------------------------------------------
-- 2. Generic `permute`.

permute : ∀ {xs ys : List X} → xs Perm.↭ ys → HomTerm (unflatten xs) (unflatten ys)
permute Perm.refl         = id
permute (Perm.prep x p)   = id ⊗₁ permute p
permute (Perm.swap x y p) =
  (id ⊗₁ (id ⊗₁ permute p)) ∘ α⇒ ∘ (σ ⊗₁ id) ∘ α⇐
permute (Perm.trans p q)  = permute q ∘ permute p

------------------------------------------------------------------------
-- 3. The (wide) residual: any two derivations whose evaluated bijections
-- coincide produce ≈Term-equal terms under `permute`.

record FaithfulnessResidual : Set where
  field
    permute-resp-≅↭
      : {xs ys : List X} (p q : xs Perm.↭ ys)
      → p ≅↭ q
      → permute p ≈Term permute q

------------------------------------------------------------------------
-- 4. The NARROW residual (trans self-loop only): a self-loop built as
-- `Perm.trans p q` with identity evaluated bijection produces an identity
-- term under `permute`.  Sufficient for the XSL chain.

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
-- 6. Headline corollary `permute-self-loop-id`, via the NARROW residual.
--
-- The narrow residual captures the trans self-loop case, which subsumes
-- refl/prep/swap via `Perm.trans Perm.refl r` (matching `Perm.refl`
-- directly is K-blocked under `--safe --without-K`).

module _ (R : TransSelfLoopResidual) where
  open TransSelfLoopResidual R

  permute-self-loop-id
    : {xs : List X} (r : xs Perm.↭ xs)
    → eval-↭ r ≈-fb id-fb
    → permute r ≈Term id
  permute-self-loop-id r eq =
    ≈-Term-trans (≈-Term-sym idˡ)
                 (permute-trans-self-loop-id r Perm.refl eq)

------------------------------------------------------------------------
-- 7. Headline corollary parameterised by the WIDE residual.

module _ (R : FaithfulnessResidual) where
  open FaithfulnessResidual R

  permute-self-loop-id-wide
    : {xs : List X} (r : xs Perm.↭ xs)
    → eval-↭ r ≈-fb id-fb
    → permute r ≈Term id
  permute-self-loop-id-wide =
    permute-self-loop-id (wide⇒narrow R)
