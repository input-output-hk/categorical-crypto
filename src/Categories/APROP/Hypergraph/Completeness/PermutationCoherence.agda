{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- Step 1 of the "bounded permutation" refactor:
--
-- Every propositional permutation `xs ↭ ys` between flat atom lists
-- induces a coherence iso `unflatten xs ≅ unflatten ys` in the free
-- symmetric monoidal category.  The witness is built by structural
-- induction on the `_↭_` constructors using only α, σ and `_⊗ᵢ_`, so
-- its size is bounded by the size of the permutation derivation.
--
-- Soundness check (σ counter-example):
--   for `xs = [a, b]`, `ys = [b, a]`, the permutation `swap a b refl`
--   produces an iso whose `from` morphism is, up to associators,
--   the braiding `σ_{Var a, Var b}` — exactly the expected coherence
--   iso for the symmetry of `Var a ⊗ Var b` vs `Var b ⊗ Var a`.
--------------------------------------------------------------------------------

open import Categories.APROP

module Categories.APROP.Hypergraph.Completeness.PermutationCoherence
  (sig : APROPSignature) where

open APROP sig

open import Categories.APROP.Hypergraph.Completeness.Unflatten sig
  using (unflatten)

open import Data.List using (List; []; _∷_)

open import Categories.Category.Monoidal using (Monoidal)
open import Categories.Category.Monoidal.Utilities Monoidal-FreeMonoidal
  using (_⊗ᵢ_)
open import Categories.Morphism FreeMonoidal
  using (_≅_; module ≅)

open Monoidal Monoidal-FreeMonoidal using (associator)

import Data.List.Relation.Binary.Permutation.Propositional as Perm
open Perm using (_↭_; refl; prep; swap; trans)

--------------------------------------------------------------------------------
-- Right-associated braiding at the head of an unflattened list.
--
--   unflatten (x ∷ y ∷ xs) = Var x ⊗ (Var y ⊗ unflatten xs)
--                          ≅ (Var x ⊗ Var y) ⊗ unflatten xs    (α⇐)
--                          ≅ (Var y ⊗ Var x) ⊗ unflatten xs    (σ-iso ⊗ᵢ id)
--                          ≅ Var y ⊗ (Var x ⊗ unflatten xs)    (α⇒)
--                          = unflatten (y ∷ x ∷ xs).
--
-- We isolate this as a helper so the `swap` clause of `↭-to-≅`
-- doesn't need to spell out the three coherence steps in line.

swap-head-≅
  : ∀ x y (xs : List X)
  → unflatten (x ∷ y ∷ xs) ≅ unflatten (y ∷ x ∷ xs)
swap-head-≅ x y xs =
  ≅.trans (≅.sym associator)
  (≅.trans (σ-iso ⊗ᵢ ≅.refl)
           associator)

--------------------------------------------------------------------------------
-- Main converter: permutation ⇒ coherence iso.
--
-- Each case uses one of the four `_↭_` constructors:
--   refl       ↦ ≅.refl
--   prep x p   ↦ ≅.refl {Var x} ⊗ᵢ ↭-to-≅ p
--   swap x y p ↦ swap-head-≅ x y _  then  refl ⊗ᵢ refl ⊗ᵢ ↭-to-≅ p
--   trans p q  ↦ ≅.trans (↭-to-≅ p) (↭-to-≅ q)
--
-- The resulting iso lives entirely in the FreeMonoidal category and
-- its underlying `from`/`to` HomTerms are built from `id`, `α`, `σ`,
-- and `_⊗₁_` only — i.e. *structural* coherence morphisms.

↭-to-≅ : ∀ {xs ys : List X} → xs ↭ ys → unflatten xs ≅ unflatten ys
↭-to-≅ refl               = ≅.refl
↭-to-≅ (prep x p)         = ≅.refl ⊗ᵢ ↭-to-≅ p
↭-to-≅ {x ∷ y ∷ xs} {.y ∷ .x ∷ ys} (swap x y p) =
  ≅.trans (swap-head-≅ x y xs)
          (≅.refl ⊗ᵢ ≅.refl ⊗ᵢ ↭-to-≅ p)
↭-to-≅ (trans p q)        = ≅.trans (↭-to-≅ p) (↭-to-≅ q)
