{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- `SMCMacLaneAtoms` — the Sense-1 trust surface for the c'-chain.
--
-- Three fields, each a pure statement in the free symmetric monoidal
-- category over an arbitrary signature `(X, mor)`:
--
--   (1) `swap-atom-aligned`       — two adjacent independent steps commute
--                                  via σ-naturality + Mac Lane bookkeeping.
--   (2) `swap-with-rest-aligned`  — same with a non-trivial tail-list.
--   (4) `bridge-to-g-permute`     — two `Steps` sequences with a common
--                                  domain produce equivalent terms modulo
--                                  a single stack permutation.
--
-- The combinatorial topological-soundness atom from the APROP
-- `SwapAtomResidual` (formerly `swap-already-fires`) is NOT here — it
-- lives in `Categories.Hypergraph.LinearityCombinatorial`, since it has
-- no SMC content (just `AllFire`/`extract-prefix` combinatorics).
--
-- This record is `--safe --without-K` and has no APROP imports.  The
-- bridge `Discharge.APROPMacLaneFromSMC` takes an instance + a
-- `LinearityCombinatorial` instance and produces an `APROPMacLaneAtoms`
-- value, closing the existing c'-chain at a strictly stricter abstraction
-- level.
--------------------------------------------------------------------------------

open import Categories.FreeMonoidal

module Categories.FreeSMC.MacLaneAtoms
  (d : FreeMonoidalData) ⦃ s≤v : Symm ≤ FreeMonoidalData.v d ⦄ where

open FreeMonoidalData d using (X)
open FreeMonoidal d
open import Categories.FreeSMC.Steps d

open import Data.List using (List; []; _∷_)
import Data.List.Relation.Binary.Permutation.Propositional as Perm
open import Data.Product using (_,_; _×_; proj₁; proj₂)

--------------------------------------------------------------------------------
-- The record.

record SMCMacLaneAtoms : Set where
  field
    --------------------------------------------------------------------
    -- (1) Mac Lane / Kelly atom on two adjacent independent steps.
    --
    -- Mathematically: `σ ∘ (f ⊗₁ g) ≈Term (g ⊗₁ f) ∘ σ` (already a
    -- `_≈Term_` axiom at `FreeMonoidal.agda:100`), threaded through
    -- `unflatten-++-≅` Mac Lane bookkeeping and the four locating
    -- permutations packaged in `IndependentSwap`.

    swap-atom-aligned
      : ∀ (e₁ e₂ : Step) (s : List X)
          (indep : IndependentSwap e₁ e₂ s)
      → ProcessEdges↭Goal
          (e₁ ∷ e₂ ∷ []) (e₂ ∷ e₁ ∷ [])
          s (proj₁ indep) (proj₂ indep)

    --------------------------------------------------------------------
    -- (2) Single swap with a non-trivial rest list of steps.
    --
    -- Same SMC content as (1), with the tail-list `xs ↭ ys` threaded
    -- through.

    swap-with-rest-aligned
      : ∀ (e₁ e₂ : Step) (xs ys : Steps) (s : List X)
          (rest-↭ : xs Perm.↭ ys)
          (af₁ : AllFire (e₁ ∷ e₂ ∷ xs) s)
          (af₂ : AllFire (e₂ ∷ e₁ ∷ ys) s)
      → ProcessEdges↭Goal
          (e₁ ∷ e₂ ∷ xs) (e₂ ∷ e₁ ∷ ys)
          s af₁ af₂

    --------------------------------------------------------------------
    -- (4) Bridge: two `Steps` sequences with a common domain produce
    -- equivalent terms modulo a stack permutation.
    --
    -- Heavily narrowed vs the APROP atom:
    --   * `{A B} (f g : HomTerm A B)` (the input morphisms) — gone.
    --     Only their compiled forms (`steps-f`, `steps-g`,
    --     `steps-f-reordered`) survive.
    --   * `(iso : ⟪f⟫ ≅ᴴ ⟪g⟫)` — gone.  The iso was unused in the
    --     conclusion of the APROP atom (only fed ψF derivation, done
    --     elsewhere via `Sub/IsoInducesEdgePerm.iso-induces-edge-residual`).
    --   * `full-dom-eq f g` — gone.  The bridge module substitutes
    --     through it before calling this atom.
    --   * `vlab`, `permute-via-vlab` — collapse in Sense 1 (the stack
    --     IS `List X`).
    --   * `subst₂ HomTerm (cong unflatten (full-dom-eq …)) refl …` —
    --     gone (substituted through).
    --
    -- Pure SMC content: under matching `AllFire` witnesses, two
    -- `process-steps` runs over the same domain produce equivalent
    -- terms modulo `permute (sym perm-↭) ∘ _`.

    bridge-to-g-permute
      : (steps-g steps-f-reordered : Steps)
        (dom : List X)
        (af-g : AllFire steps-g           dom)
        (af-r : AllFire steps-f-reordered dom)
        (perm-↭ :
          proj₁ (process-steps steps-g           dom af-g)
          Perm.↭
          proj₁ (process-steps steps-f-reordered dom af-r))
      → proj₂ (process-steps steps-g dom af-g)
        ≈Term
        permute (Perm.↭-sym perm-↭)
          ∘ proj₂ (process-steps steps-f-reordered dom af-r)
