{-# OPTIONS --without-K #-}

--------------------------------------------------------------------------------
-- Per-axiom soundness proofs. Extracted from the Soundness catch-all
-- postulate as each axiom is discharged.
--
-- With the switch to hComposeP (pruned cospan composition), axioms where
-- LHS had strictly more vertices than RHS under the unpruned version now
-- have matching vertex counts (modulo +-identityʳ casts) and are
-- constructively provable.
--
-- Currently proved: ∅ (this file is a placeholder for now).
--
-- Strategy per axiom:
--   1. Identify LHS and RHS of the `⟪_⟫` translation.
--   2. Use `hId-count-non-dom ≡ 0` (or `⟪_⟫-dom-unique` for the count-non
--      of general ⟪f⟫.dom) to show the vertex counts match.
--   3. Construct the ≅ᴴ record field-by-field:
--      φ/φ⁻¹ via splitAt + case on the trivially-empty side.
--      ψ/ψ⁻¹ similarly (hId has no edges).
--      Labels, endpoints, elab: chase through the subst₂ + map-via-remapP
--      machinery.
--------------------------------------------------------------------------------

open import Categories.APROP

module Categories.APROP.Hypergraph.SoundnessAxioms (sig : APROPSignature) where

open APROP sig
open import Categories.APROP.Hypergraph.Core
open import Categories.APROP.Hypergraph.FromAPROP sig
open import Categories.APROP.Hypergraph.Translation sig
open import Categories.APROP.Hypergraph.Iso
open import Categories.APROP.Hypergraph.PrunedCompose sig
open import Categories.APROP.Hypergraph.Invariant sig

open import Categories.APROP.Hypergraph.Prune
  using (nonMem; count-non; AllIn; AllIn→count-non-zero)

open import Data.Empty using (⊥-elim)
open import Data.Fin using (Fin; zero; suc; inject+; raise; splitAt)
open import Data.Fin.Properties using (splitAt-inject+; splitAt-raise)
open import Data.List using (List; []; _∷_; map; length)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Nat.Properties using (+-identityʳ)
open import Data.Sum using ([_,_]′; inj₁; inj₂)
open import Function using (id)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; sym; trans; subst; subst₂)

--------------------------------------------------------------------------------
-- `idˡ`: `id ∘ f ≈Term f`.
--
-- Translation:
--   ⟪ id ∘ f ⟫ = hComposeP ⟪f⟫ (hId B)
-- where B is the codomain of f.
--
-- Key facts used:
--   * `hId B` has no edges (hId-nE ≡ 0 by induction on B).
--   * `hId B`.dom covers all vertices (hId-dom-covers).
--   * Therefore `count-non (hId B).dom ≡ 0` (hId-count-non-dom).
--
-- Consequence: the composite's vertex count is `⟪f⟫.nV + 0` and the
-- edge count is `⟪f⟫.nE + 0`. The iso with `⟪f⟫` is essentially
-- identity on the G-side with trivial coverage of the empty K-side.

-- First, a helper fact: hId has no edges.
hId-nE : ∀ A → Hypergraph.nE (hId A) ≡ 0
hId-nE unit       = refl
hId-nE (Var x)    = refl
hId-nE (A ⊗₀ B)   = cong₂-+ (hId-nE A) (hId-nE B)
  where
    cong₂-+ : ∀ {a b c d : ℕ} → a ≡ b → c ≡ d → a + c ≡ b + d
    cong₂-+ refl refl = refl
