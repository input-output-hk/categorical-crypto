{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- The FULL strict decoder `decodePˢ`: the algorithmic decoder run inside
-- the presented strict SMC `S` (`FreeStrictSMC.Build` at `FlatGen`).
--
--   decodePˢ f = castˢ (⟪⟫-domL f) (⟪⟫-codL f)
--                  (permuteˢ (finalPermˢ f) ∘ˢ proj₂ (runˢ ⟪ f ⟫))
--
-- where `runˢ H = process-edgesˢ (range H.nE) H.dom` is the strict run and
-- `finalPermˢ f` is the closing permutation of the final stack onto `cod`.
-- Totality is NOT re-proved: the strict run's stack IS the non-strict
-- `process-edges` (the strict decoder pairs that fold with its term), so
-- the success witness of the live decoder (`decode-attempt-LinearP`)
-- transfers with no cast at all.  WHICH permutation it is
-- never matters downstream: the atom / σ / Agen / ⊗ shapes collapse
-- `permuteˢ (finalPermˢ f)` by RIGIDITY (`perm-rigidˢ` at the `Unique`
-- codomain of `⟪ f ⟫`) and the ∘-shape transports it opaquely, so nothing
-- ever reads an `extract-exact ... ≡ just _` equation for it.
--------------------------------------------------------------------------------

open import Categories.APROP
open import Relation.Binary using (DecidableEquality)

module Categories.APROP.Hypergraph.Soundness.Strict.Decode.Decode
  (sig : APROPSignature)
  (_≟X_ : DecidableEquality (APROPSignature.X sig))
  where

open APROP sig

open import Categories.APROP.Hypergraph.Model.Core using (Hypergraph)
open import Categories.APROP.Hypergraph.Model.FromAPROP sig
  using (FlatGen; flatten; range)
open import Categories.APROP.Hypergraph.Model.Translation sig
  using (⟪_⟫; ⟪⟫-domL; ⟪⟫-codL)
open import Categories.APROP.Hypergraph.Soundness.Discharge.DecodeAttemptLinearP sig
  using (decode-attempt-LinearP)

open import Categories.APROP.Hypergraph.Soundness.Strict.Decode.Decoder sig _≟X_ public

open import Data.Fin using (Fin)
open import Data.List using (List; map)
open import Data.Product using (Σ-syntax; proj₁; proj₂)
import Data.List.Relation.Binary.Permutation.Propositional as Perm

--------------------------------------------------------------------------------
-- Per-hypergraph strict run.

module Run (H : Hypergraph FlatGen) where
  private module H = Hypergraph H
  open StrictDecoder H public

  runˢ : Σ[ s ∈ List (Fin H.nV) ] HomS (map vl H.dom) (map vl s)
  runˢ = process-edgesˢ (range H.nE) H.dom

  s-finˢ : List (Fin H.nV)
  s-finˢ = proj₁ runˢ

--------------------------------------------------------------------------------
-- Transfer of the live decoder's success witness: the strict final stack
-- permutes onto `H.cod`.

module _ {A B : ObjTerm} (f : HomTerm A B) where
  private
    module RF = Run ⟪ f ⟫
    module Hf = Hypergraph ⟪ f ⟫

  -- The non-strict totality witness IS the strict one: `RF.s-finˢ` is
  -- `process-all-edges ⟪f⟫ dom` by definition of the strict run.
  finalPermˢ : RF.s-finˢ Perm.↭ Hf.cod
  finalPermˢ = decode-attempt-LinearP f

--------------------------------------------------------------------------------
-- The full strict decoder.

decodePˢ : ∀ {A B} (f : HomTerm A B) → HomS (flatten A) (flatten B)
decodePˢ f =
  castˢ (⟪⟫-domL f) (⟪⟫-codL f)
    (Run.permuteˢ ⟪ f ⟫ (finalPermˢ f) ∘ˢ proj₂ (Run.runˢ ⟪ f ⟫))
