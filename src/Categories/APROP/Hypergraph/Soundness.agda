{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- Soundness theorem for the strictified pipeline.
--
-- `soundness` delegates to `Strict.Soundness.soundness-strict`, which is
-- assembled at the unconditional strict ⊗-shape
-- `Strict.Tensor.TensorKBlockFinal.decodePˢ-⊗-concrete`.  That path proves
-- `⟪f⟫ ≅ᴴ ⟪g⟫ → f ≈Term g` entirely inside the presented strict SMC `S`
-- (part (I)ˢ `st ≈ˢ decodePˢ` + part (II)ˢ `decodePˢ`-iso-invariance,
-- reflected via `embF`/`st-roundtrip` + the `bridge` cancellation),
-- with the single deep Kelly residual `permˢ-K` discharged axiom-free.
--------------------------------------------------------------------------------

open import Categories.APROP
open import Categories.APROP.Hypergraph.Solver.Signature using (APROPSignatureDec)

module Categories.APROP.Hypergraph.Soundness
  (sig-dec : APROPSignatureDec) where

open APROPSignatureDec sig-dec using (sig; _≟X_)
open APROP sig
open import Categories.APROP.Hypergraph.Model.Iso
open import Categories.APROP.Hypergraph.Model.Translation sig using (⟪_⟫)

import Categories.APROP.Hypergraph.Soundness.Strict.Soundness sig _≟X_ as SA

--------------------------------------------------------------------------------
-- The soundness theorem.

opaque
  soundness : ∀ {A B} {f g : HomTerm A B} → ⟪ f ⟫ ≅ᴴ ⟪ g ⟫ → f ≈Term g
  soundness = SA.soundness-strict
