{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- Phase 8 — THE FINAL WIRING.  Closes the strict ⊗-shape
--
--     decodePˢ-⊗ : decodePˢ (f ⊗₁ g) ≈ˢ decodePˢ f ⊗ˢ decodePˢ g    (UNCOND.)
--
-- by feeding `TensorBraid.Braid.decodePˢ-⊗-cond` the LAST residual — the
-- K-block braid `KBlockσ` — which `Braid.Reconcile-e.kblockσ` discharges from
-- three already-proven theorems (`process-edges-equivariantˢ`,
-- `stack-sepˢ`/`term-sepᵛ`, `box-conjᵛ`/`block-swap-comm`; see the derivation's
-- header there).
--
-- ZERO postulates, `--safe --without-K`.
--------------------------------------------------------------------------------

open import Categories.APROP
open import Relation.Binary using (DecidableEquality)

module Categories.APROP.Hypergraph.Soundness.Strict.Tensor.TensorKBlockFinal
  (sig : APROPSignature)
  (_≟X_ : DecidableEquality (APROPSignature.X sig))
  where

open APROP sig

open import Categories.APROP.Hypergraph.Soundness.Strict.Decode.Decode sig _≟X_
import Categories.APROP.Hypergraph.Soundness.Strict.Tensor.TensorBraid sig _≟X_ as TB

--------------------------------------------------------------------------------
-- ## The UNCONDITIONAL ⊗-shape.  `TensorBraid` supplies the conditional shape
-- and `Reconcile-e.kblockσ` its last hypothesis; this has the EXACT type of
-- `PartI`'s / `Strict.Soundness`'s `decodePˢ-⊗` parameter, so it closes the
-- last residual of the strict soundness assembly.

decodePˢ-⊗-concrete
  : ∀ {A B C D} (f : HomTerm A B) (g : HomTerm C D)
  → decodePˢ (f ⊗₁ g) ≈ˢ decodePˢ f ⊗ˢ decodePˢ g
decodePˢ-⊗-concrete f g = Brd.decodePˢ-⊗-cond Brd.Reconcile-e.kblockσ
  where module Brd = TB.Braid f g
