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
-- header there), and by instantiating the deferred Kelly residual `permˢ-K` at
-- the concrete `Strict.Perm.PermK.permˢ-K`.
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
open import Categories.APROP.Hypergraph.Soundness.Strict.Perm.PermSupport sig _≟X_
import Categories.APROP.Hypergraph.Soundness.Strict.Tensor.TensorBraid sig _≟X_ as TB

--------------------------------------------------------------------------------

module _
  (permˢ-K : ∀ (V : Set) (_≟V_ : DecidableEquality V) (vlab : V → X)
           → Support.PermK V vlab)
  where

  module _ {A B C D : ObjTerm} (f : HomTerm A B) (g : HomTerm C D) where
    private
      module Brd = TB.Braid permˢ-K {A} {B} {C} {D} f g

    decodePˢ-⊗ : decodePˢ (f ⊗₁ g) ≈ˢ decodePˢ f ⊗ˢ decodePˢ g
    decodePˢ-⊗ = Brd.decodePˢ-⊗-cond Brd.Reconcile-e.kblockσ

--------------------------------------------------------------------------------
-- ## The UNCONDITIONAL ⊗-shape at the CONCRETE Kelly residual `PK.permˢ-K`
-- (axiom-free, discharged by `Strict.Perm.PermK` ⇐ `Strict.Perm.Braid`).  This has
-- the EXACT type of `PartI`'s / `Soundness`'s `decodePˢ-⊗` parameter, so
-- it closes the last residual of the strict soundness assembly.

import Categories.APROP.Hypergraph.Soundness.Strict.Perm.PermK sig _≟X_ as PK

decodePˢ-⊗-concrete
  : ∀ {A B C D} (f : HomTerm A B) (g : HomTerm C D)
  → decodePˢ (f ⊗₁ g) ≈ˢ decodePˢ f ⊗ˢ decodePˢ g
decodePˢ-⊗-concrete f g = decodePˢ-⊗ PK.permˢ-K f g
