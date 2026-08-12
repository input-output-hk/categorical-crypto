{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- The ⊗-SHAPE of the strict decoder `decodePˢ` (strict analogue of the
-- former non-strict `DecodeTensorShape`).
--
--   decodePˢ-⊗ : decodePˢ (f ⊗₁ g) ≈ˢ decodePˢ f ⊗ˢ decodePˢ g   (mod casts)
--
-- `⟪ f ⊗₁ g ⟫ = hTensor ⟪ f ⟫ ⟪ g ⟫`, with vertices `G.nV + K.nV` (G's then
-- K's, shifted), edges `range (G.nE + K.nE) = gblk ++ kblk` (DEFINITIONAL,
-- `gblk = map (_↑ˡ K.nE)(range G.nE)`, `kblk = map (G.nE ↑ʳ_)(range K.nE)`),
-- and boundary `map injL G.dom ++ map injR K.dom` / `… cod …`.
--
-- CRITICAL ASYMMETRY (the documented finding — NOT re-discovered here).  The
-- ⊗-shape is NOT two separability frames.  `edge-stepˢ` PREPENDS fired outputs:
--
--   * the RIGHT frame (untouched region = SUFFIX) works — this is the PROVEN
--     `Decoder.term-sepᵛ`.  It factors the G-block run over `C.dom =
--     map injL G.dom ++ map injR K.dom` as `(G-run on map injL G.dom) ⊗ᵛ
--     idᵛ {map injR K.dom}` (the untouched K-input is a suffix).
--   * the LEFT frame is FALSE for any firing block: in `hTensor G K`, after
--     G's block fires (leaving `G.cod ++ K.dom`-shaped stack), K's edges act on
--     the K-input suffix and PREPEND K's outputs in FRONT of `G.cod`, producing
--     a BRAIDED form (`SeparableStack`'s obstruction note: no left frame).
--
-- So the clean `decodePˢ f ⊗ˢ decodePˢ g` is recovered ONLY at the whole-decode
-- level, where the final extract-exact permutation `finalPermˢ (f ⊗₁ g)`
-- re-sorts the braided K-outputs back behind `G.cod`.  This is exactly the σ/K
-- content; in the strict SMC it collapses to the `σˢ`/`σ-hexˢ` machinery of
-- `Strict/Perm/Braid.agda` + `Strict/Decode/DecodeSigma.agda` (`σ-hexˢʳ`) and is
-- discharged
-- by `perm-rigidˢ` on the final permutation.
--------------------------------------------------------------------------------

open import Categories.APROP
open import Relation.Binary using (DecidableEquality)

module Categories.APROP.Hypergraph.Soundness.Strict.Decode.DecodeTensor
  (sig : APROPSignature)
  (_≟X_ : DecidableEquality (APROPSignature.X sig))
  where

open APROP sig

open import Categories.APROP.Hypergraph.Model.Translation sig using (⟪_⟫; ⟪⟫-domL; ⟪⟫-codL)

open import Categories.APROP.Hypergraph.Soundness.Strict.Decode.Decode sig _≟X_

open import Data.Product using (proj₂)
open import Relation.Binary.PropositionalEquality using (refl; sym)

module Tensor {A B C D : ObjTerm}
  (f : HomTerm A B) (g : HomTerm C D)
  -- RESIDUAL 1 (the K-block braid + final reconciliation, folded into a
  -- single `≈ˢ` between the C-run inner term and the clean tensor — the
  -- strict, whole-decode-level analogue of `DecodeTensorShape`'s
  -- σ-resort).  Stated at the boundary objects, hence cast-FREE.
  (reconcileˢ
    : Run.permuteˢ ⟪ f ⊗₁ g ⟫ (finalPermˢ (f ⊗₁ g))
        ∘ˢ proj₂ (Run.runˢ ⟪ f ⊗₁ g ⟫)
      ≈ˢ castˢ (sym (⟪⟫-domL (f ⊗₁ g))) (sym (⟪⟫-codL (f ⊗₁ g)))
          (decodePˢ f ⊗ˢ decodePˢ g))
  where

  -- the ⊗-shape: boundaries align definitionally (flatten distributes over
  -- ⊗₀ as `_++_`), so the statement is cast-free.
  decodePˢ-⊗ : decodePˢ (f ⊗₁ g) ≈ˢ decodePˢ f ⊗ˢ decodePˢ g
  decodePˢ-⊗ =
    viaˢ (cast-≈̂ {p = ⟪⟫-domL (f ⊗₁ g)} {q = ⟪⟫-codL (f ⊗₁ g)})
         reconcileˢ
         (≈̂-sym (cast-≈̂ {p = sym (⟪⟫-domL (f ⊗₁ g))}
                        {q = sym (⟪⟫-codL (f ⊗₁ g))}))

--------------------------------------------------------------------------------
-- `decodePˢ-⊗` is reduced to the single boundary residual `reconcileˢ`,
-- discharged in `Strict/Tensor/TensorReconcile.agda`: it re-sorts the braided
-- K-block outputs (see CRITICAL ASYMMETRY above) back behind `G.cod` via the
-- `σˢ`/`σ-hexˢʳ` block-braid and the final `perm-rigidˢ`.  Substrate there:
-- `process-edgesˢ-++` (run split over `gblk ++ kblk`) and, for the G-side, the
-- proven right-frame `Decoder.term-sepᵛ` applied at `R = map injR K.dom`.
--------------------------------------------------------------------------------
