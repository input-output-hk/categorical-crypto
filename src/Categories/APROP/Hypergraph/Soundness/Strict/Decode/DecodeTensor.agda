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
--     `Decoder.term-sepˢ`.  It factors the G-block run over `C.dom =
--     map injL G.dom ++ map injR K.dom` as `(G-run on map injL G.dom) ⊗ˢ
--     idˢ {map injR K.dom}` (the untouched K-input is a suffix).
--   * the LEFT frame is FALSE for any firing block: in `hTensor G K`, after
--     G's block fires (leaving `G.cod ++ K.dom`-shaped stack), K's edges act on
--     the K-input suffix and PREPEND K's outputs in FRONT of `G.cod`, producing
--     a BRAIDED form (`Separability`'s obstruction note proves no `term-sepˢ-ˡ`).
--
-- So the clean `decodePˢ f ⊗ˢ decodePˢ g` is recovered ONLY at the whole-decode
-- level, where the final extract-exact permutation `finalPermˢ (f ⊗₁ g)`
-- re-sorts the braided K-outputs back behind `G.cod`.  This is exactly the σ/K
-- content; in the strict SMC it collapses to the `σˢ`/`σ-hexˢ` machinery of
-- `Strict/Braid.agda` + `Strict/DecodeSigma.agda` (`σ-hexˢʳ`) and is discharged
-- by `perm-rigidˢ` on the final permutation.
--------------------------------------------------------------------------------

open import Categories.APROP
open import Relation.Binary using (DecidableEquality)

module Categories.APROP.Hypergraph.Soundness.Strict.Decode.DecodeTensor
  (sig : APROPSignature)
  (_≟X_ : DecidableEquality (APROPSignature.X sig))
  where

open APROP sig

open import Categories.APROP.Hypergraph.Model.Core using (Hypergraph)
open import Categories.APROP.Hypergraph.Model.FromAPROP sig
  using (FlatGen; range; hTensor; module hTensor-impl)
open import Categories.APROP.Hypergraph.Model.Translation sig using (⟪_⟫; ⟪⟫-domL; ⟪⟫-codL)

open import Categories.APROP.Hypergraph.Soundness.Strict.Decode.Decode sig _≟X_
open import Categories.APROP.Hypergraph.Soundness.Strict.Perm.PermSupport sig _≟X_

open import Data.Fin using (Fin; _↑ˡ_)
open import Data.List using (List; _++_; map)
open import Data.List.Properties using (map-++)
open import Data.Product using (proj₁; proj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym)

module _
  (permˢ-K : ∀ (V : Set) (_≟V_ : DecidableEquality V) (vlab : V → X) → Support.PermK V vlab)
  where

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
      ≈-trans (cast-resp (⟪⟫-domL (f ⊗₁ g)) (⟪⟫-codL (f ⊗₁ g)) reconcileˢ)
      (≈-trans (≡⇒≈ˢ (cast-fuse (sym (⟪⟫-domL (f ⊗₁ g))) (⟪⟫-domL (f ⊗₁ g))
                                (sym (⟪⟫-codL (f ⊗₁ g))) (⟪⟫-codL (f ⊗₁ g))
                                (decodePˢ f ⊗ˢ decodePˢ g)))
        (≡⇒≈ˢ (cast-irrel _ refl _ refl (decodePˢ f ⊗ˢ decodePˢ g))))

  ------------------------------------------------------------------------
  -- The G-block factoring, the genuinely-strict provable piece (the G-side
  -- core).  Over the C-run on `C.dom = map injL G.dom ++ map injR K.dom`, the
  -- G-edge block `gblk` touches only the `injL` prefix; the untouched
  -- `map injR K.dom` is a SUFFIX, so the proven RIGHT-frame `term-sepˢ`
  -- factors the G-block run as `(G-run) ⊗ˢ idˢ {map injR K.dom}`.  This is
  -- exactly the G-side of the reconciliation `reconcileˢ` consumes.

  module GBlock {A B C D : ObjTerm}
    (f : HomTerm A B) (g : HomTerm C D)
    where
    private
      G = ⟪ f ⟫
      K = ⟪ g ⟫
      module Gd = Hypergraph G
      module Kd = Hypergraph K
      open hTensor-impl G K using (injL)
      open StrictDecoder (hTensor G K)

      gblk = map (_↑ˡ Kd.nE) (range Gd.nE)

    -- the G-block run over the tensor stack, with the K-input as the
    -- untouched right frame `R = map injR K.dom` — `term-sepˢ` applies
    -- whenever the gblk inputs are disjoint from `R` (`block-disjoint`),
    -- which holds because gblk inputs are `injL`-vertices and `R` is all
    -- `injR`-vertices.  The disjointness witness is the strict mirror of the
    -- non-strict `gblock-disjoint`.
    G-block-frameˢ
      : ∀ (R : List (Fin (Hypergraph.nV (hTensor G K))))
        → block-disjoint gblk R
        → (Q : map vl (proj₁ (process-edgesˢ gblk (map injL Gd.dom ++ R)))
               ≡ map vl (proj₁ (process-edgesˢ gblk (map injL Gd.dom))) ++ map vl R)
        → castˢ (map-++ vl (map injL Gd.dom) R) Q
            (proj₂ (process-edgesˢ gblk (map injL Gd.dom ++ R)))
          ≈ˢ proj₂ (process-edgesˢ gblk (map injL Gd.dom)) ⊗ˢ idˢ {map vl R}
    G-block-frameˢ R dis Q = term-sepˢ gblk (map injL Gd.dom) R dis Q

--------------------------------------------------------------------------------
-- `decodePˢ-⊗` is reduced to the single boundary residual `reconcileˢ`,
-- discharged in `Strict/Tensor/TensorReconcile.agda`: it re-sorts the braided
-- K-block outputs (see CRITICAL ASYMMETRY above) back behind `G.cod` via the
-- `σˢ`/`σ-hexˢʳ` block-braid and the final `perm-rigidˢ`.  Substrate here:
-- `process-edgesˢ-++` (run split over `gblk ++ kblk`) and `G-block-frameˢ`
-- (the G-side, from the proven right-frame `term-sepˢ`).
--------------------------------------------------------------------------------
