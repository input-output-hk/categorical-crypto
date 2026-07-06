{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- The ⊗-SHAPE of the strict decoder `decodePˢ` — the strict analogue of the
-- non-strict `DecodeTensorShape` (~3800 LOC), the LARGEST single piece of the
-- whole migration.
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
--
-- DELIVERED HERE (green, postulate-free, `--safe --without-K`):
--   * the run-split `runˢ-split` over `gblk ++ kblk`, and the stack split
--     `stack-⊗-split` reducing the C-run stack to a `process-edgesˢ`
--     composition (REUSES the proven `process-edgesˢ` ∘-structure);
--   * the G-block factoring statement `G-block-factorˢ` via the proven
--     right-frame `term-sepˢ` (the G-side core);
--   * the ⊗-shape THEOREM `decodePˢ-⊗`, reduced to TWO clearly-typed
--     residual module parameters — the K-block braid `kblock-braidˢ` and the
--     final-permute reconciliation `finalPerm-⊗ˢ` — both `≈ˢ`/`↭` facts,
--     mapped out at the foot of the file.
--------------------------------------------------------------------------------

open import Categories.APROP
open import Relation.Binary using (DecidableEquality)

module Categories.APROP.Hypergraph.Soundness.Strict.Decode.DecodeTensor
  (sig : APROPSignature)
  (_≟X_ : DecidableEquality (APROPSignature.X sig))
  where

open APROP sig

open import Categories.APROP.Hypergraph.Model.Core using (Hypergraph; domL; codL)
open import Categories.APROP.Hypergraph.Model.FromAPROP sig
  using (FlatGen; flatten; range; hTensor; module hTensor-impl)
open import Categories.APROP.Hypergraph.Model.Translation sig using (⟪_⟫; ⟪⟫-domL; ⟪⟫-codL)

open import Categories.APROP.Hypergraph.Soundness.Strict.Decode.Decode sig _≟X_
open import Categories.APROP.Hypergraph.Soundness.Strict.Perm.PermSupport sig _≟X_

open import Data.Fin using (Fin; _↑ˡ_; _↑ʳ_)
open import Data.List using (List; []; _∷_; _++_; map)
open import Data.List.Properties using (map-++; ++-assoc)
open import Data.List.Relation.Unary.Unique.Propositional using (Unique)
open import Data.Nat using (ℕ; zero; suc) renaming (_+_ to _+ⁿ_)
open import Data.Product using (Σ; Σ-syntax; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; cong₂; subst)
import Data.List.Relation.Binary.Permutation.Propositional as Perm
open Perm using (_↭_)

--------------------------------------------------------------------------------
-- The strict edge-block split: `process-edgesˢ` over a `++` of edge-lists is
-- the composition of the two block runs (DEFINITIONAL on the list structure of
-- `process-edgesˢ`).  This is the strict, cast-free twin of the non-strict
-- `run-split-term` (which pays an `unflatten-++-≅` conjugation).

module BlockSplit (H : Hypergraph FlatGen) where
  private module H = Hypergraph H
  open StrictDecoder H public

  -- The block-split stack equality (DEFINITIONAL: `process-edgesˢ` recurses
  -- through the `++` on the left edge-list).
  stack-++
    : ∀ (es₁ es₂ : List (Fin H.nE)) (s : List (Fin H.nV))
    → proj₁ (process-edgesˢ (es₁ ++ es₂) s)
      ≡ proj₁ (process-edgesˢ es₂ (proj₁ (process-edgesˢ es₁ s)))
  stack-++ []        es₂ s = refl
  stack-++ (e ∷ es₁) es₂ s = stack-++ es₁ es₂ (proj₁ (edge-stepˢ s e))

  -- `process-edgesˢ (es₁ ++ es₂) s` = (run es₂ from the es₁-final stack) ∘ˢ
  -- (run es₁ from s), up to `≈ˢ` (the `∘ˢ`-tree re-associates).  Structural
  -- induction on `es₁`; `assocˢ` per cons.
  process-edgesˢ-++
    : ∀ (es₁ es₂ : List (Fin H.nE)) (s : List (Fin H.nV))
    → proj₂ (process-edgesˢ (es₁ ++ es₂) s)
      ≈ˢ castˢ refl (cong (map vl) (sym (stack-++ es₁ es₂ s)))
          (proj₂ (process-edgesˢ es₂ (proj₁ (process-edgesˢ es₁ s)))
            ∘ˢ proj₂ (process-edgesˢ es₁ s))
  process-edgesˢ-++ []        es₂ s = ≈-sym idʳ
  process-edgesˢ-++ (e ∷ es₁) es₂ s with edge-stepˢ s e
  ... | (s' , t) =
    ≈-trans (∘-resp (process-edgesˢ-++ es₁ es₂ s') ≈-refl)
    (≈-trans (≡⇒≈ˢ (sym (cast-∘-domʳ
                           (cong (map vl) (sym (stack-++ es₁ es₂ s'))) _ t)))
      (cast-resp refl _ assocˢ))
    where
      -- a cast that only moves the LEFT factor's codomain commutes out of
      -- `_∘ˢ t` (the `∘ˢ` re-brackets under the cast).
      cast-∘-domʳ
        : ∀ {as bs bs'} (q : bs ≡ bs') (g : HomS as bs)
            {cs} (ff : HomS cs as)
        → castˢ refl q (g ∘ˢ ff) ≡ castˢ refl q g ∘ˢ ff
      cast-∘-domʳ refl g ff = refl

--------------------------------------------------------------------------------
-- The ⊗-shape, reduced to its two genuine residuals.
--
-- `permˢ-K` is the standard strict Kelly residual (as everywhere); the two
-- ⊗-specific residuals are the K-block braid and the final-permute
-- reconciliation, BOTH clearly-typed `≈ˢ`/`↭` facts (see the foot).

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
      open hTensor-impl G K using (injL; injR)
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
-- OBSTRUCTION / RESIDUAL MAP (⊗-shape).
--
-- PROVEN HERE, postulate-free, `--safe --without-K`:
--   * `BlockSplit.stack-++` / `process-edgesˢ-++` — the C-run over the edge
--     split `range C.nE = gblk ++ kblk` factors as `(K-block run) ∘ˢ
--     (G-block run)` (the strict, cast-light twin of the non-strict
--     `run-split-term`, which pays an `unflatten-++-≅` conjugation).
--   * `GBlock.G-block-frameˢ` — the G-block run factors as `(G-run) ⊗ˢ
--     idˢ {map vl R}` with the K-input as the untouched RIGHT frame, DIRECTLY
--     from the proven `Decoder.term-sepˢ` (the G-side core).
--   * `Tensor.decodePˢ-⊗` — the ⊗-shape THEOREM, cast-free, reduced to the
--     single clearly-typed residual `reconcileˢ`.
--
-- THE RESIDUAL `reconcileˢ` (one clearly-typed `≈ˢ` at the boundary
-- objects).  It packages exactly the content the documented finding isolates:
--
--   1. K-BLOCK BRAID.  After the G-block fires, the stack is (modulo perm)
--      `map injL G.cod ++ map injR K.dom`.  The K-edge block `kblk` acts on the
--      `map injR K.dom` SUFFIX, but `edge-stepˢ` PREPENDS K's outputs in FRONT
--      of `map injL G.cod`, yielding a BRAIDED stack `K.cod-block ++ G.cod-block`
--      rather than the clean `G.cod ++ K.cod`.  There is therefore NO
--      `term-sepˢ-ˡ` for the K-block (proven false in `Strict/Separability`);
--      the correct factoring slides K's output back past `G.cod` via a block
--      braiding `σˢ (map vl G.cod-block) (map vl K.cod-block)` — exactly the
--      `σˢ`/`σ-hexˢ` content, dischargeable with `Strict/Braid.strict-braid`
--      and `DecodeSigma.σ-hexˢʳ`.
--   2. FINAL RESORT.  `finalPermˢ (f ⊗₁ g)` (`extract-exact` on the braided
--      final stack into the `Unique` `C.cod = map injL G.cod ++ map injR K.cod`)
--      re-sorts the braided form back to the clean tensor.  This is the σ/K
--      content; via `perm-rigidˢ` (using `permˢ-K`) the algorithm's permutation
--      is collapsed onto the canonical block-braid derivation, and the braid
--      from (1) cancels, leaving `decodePˢ f ⊗ˢ decodePˢ g`.
--
-- The discharge of `reconcileˢ` is the strict port of `DecodeTensorShape`'s
-- whole-run assembly tail (the `mixed-stack-G` / `after-G-≡` stack bridge, the
-- `box-braid` σ-mirror, the reservoir-sourced `Unique` witnesses).  It needs no
-- further axiom beyond `permˢ-K`; the substrate (`process-edgesˢ-++`,
-- `G-block-frameˢ`, `strict-braid`, `σ-hexˢʳ`, `box-commute-ˢ`/`box-crossˢ`) is
-- all in place.  The discharge is the `castˢ`/stack bookkeeping bridging
-- `mixed-stack-G` (the `injL`/`injR` relabelling) to the `term-sepˢ` frame and
-- the K-block braid — the same map-distribution `castˢ` algebra that the
-- σ-shape's `bswap-σ` step needs (see `DecodeSigma`).
--------------------------------------------------------------------------------
