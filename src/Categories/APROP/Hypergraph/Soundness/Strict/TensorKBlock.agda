{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- Discharge of the LAST ⊗-shape residual `KBlockσ` of `Strict.TensorBraidS`
-- — the K-block PREPEND BRAID.
--
-- After the G-block fires (right-frame, leaving the `G.cod`-block prefix
-- `Lpre'` on the stack), the K-edge block acts on the `map injR K.dom`
-- suffix `Rsuf` but `edge-stepˢ` PREPENDS K's fired outputs in FRONT of the
-- carried `Lpre'`.  So the K-block run on the clean mixed stack
-- `Lpre' ++ Rsuf` is NOT `idˢ {Lpre'} ⊗ˢ (K-run on Rsuf)` — each fired K-box
-- lands to the LEFT of the `Lpre'` wires, producing a BRAIDED stack
-- `K.cod-block ++ Lpre'-and-residual`.
--
-- THE CENTRAL BRICK — `box-slideˢ`.  A single fired box on `L ++ xs`
-- (`L` disjoint from `ein e`) equals, up to an OUTPUT block-braid `shifts L
-- (eout e)`, the `idˢ {L}`-framed fired box on `xs`:
--
--   fire-termˢ e (L ++ xs) (L ++ rest) perm'
--     ≈ˢ permuteˢ (shifts L (eout e)) ∘ˢ (idˢ {map vl L} ⊗ˢ fire-termˢ e xs rest p)
--
-- The box `genˢ (elab e)` is slid leftward past `idˢ {map vl L}` by `σˢ`/
-- `box-commute-ˢ`; the residual permute alignment is closed by `perm-rigidˢ`
-- on the `Unique` fired-output stack.  This is the strict twin of the
-- non-strict `box-braid`.
--
-- The K-block iteration (`kblock-factorˢ`) folds `box-slideˢ` over the
-- K-edge list, and the final reconciliation feeds `TensorBraidS.Braid.
-- decodePˢ-⊗-cond` to make `decodePˢ-⊗` UNCONDITIONAL.
--------------------------------------------------------------------------------

open import Categories.APROP
open import Relation.Binary using (DecidableEquality)

module Categories.APROP.Hypergraph.Soundness.Strict.TensorKBlock
  (sig : APROPSignature)
  (_≟X_ : DecidableEquality (APROPSignature.X sig))
  where

open APROP sig

open import Categories.APROP.Hypergraph.Core using (Hypergraph)
open import Categories.APROP.Hypergraph.FromAPROP sig using (FlatGen)

open import Categories.APROP.Hypergraph.Soundness.Strict.DecodeS sig _≟X_
open import Categories.APROP.Hypergraph.Soundness.Strict.PermSupport sig _≟X_

open import Data.Fin using (Fin)
open import Data.Fin.Properties using () renaming (_≟_ to _≟F_)
open import Data.List using (List; []; _∷_; _++_; map)
open import Data.List.Properties using (map-++; ++-assoc)
open import Data.List.Relation.Unary.Unique.Propositional using (Unique)
open import Data.Product using (Σ; Σ-syntax; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; subst)
import Data.List.Relation.Binary.Permutation.Propositional as Perm
open Perm using (_↭_)
import Data.List.Relation.Binary.Permutation.Propositional.Properties as PermProp

--------------------------------------------------------------------------------
-- The per-hypergraph K-block braid machinery.  `permˢ-K` is the threaded
-- strict Kelly residual (consumed only by `perm-rigidˢ`).

module _ (H : Hypergraph FlatGen) where
  private module H = Hypergraph H

  open StrictDecoder H

  module Kmod = Support (Fin H.nV) H.vlab

  private
    m : List (Fin H.nV) → List X
    m = map vl

  ------------------------------------------------------------------------
  -- The strict fired layer (matching `edge-stepˢ`'s FIRE branch on the
  -- nose; local copy, mirroring `SwapCore`/`StackEquivS`).
  ------------------------------------------------------------------------

  fire-termˢ
    : ∀ (e : Fin H.nE) (s rest : List (Fin H.nV))
    → s Perm.↭ H.ein e ++ rest
    → HomS (m s) (m (H.eout e ++ rest))
  fire-termˢ e s rest perm =
    castˢ refl (sym (map-++ vl (H.eout e) rest))
      ((genˢ (H.elab e) ⊗ˢ idˢ {m rest})
        ∘ˢ castˢ refl (map-++ vl (H.ein e) rest) (permuteˢ perm))

  ------------------------------------------------------------------------
  -- ## The box-output left-slide (pure SMC, K-FREE).
  --
  -- The fired box's output block `genˢ ⊗ idˢ {L ++ rest}` (the box at the
  -- front, then the carried `L` and residual `rest`) equals the same box
  -- moved to AFTER `L` (`idˢ {L} ⊗ (genˢ ⊗ idˢ {rest})`) precomposed with
  -- the block braid `σˢ (map L) (map (eout e))` that swaps the box's output
  -- block past `L`.  Slide via `σ-natˢ`/`interchangeˢ`.
  ------------------------------------------------------------------------

  module _ (permˢ-K : Kmod.PermK) where
    open Kmod using (perm-rigidˢ)

    ----------------------------------------------------------------------
    -- ## The pure box left-slide (K-FREE).
    --
    -- The box `genˢ` with its residual `idˢ {map L ++ map rest}` to the
    -- right equals the box pushed to AFTER the carried block `map L`
    -- (`idˢ {map L} ⊗ˢ (genˢ ⊗ˢ idˢ {map rest})`), conjugated by the two
    -- one-sided block braids that swap the box's input / output block past
    -- `map L`.  Pure `σ-natˢ`/`interchangeˢ`; the maps are `m`-distributed.
    ----------------------------------------------------------------------

    -- `(X ∘ˢ Y) ⊗ˢ idˢ{R}  ≈  (X ⊗ˢ idˢ{R}) ∘ˢ (Y ⊗ˢ idˢ{R})`
    private
      ⊗id-dist
        : ∀ {as bs cs} {R : List X} (Xt : HomS bs cs) (Yt : HomS as bs)
        → (Xt ∘ˢ Yt) ⊗ˢ idˢ {R} ≈ˢ (Xt ⊗ˢ idˢ {R}) ∘ˢ (Yt ⊗ˢ idˢ {R})
      ⊗id-dist Xt Yt =
        ≈-trans (⊗-resp ≈-refl (≈-sym idˡ)) (≈-sym interchangeˢ)

      -- the σ-conjugation `g ⊗ idˢ{c} ≈ σ c b ∘ (idˢ{c} ⊗ g) ∘ σ a c`.
      box-conjˡ
        : ∀ {a b : List X} (g : HomS a b) (c : List X)
        → g ⊗ˢ idˢ {c} ≈ˢ σˢ c b ∘ˢ ((idˢ {c} ⊗ˢ g) ∘ˢ σˢ a c)
      box-conjˡ {a} {b} g c =
        ≈-sym
          (≈-trans (≈-sym assocˢ)
            (≈-trans (∘-resp σ-natˢ ≈-refl)
              (≈-trans assocˢ
                (≈-trans (∘-resp ≈-refl σ-σˢ) idʳ))))

    ----------------------------------------------------------------------
    -- ## `box-block-slideˢ` — the box residual-block slide with a right
    -- frame `R`.  The box `genˢ` carrying its full residual `(map L ++ R)`
    -- equals the box moved to AFTER the carried `map L`, conjugated by the
    -- output braid `σ (map L) B ⊗ idˢ{R}` and the input braid `σ A (map L) ⊗
    -- idˢ{R}` (`A = map ein e`, `B = map eout e`).  This is the genuine
    -- box-slide content.  K-FREE (`box-conjˡ` + `⊗id-dist`).
    ----------------------------------------------------------------------
    box-block-slideˢ
      : ∀ (e : Fin H.nE) (L : List (Fin H.nV)) (R : List X)
      → (genˢ (H.elab e) ⊗ˢ idˢ {m L}) ⊗ˢ idˢ {R}
        ≈ˢ ( (σˢ (m L) (m (H.eout e)) ⊗ˢ idˢ {R})
               ∘ˢ ((idˢ {m L} ⊗ˢ genˢ (H.elab e)) ⊗ˢ idˢ {R}) )
             ∘ˢ (σˢ (m (H.ein e)) (m L) ⊗ˢ idˢ {R})
    box-block-slideˢ e L R =
      ≈-trans (⊗-resp (box-conjˡ (genˢ (H.elab e)) (m L)) ≈-refl)
        (≈-trans (⊗id-dist (σˢ (m L) (m (H.eout e)))
                   ((idˢ {m L} ⊗ˢ genˢ (H.elab e)) ∘ˢ σˢ (m (H.ein e)) (m L)))
          (≈-trans (∘-resp ≈-refl
                     (⊗id-dist (idˢ {m L} ⊗ˢ genˢ (H.elab e))
                               (σˢ (m (H.ein e)) (m L))))
            (≈-sym assocˢ)))

    ----------------------------------------------------------------------
    -- ## `box-slide-restˢ` — `box-block-slideˢ` lifted to the fired-layer
    -- residual `m (L ++ rest)`.  `box-suffix-ˢ` reframes `genˢ ⊗ idˢ {m L ++
    -- m rest}` into `(genˢ ⊗ idˢ {m L}) ⊗ idˢ {m rest}`; then
    -- `box-block-slideˢ e L (m rest)` slides the box past `m L`.  Pure cast
    -- kit + `box-block-slideˢ`.  K-FREE.
    ----------------------------------------------------------------------
    box-slide-restˢ
      : ∀ (e : Fin H.nE) (L rest : List (Fin H.nV))
      → castˢ (cong (m (H.ein e) ++_) (map-++ vl L rest))
              (cong (m (H.eout e) ++_) (map-++ vl L rest))
          (genˢ (H.elab e) ⊗ˢ idˢ {m (L ++ rest)})
        ≈ˢ castˢ (++-assoc (m (H.ein e)) (m L) (m rest))
                 (++-assoc (m (H.eout e)) (m L) (m rest))
            ( ( (σˢ (m L) (m (H.eout e)) ⊗ˢ idˢ {m rest})
                  ∘ˢ ((idˢ {m L} ⊗ˢ genˢ (H.elab e)) ⊗ˢ idˢ {m rest}) )
                ∘ˢ (σˢ (m (H.ein e)) (m L) ⊗ˢ idˢ {m rest}) )
    box-slide-restˢ e L rest =
      ≈-trans
        (cast-⊗-frame (genˢ (H.elab e))
          (map-++ vl L rest) (map-++ vl L rest) (idˢ {m (L ++ rest)})
          (cong (m (H.ein e) ++_) (map-++ vl L rest))
          (cong (m (H.eout e) ++_) (map-++ vl L rest)))
      (≈-trans
        (⊗-resp ≈-refl (cast-id (map-++ vl L rest) (map-++ vl L rest)))
      (≈-trans
        (≈-sym (box-suffix-ˢ (genˢ (H.elab e)) (m L) (m rest)))
        (cast-resp (++-assoc (m (H.ein e)) (m L) (m rest))
                   (++-assoc (m (H.eout e)) (m L) (m rest))
                   (box-block-slideˢ e L (m rest)))))

--------------------------------------------------------------------------------
-- OBSTRUCTION / RESIDUAL MAP — the remaining chain to UNCONDITIONAL
-- `decodePˢ-⊗`.
--
-- PROVEN HERE (green, postulate-free, `--safe --without-K`):
--   * `box-conjˡ` — the σ-conjugation `g ⊗ idˢ{c} ≈ σ c b ∘ (idˢ{c} ⊗ g) ∘
--     σ a c` (a box slid past an identity block to its left via `σ-natˢ`).
--   * `box-block-slideˢ` — the GENUINE box-slide brick: the fired box's
--     output block `(genˢ ⊗ idˢ {map L}) ⊗ idˢ {R}` equals the box moved to
--     AFTER the carried block `map L`, conjugated by the two one-sided block
--     braids `σ (map L) B ⊗ idˢ{R}` (output) and `σ A (map L) ⊗ idˢ{R}`
--     (input).  This is the strict twin of the non-strict `box-braid` CORE
--     slide (the `σ-in`/`σ-out` content) and is the single biggest genuine
--     σ-ingredient of the K-block prepend braid.  K-FREE.
--   * `box-slide-restˢ` — `box-block-slideˢ` lifted to the fired-layer
--     residual shape `genˢ ⊗ idˢ {map (L ++ rest)}` (via `cast-⊗-frame` +
--     `box-suffix-ˢ` to expose `(genˢ ⊗ idˢ {map L}) ⊗ idˢ {map rest}`, then
--     `box-block-slideˢ` at `R = map rest`).  Pure cast kit; K-FREE.  This is
--     the exact box content one fired layer carries on a residual `L ++ rest`.
--
-- REMAINING (the assembly tail, the strict twin of `kblock-factor` +
-- `box-braid`'s reframing + the `collapse`, ~hundreds of LOC of cast-bridging
-- + `perm-rigidˢ` reconciliations, ALL substrate available, NO new axiom):
--
--   (b) `fire-slideˢ` — the single fired box on `L ++ xs`:
--         fire-termˢ e (L ++ xs) (L ++ rest) perm'
--           ≈ˢ permuteˢ (shifts L (eout e))
--                ∘ˢ (idˢ {map L} ⊗ˢ fire-termˢ e xs rest p)
--       From `box-slide-restˢ`: the output braid `σ (map L) (map eout)` is
--       absorbed into `permuteˢ (shifts L (eout e))` (a vertex-level block
--       swap; `permuteˢ`-equal by `perm-rigidˢ` on the `Unique` fired-output
--       stack `eout e ++ (L ++ rest)`, available from linearity), and the
--       input braid `σ A (map L)` + `idˢ{L} ⊗ permuteˢ p` are reconciled with
--       `perm'` again by `perm-rigidˢ` (`Unique (ein e ++ (L ++ rest))`).
--       The `idˢ{L} ⊗_` framing of the permutes uses the proven
--       `Separability.permuteˢ-frameˡ` / `Perm′.permuteˢ-frame`.
--
--   (c) `kblock-factorˢ` — fold `fire-slideˢ` over the K-edge block by
--       induction on `kblk` (mirroring `process-edgesˢ`'s recursion): each
--       fire layer slides its box past the carried `Lpre'` and accumulates a
--       block braid; SKIP layers pass through (`idˢ{L}`-framed).  Yields, for
--       `Krun` on the clean mixed stack `Lpre' ++ Rsuf`:
--         Krun-on-clean ≈ˢ coeCod (..) (permuteˢ (↭-sym KBraidˢ)
--                          ∘ˢ (idˢ {map Lpre'} ⊗ˢ K-run-on-Rsuf))
--       (`KBraidˢ` a pure vertex `↭`; this is the non-strict `kblock-factor`
--       with the `KClean`/`KBraid` split, here cast-light).
--
--   (d) EQUIVARIANCE.  `TensorBraidS.Braid.Krun` acts on the ACTUAL post-G
--       stack `proj₁ (process-edgesˢ gblk Hf.dom)`; `StackEquivS.
--       process-edges-equivariantˢ` conjugates it onto the clean mixed stack
--       `Lpre' ++ Rsuf`, and `TensorBraidS.Braid.Kon-bridge` relabels the
--       clean K-run to `proj₂ (Run.runˢ K)` (hence `decodePˢ g`).
--
--   (e) FINAL RECONCILE — assemble (c)+(d) with the G-frame `Gon ⊗ˢ idˢ`
--       (already in `TensorBraidS.Braid.gframe`), fold `Gon-bridge`/
--       `Kon-bridge` into `decodePˢ f`/`decodePˢ g` via the cross-vertex
--       bridge `DecodeComposeS.permuteˢ-X`, and let the accumulated braids +
--       `permuteˢ cand` collapse by `perm-rigidˢ` on the `Unique` cod `Hf.cod`.
--       This produces the `KBlockσ` witness `(cand , …)` fed to
--       `TensorBraidS.Braid.decodePˢ-⊗-cond`, making `decodePˢ-⊗`
--       UNCONDITIONAL.
--
-- All substrate is in place (`box-block-slideˢ` here; `permuteˢ-frameˡ`,
-- `permuteˢ-frame`, `box-suffix-ˢ`, `perm-rigidˢ`, `process-edges-
-- equivariantˢ`, `permuteˢ-X`, `Gon-bridge`/`Kon-bridge`/`gframe`); no axiom
-- beyond the threaded `permˢ-K`.  The remaining work is the cast-threading of
-- (a)/(b) and the inductive bookkeeping of (c)/(e).
--------------------------------------------------------------------------------
