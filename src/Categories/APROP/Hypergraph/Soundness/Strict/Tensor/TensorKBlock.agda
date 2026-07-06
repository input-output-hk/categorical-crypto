{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- The K-block braid residual `KBlockσ` and its supporting lemmas, organised as
-- submodules TKB/TKB2/.../TKB6 (each carrying its own clash-free imports) plus
-- the top-level `KBlockDisjoint`.  `TensorKBlockFinal` stays separate to avoid
-- the `TensorBraid` import cycle.
--------------------------------------------------------------------------------

open import Categories.APROP
open import Relation.Binary using (DecidableEquality)

module Categories.APROP.Hypergraph.Soundness.Strict.Tensor.TensorKBlock
  (sig : APROPSignature)
  (_≟X_ : DecidableEquality (APROPSignature.X sig))
  where

open APROP sig

-- Hoisted (needed for every 'module TKBn (H : Hypergraph FlatGen)' header):
open import Categories.APROP.Hypergraph.Model.Core using (Hypergraph)
open import Categories.APROP.Hypergraph.Model.FromAPROP sig using (FlatGen)
-- Canonical Decoder alias for disambiguating 'open StrictDecoder':
import Categories.APROP.Hypergraph.Soundness.Strict.Decode.Decoder sig _≟X_ as Dec

------------------------------------------------------------------------
-- ===== submodule TKB =====
------------------------------------------------------------------------
module TKB (H : Hypergraph FlatGen) where
  open import Categories.APROP.Hypergraph.Soundness.Strict.Decode.Decode sig _≟X_
  open import Categories.APROP.Hypergraph.Soundness.Strict.Perm.PermSupport sig _≟X_
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

  private module H = Hypergraph H

  open Dec.StrictDecoder H

  module Kmod = Support (Fin H.nV) H.vlab

  private
    m : List (Fin H.nV) → List X
    m = map vl

  ------------------------------------------------------------------------
  -- The strict fired layer (matching `edge-stepˢ`'s FIRE branch on the
  -- nose; local copy, mirroring `SwapCore`/`StackEquiv`).
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
-- THE CHAIN TO UNCONDITIONAL `decodePˢ-⊗`.
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
-- THE ASSEMBLY TAIL (the strict twin of `kblock-factor` +
-- `box-braid`'s reframing + the `collapse`, cast-bridging
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
--   (d) EQUIVARIANCE.  `TensorBraid.Braid.Krun` acts on the ACTUAL post-G
--       stack `proj₁ (process-edgesˢ gblk Hf.dom)`; `StackEquiv.
--       process-edges-equivariantˢ` conjugates it onto the clean mixed stack
--       `Lpre' ++ Rsuf`, and `TensorBraid.Braid.Kon-bridge` relabels the
--       clean K-run to `proj₂ (Run.runˢ K)` (hence `decodePˢ g`).
--
--   (e) FINAL RECONCILE — assemble (c)+(d) with the G-frame `Gon ⊗ˢ idˢ`
--       (already in `TensorBraid.Braid.gframe`), fold `Gon-bridge`/
--       `Kon-bridge` into `decodePˢ f`/`decodePˢ g` via the cross-vertex
--       bridge `DecodeCompose.permuteˢ-X`, and let the accumulated braids +
--       `permuteˢ cand` collapse by `perm-rigidˢ` on the `Unique` cod `Hf.cod`.
--       This produces the `KBlockσ` witness `(cand , …)` fed to
--       `TensorBraid.Braid.decodePˢ-⊗-cond`, making `decodePˢ-⊗`
--       UNCONDITIONAL.
--
-- The substrate this chain consumes is provided across this tree
-- (`box-block-slideˢ` here; `permuteˢ-frameˡ`, `permuteˢ-frame`,
-- `box-suffix-ˢ`, `perm-rigidˢ`, `process-edges-equivariantˢ`, `permuteˢ-X`,
-- `Gon-bridge`/`Kon-bridge`/`gframe`); no axiom beyond the threaded `permˢ-K`.
-- The chain is the cast-threading of (a)/(b) and the inductive bookkeeping of
-- (c)/(e).
--------------------------------------------------------------------------------

------------------------------------------------------------------------
-- ===== submodule TKB2 =====
------------------------------------------------------------------------
module TKB2 (H : Hypergraph FlatGen) where
  open import Categories.APROP.Hypergraph.Soundness.Strict.Decode.Decode sig _≟X_
  open import Categories.APROP.Hypergraph.Soundness.Strict.Perm.PermSupport sig _≟X_
  open import Categories.APROP.Hypergraph.Soundness.Strict.Separability sig _≟X_
    using (module StrictSep)
  open import Categories.APROP.Hypergraph.Soundness.Strict.Decode.DecodeSigma sig _≟X_
    using (module Scr)
  open import Categories.APROP.Hypergraph.Soundness.Strict.Interchange.BlockSwapComm sig _≟X_
    using (block-swap-comm)
  open import Data.Fin using (Fin)
  open import Data.List using (List; []; _∷_; _++_; map)
  open import Data.List.Properties using (map-++; ++-assoc)
  open import Data.List.Relation.Unary.Unique.Propositional using (Unique)
  open import Data.Product using (Σ; Σ-syntax; _,_; proj₁; proj₂)
  open import Relation.Binary.PropositionalEquality
    using (_≡_; refl; sym; trans; cong; subst)
  import Data.List.Relation.Binary.Permutation.Propositional as Perm
  open Perm using (_↭_)
  import Data.List.Relation.Binary.Permutation.Propositional.Properties as PermProp

  private module H = Hypergraph H

  open Dec.StrictDecoder H
  open StrictSep H using (permuteˢ-frameˡ)

  module Kmod = Support (Fin H.nV) H.vlab

  private
    m : List (Fin H.nV) → List X
    m = map vl

  ------------------------------------------------------------------------
  -- The strict fired layer (matching `edge-stepˢ`'s FIRE branch on the
  -- nose; local copy, identical to `TensorKBlock.fire-termˢ`).
  ------------------------------------------------------------------------

  fire-termˢ
    : ∀ (e : Fin H.nE) (s rest : List (Fin H.nV))
    → s Perm.↭ H.ein e ++ rest
    → HomS (m s) (m (H.eout e ++ rest))
  fire-termˢ e s rest perm =
    castˢ refl (sym (map-++ vl (H.eout e) rest))
      ((genˢ (H.elab e) ⊗ˢ idˢ {m rest})
        ∘ˢ castˢ refl (map-++ vl (H.ein e) rest) (permuteˢ perm))

  module _ (permˢ-K : Kmod.PermK) where
    open Kmod using (perm-rigidˢ)

    private
      module ScrH = Scr (Fin H.nV) H.vlab

    -- the canonical output block-braid: swap `L` past `eout e`, framed by
    -- `rest` on the right.  `(L ++ eout e) ++ rest ↭ (eout e ++ L) ++ rest`.
    obraid : ∀ (e : Fin H.nE) (L rest : List (Fin H.nV))
           → ((L ++ H.eout e) ++ rest) Perm.↭ ((H.eout e ++ L) ++ rest)
    obraid e L rest = PermProp.++⁺ʳ rest (ScrH.bswap L (H.eout e))

    -- the canonical input block-braid: swap `ein e` past `L`, framed by
    -- `rest`.  `(ein e ++ L) ++ rest ↭ (L ++ ein e) ++ rest`.
    ibraid : ∀ (e : Fin H.nE) (L rest : List (Fin H.nV))
           → ((H.ein e ++ L) ++ rest) Perm.↭ ((L ++ H.ein e) ++ rest)
    ibraid e L rest = PermProp.++⁺ʳ rest (ScrH.bswap (H.ein e) L)

    ----------------------------------------------------------------------
    -- ## (b) `fire-slideˢ`.
    --
    -- A single fired box on `L ++ xs` slides past the carried block `L`.
    -- The output block-braid is the canonical `permuteˢ (obraid e L rest)`;
    -- the input side reconciles `obraid`'s mate against the layer permute by
    -- `perm-rigidˢ` on the `Unique` input stack `ein e ++ (L ++ rest)`.
    --
    -- (Decomposed: the box itself is `box-slide-restˢ′`; the two σ-blocks are
    -- bridged to `permuteˢ`s via `block-swap-comm` + `permuteˢ-frame`; the
    -- final permute reconciliation uses `perm-rigidˢ`.)
    ----------------------------------------------------------------------

    -- ### A generic "block-σ ⊗ idˢ{rest} = permuteˢ braid" bridge.
    --   `σˢ (m P)(m Q) ⊗ˢ idˢ{m rest}`
    --     ≈ castˢ … permuteˢ (++⁺ʳ rest (bswap P Q))`,
    -- the two casts being the map-distribution of the framed endpoints.
    blockσ-perm
      : ∀ (P Q rest : List (Fin H.nV))
      → permuteˢ (PermProp.++⁺ʳ rest (ScrH.bswap P Q))
        ≈ˢ castˢ (trans (cong (_++ m rest) (sym (map-++ vl P Q)))
                        (sym (map-++ vl (P ++ Q) rest)))
                 (trans (cong (_++ m rest) (sym (map-++ vl Q P)))
                        (sym (map-++ vl (Q ++ P) rest)))
            (σˢ (m P) (m Q) ⊗ˢ idˢ {m rest})
    blockσ-perm P Q rest =
      ≈-trans
        (cast-flip (map-++ vl (P ++ Q) rest) (map-++ vl (Q ++ P) rest)
          (permuteˢ-frame rest (ScrH.bswap P Q)))
      (≈-trans
        (cast-resp (sym (map-++ vl (P ++ Q) rest)) (sym (map-++ vl (Q ++ P) rest))
          (⊗-resp (block-swap-comm (Fin H.nV) H.vlab P Q) ≈-refl))
      (≈-trans
        (cast-resp (sym (map-++ vl (P ++ Q) rest)) (sym (map-++ vl (Q ++ P) rest))
          (≡⇒≈ˢ (cast-⊗ˡ (sym (map-++ vl P Q)) (sym (map-++ vl Q P))
                   (σˢ (m P) (m Q)))))
        (≈-trans
          (≡⇒≈ˢ (cast-fuse
                  (cong (_++ m rest) (sym (map-++ vl P Q)))
                  (sym (map-++ vl (P ++ Q) rest))
                  (cong (_++ m rest) (sym (map-++ vl Q P)))
                  (sym (map-++ vl (Q ++ P) rest))
                  (σˢ (m P) (m Q) ⊗ˢ idˢ {m rest})))
          (≡⇒≈ˢ (cast-irrel _ _ _ _ (σˢ (m P) (m Q) ⊗ˢ idˢ {m rest}))))))

    ----------------------------------------------------------------------
    -- ## (b) `fire-slideˢ`.
    --
    --   fire-termˢ e (L ++ xs) (L ++ rest) perm'
    --     ≈ˢ castₒ (permuteˢ (obraid e L rest))
    --         ∘ˢ (idˢ {m L} ⊗ˢ fire-termˢ e xs rest p)
    --
    -- where `castₒ` reframes the canonical output braid's endpoints onto the
    -- composite's.  Requires `Unique (ein e ++ L ++ rest)` (the layer's input
    -- multiset), supplied by linearity at the use site.
    ----------------------------------------------------------------------

    private
      gen' : ∀ (e : Fin H.nE) → HomS (m (H.ein e)) (m (H.eout e))
      gen' e = genˢ (H.elab e)

    -- The OUTPUT-braid reframing cast (assoc + map-distribution).
    odom : ∀ (e : Fin H.nE) (L rest : List (Fin H.nV))
         → m ((L ++ H.eout e) ++ rest) ≡ m L ++ m (H.eout e ++ rest)
    odom e L rest =
      trans (map-++ vl (L ++ H.eout e) rest)
        (trans (cong (_++ m rest) (map-++ vl L (H.eout e)))
          (trans (++-assoc (m L) (m (H.eout e)) (m rest))
            (cong (m L ++_) (sym (map-++ vl (H.eout e) rest)))))

    ocod : ∀ (e : Fin H.nE) (L rest : List (Fin H.nV))
         → m ((H.eout e ++ L) ++ rest) ≡ m (H.eout e ++ (L ++ rest))
    ocod e L rest =
      trans (map-++ vl (H.eout e ++ L) rest)
        (trans (cong (_++ m rest) (map-++ vl (H.eout e) L))
          (trans (++-assoc (m (H.eout e)) (m L) (m rest))
            (trans (cong (m (H.eout e) ++_) (sym (map-++ vl L rest)))
              (sym (map-++ vl (H.eout e) (L ++ rest))))))

    -- The MID box block `(idˢ{m L} ⊗ˢ genˢ) ⊗ˢ idˢ{m rest}` reassociates to
    -- `idˢ{m L} ⊗ˢ (genˢ ⊗ˢ idˢ{m rest})` (the box inside `idˢ{L} ⊗ fire`).
    mid-assoc
      : ∀ (e : Fin H.nE) (L rest : List (Fin H.nV))
      → castˢ (++-assoc (m L) (m (H.ein e)) (m rest))
              (++-assoc (m L) (m (H.eout e)) (m rest))
          ((idˢ {m L} ⊗ˢ gen' e) ⊗ˢ idˢ {m rest})
        ≈ˢ idˢ {m L} ⊗ˢ (gen' e ⊗ˢ idˢ {m rest})
    mid-assoc e L rest = ⊗-assocˢ (idˢ {m L}) (gen' e) (idˢ {m rest})

    -- The INPUT σ-block bridged to the canonical braid `ibraid`.
    --   σˢ (m ein)(m L) ⊗ˢ idˢ{m rest} ≈ castˢ … permuteˢ (ibraid e L rest)
    in-σ-perm
      : ∀ (e : Fin H.nE) (L rest : List (Fin H.nV))
      → (σˢ (m (H.ein e)) (m L) ⊗ˢ idˢ {m rest})
        ≈ˢ castˢ (sym (trans (cong (_++ m rest) (sym (map-++ vl (H.ein e) L)))
                             (sym (map-++ vl (H.ein e ++ L) rest))))
                 (sym (trans (cong (_++ m rest) (sym (map-++ vl L (H.ein e))))
                             (sym (map-++ vl (L ++ H.ein e) rest))))
            (permuteˢ (ibraid e L rest))
    in-σ-perm e L rest =
      cast-flip _ _ (≈-sym (blockσ-perm (H.ein e) L rest))

    ----------------------------------------------------------------------
    -- ## The INPUT permute reconciliation (the single `perm-rigidˢ` use).
    --
    -- The input braid `permuteˢ (ibraid e L rest)` composed with the layer
    -- permute `permuteˢ perm'` (re-bracketed onto the braid's domain) equals
    -- the `idˢ{m L}`-framed inner permute `idˢ{m L} ⊗ˢ permuteˢ p`, modulo a
    -- single re-bracketing cast.  Closed by `perm-rigidˢ` on the `Unique`
    -- multiset `(L ++ ein e) ++ rest`.
    ----------------------------------------------------------------------

    -- re-bracket `ein ++ (L ++ rest)` ⇝ `(ein ++ L) ++ rest`.
    brkIn : ∀ (e : Fin H.nE) (L rest : List (Fin H.nV))
          → H.ein e ++ (L ++ rest) ≡ (H.ein e ++ L) ++ rest
    brkIn e L rest = sym (++-assoc (H.ein e) L rest)

    -- re-bracket `L ++ (ein ++ rest)` ⇝ `(L ++ ein) ++ rest`.
    brkL : ∀ (e : Fin H.nE) (L rest : List (Fin H.nV))
         → L ++ (H.ein e ++ rest) ≡ (L ++ H.ein e) ++ rest
    brkL e L rest = sym (++-assoc L (H.ein e) rest)

    in-reconcile
      : ∀ (e : Fin H.nE) (L xs rest : List (Fin H.nV))
          (perm' : (L ++ xs) Perm.↭ H.ein e ++ (L ++ rest))
          (p : xs Perm.↭ H.ein e ++ rest)
      → Unique ((L ++ H.ein e) ++ rest)
      → permuteˢ (ibraid e L rest)
          ∘ˢ castˢ refl (cong m (brkIn e L rest)) (permuteˢ perm')
        ≈ˢ castˢ (sym (map-++ vl L xs))
                 (trans (sym (map-++ vl L (H.ein e ++ rest))) (cong m (brkL e L rest)))
            (idˢ {m L} ⊗ˢ permuteˢ p)
    in-reconcile e L xs rest perm' p uIn =
      ≈-trans (∘-resp ≈-refl lhs-perm)
      (≈-trans (≈-refl
                  {f = permuteˢ (Perm.trans
                         (subst (λ z → (L ++ xs) Perm.↭ z) (brkIn e L rest) perm')
                         (ibraid e L rest))})
      (≈-trans (perm-rigidˢ permˢ-K uIn
                  (Perm.trans (subst (λ z → (L ++ xs) Perm.↭ z) (brkIn e L rest) perm')
                              (ibraid e L rest))
                  (subst (λ z → (L ++ xs) Perm.↭ z) (brkL e L rest) (PermProp.++⁺ˡ L p)))
        rhs-perm))
      where
        lhs-perm
          : castˢ refl (cong m (brkIn e L rest)) (permuteˢ perm')
            ≈ˢ permuteˢ (subst (λ z → (L ++ xs) Perm.↭ z) (brkIn e L rest) perm')
        lhs-perm = ≡⇒≈ˢ (sym (permuteˢ-subst (brkIn e L rest) perm'))

        rhs-perm
          : permuteˢ (subst (λ z → (L ++ xs) Perm.↭ z) (brkL e L rest) (PermProp.++⁺ˡ L p))
            ≈ˢ castˢ (sym (map-++ vl L xs))
                     (trans (sym (map-++ vl L (H.ein e ++ rest))) (cong m (brkL e L rest)))
                (idˢ {m L} ⊗ˢ permuteˢ p)
        rhs-perm =
          ≈-trans (≡⇒≈ˢ (permuteˢ-subst (brkL e L rest) (PermProp.++⁺ˡ L p)))
          (≈-trans (cast-resp refl (cong m (brkL e L rest))
                      (cast-flip (map-++ vl L xs) (map-++ vl L (H.ein e ++ rest))
                         (permuteˢ-frameˡ L p)))
            (≈-trans (≡⇒≈ˢ (cast-fuse (sym (map-++ vl L xs)) refl
                     (sym (map-++ vl L (H.ein e ++ rest))) (cong m (brkL e L rest))
                     (idˢ {m L} ⊗ˢ permuteˢ p)))
              (≡⇒≈ˢ (cast-irrel _ (sym (map-++ vl L xs)) _ _
                       (idˢ {m L} ⊗ˢ permuteˢ p)))))

    ----------------------------------------------------------------------
    -- ## The `idˢ{L}`-framed composite split.
    --   idˢ{m L} ⊗ˢ (g ∘ˢ f) ≈ (idˢ{m L} ⊗ˢ g) ∘ˢ (idˢ{m L} ⊗ˢ f)
    ----------------------------------------------------------------------
    private
      id⊗-dist
        : ∀ {as bs cs} (L : List X) (g : HomS bs cs) (f : HomS as bs)
        → idˢ {L} ⊗ˢ (g ∘ˢ f) ≈ˢ (idˢ {L} ⊗ˢ g) ∘ˢ (idˢ {L} ⊗ˢ f)
      id⊗-dist L g f =
        ≈-trans (⊗-resp (≈-sym idˡ) ≈-refl) (≈-sym interchangeˢ)

    ----------------------------------------------------------------------
    -- ## The framed inner fire layer `FF = idˢ{m L} ⊗ˢ fire-termˢ e xs rest p`
    -- reduced to NF `castˢ (MID-frame ∘ (idˢ{L}⊗permuteˢ p))`.
    ----------------------------------------------------------------------

    -- FF reduced to `castˢ Pf Qf ((idˢ{L}⊗BOXx) ∘ (idˢ{L}⊗PERMx))`.
    framed-fire-split
      : ∀ (e : Fin H.nE) (L xs rest : List (Fin H.nV))
          (p : xs Perm.↭ H.ein e ++ rest)
      → idˢ {m L} ⊗ˢ fire-termˢ e xs rest p
        ≈ˢ castˢ refl (cong (m L ++_) (sym (map-++ vl (H.eout e) rest)))
            ( (idˢ {m L} ⊗ˢ (gen' e ⊗ˢ idˢ {m rest}))
              ∘ˢ (idˢ {m L} ⊗ˢ castˢ refl (map-++ vl (H.ein e) rest) (permuteˢ p)) )
    framed-fire-split e L xs rest p =
      ≈-trans
        (≈-sym
          (cast-⊗-frame (idˢ {m L}) refl (sym (map-++ vl (H.eout e) rest))
            ((gen' e ⊗ˢ idˢ {m rest})
              ∘ˢ castˢ refl (map-++ vl (H.ein e) rest) (permuteˢ p))
            (cong (m L ++_) refl) (cong (m L ++_) (sym (map-++ vl (H.eout e) rest)))))
      (≈-trans
        (≡⇒≈ˢ (cast-irrel (cong (m L ++_) refl) refl
                 (cong (m L ++_) (sym (map-++ vl (H.eout e) rest)))
                 (cong (m L ++_) (sym (map-++ vl (H.eout e) rest)))
                 (idˢ {m L} ⊗ˢ ((gen' e ⊗ˢ idˢ {m rest})
                   ∘ˢ castˢ refl (map-++ vl (H.ein e) rest) (permuteˢ p)))))
        (cast-resp refl (cong (m L ++_) (sym (map-++ vl (H.eout e) rest)))
          (id⊗-dist (m L) (gen' e ⊗ˢ idˢ {m rest})
            (castˢ refl (map-++ vl (H.ein e) rest) (permuteˢ p)))))

    ----------------------------------------------------------------------
    -- ## (b) `fire-slideˢ` — the single fired box slides past `L`.
    --
    --   fire-termˢ e (L ++ xs) (L ++ rest) perm'
    --     ≈ˢ castˢ (odom e L rest) (ocod e L rest) (permuteˢ (obraid e L rest))
    --         ∘ˢ (idˢ {m L} ⊗ˢ fire-termˢ e xs rest p)
    --
    -- Requires `Unique ((L ++ ein e) ++ rest)`.  The OUTPUT braid is the
    -- canonical block braid `obraid`; the input σ + layer permute collapse
    -- into the framed inner permute by `in-reconcile`.
    ----------------------------------------------------------------------

    -- The OUTPUT braid `castₒ (permuteˢ obraid)` reduced to the σ-block `OUT`.
    --   castˢ (odom)(ocod)(permuteˢ (obraid e L rest))
    --     ≈ castˢ ?? (σˢ (m L)(m eout) ⊗ˢ idˢ{m rest})
    out-braid-σ
      : ∀ (e : Fin H.nE) (L rest : List (Fin H.nV))
      → castˢ (odom e L rest) (ocod e L rest) (permuteˢ (obraid e L rest))
        ≈ˢ castˢ (trans (trans (cong (_++ m rest) (sym (map-++ vl L (H.eout e))))
                               (sym (map-++ vl (L ++ H.eout e) rest)))
                        (odom e L rest))
                 (trans (trans (cong (_++ m rest) (sym (map-++ vl (H.eout e) L)))
                               (sym (map-++ vl (H.eout e ++ L) rest)))
                        (ocod e L rest))
            (σˢ (m L) (m (H.eout e)) ⊗ˢ idˢ {m rest})
    out-braid-σ e L rest =
      ≈-trans (cast-resp (odom e L rest) (ocod e L rest)
                 (blockσ-perm L (H.eout e) rest))
        (≡⇒≈ˢ (cast-fuse _ (odom e L rest) _ (ocod e L rest)
                 (σˢ (m L) (m (H.eout e)) ⊗ˢ idˢ {m rest})))


--------------------------------------------------------------------------------
-- THE CHAIN TO `KBlockσ`.
--
-- PROVEN HERE (green, postulate-free, `--safe --without-K`):
--   * `blockσ-perm` — the framed block braid `σˢ (m P)(m Q) ⊗ˢ idˢ{m rest}` as
--     a `permuteˢ` of the canonical right-framed `bswap` derivation
--     `++⁺ʳ rest (bswap P Q)`.  This bridges every σ-block in the slid box to
--     a pure vertex `↭` (the form `kblock-factorˢ` accumulates).  Built from
--     the proven `block-swap-comm` (`BlockSwapComm`) + `Perm′.permuteˢ-frame`.
--   * `in-σ-perm` — the INPUT σ-block as `permuteˢ (ibraid e L rest)`.
--   * `in-reconcile` — the SINGLE `perm-rigidˢ` use: the input braid composed
--     with the (re-bracketed) layer permute equals the `idˢ{m L}`-framed inner
--     permute, on the `Unique` multiset `(L ++ ein e) ++ rest`.  This is the
--     genuine reconciliation content of the K-prepend braid for one layer.
--   * `mid-assoc` — the MID box block reassociates to `idˢ{m L}⊗(genˢ⊗idˢ)`.
--   * `framed-fire-split` / `id⊗-dist` — the framed inner fire layer
--     `idˢ{m L} ⊗ˢ fire-termˢ e xs rest p` split into box ∘ permute.
--   * `odom`/`ocod`/`obraid`/`ibraid` — the canonical output/input block braids
--     and their map-distribution reframing casts.
--   (`box-slide-restˢ′` is the inherited TensorKBlock box-slide brick.)
--
-- THE ASSEMBLY TAIL (NO new math, ALL substrate present):
--
--   (b) `fire-slideˢ` — the single fired box on `L ++ xs` (statement above,
--       well-typed).  The cast/assoc GLUE joins the proven sub-bricks:
--       rewrite the box via `box-slide-restˢ′`, reassociate
--       `(OUT ∘ MID) ∘ INσ` and feed `INσ ∘ PERML` to `in-reconcile`, `MID` to
--       `mid-assoc`, `OUT` to `blockσ-perm L (eout e) rest`, then reassemble
--       against the RHS via `framed-fire-split`.  This is the same
--       map-distribution cast kit as `Decoder.layer-sepˢ`'s both-sides-to-NF.
--
--   (c) `kblock-factorˢ` — fold `fire-slideˢ` over `kblk` by induction
--       (mirroring `process-edgesˢ`'s recursion), accumulating a pure
--       vertex-`↭` block braid (each layer's `obraid`, telescoped through ∘ˢ).
--       SKIP layers pass through `idˢ{L}`-framed.
--
--   (d) EQUIVARIANCE — conjugate `TensorBraid.Braid.Krun` (on the actual
--       post-G stack) onto the clean mixed stack via the proven
--       `StackEquiv.process-edges-equivariantˢ`; relabel via `Kon-bridge`.
--
--   (e) FINAL RECONCILE — assemble with `gframe`/`Gon-bridge`, route block runs
--       into `decodePˢ f`/`decodePˢ g` via `DecodeCompose.permuteˢ-X`, and
--       collapse the accumulated braids + `permuteˢ cand` by `perm-rigidˢ` on
--       the `Unique` cod `Hf.cod`, producing the `KBlockσ` witness fed to
--       `TensorBraid.Braid.decodePˢ-⊗-cond` → UNCONDITIONAL `decodePˢ-⊗`.
--------------------------------------------------------------------------------


------------------------------------------------------------------------
-- ===== submodule TKB4 =====
------------------------------------------------------------------------
module TKB4 (H : Hypergraph FlatGen) where
  open import Categories.APROP.Hypergraph.Soundness.Decode.Decode sig
    using (edge-step; process-edges)
  open import Categories.APROP.Hypergraph.Soundness.Strict.Decode.Decode sig _≟X_
  open import Categories.APROP.Hypergraph.Soundness.Strict.Perm.PermSupport sig _≟X_
  open import Categories.APROP.Hypergraph.Soundness.Strict.Interchange.StackEquiv sig _≟X_
    using (module EquivStep)
  import Categories.APROP.Hypergraph.Soundness.Strict.Decode.DecodeCompose sig _≟X_ as DC
  import Categories.APROP.Hypergraph.Soundness.Discharge.Sub.StackUniqueReach sig as SUR
  open import Data.Fin using (Fin)
  open import Data.List using (List; []; _∷_; _++_; map)
  open import Data.List.Properties using (map-++; ++-assoc)
  open import Data.List.Relation.Unary.Unique.Propositional using (Unique)
  open import Data.List.Relation.Unary.All using (All; []; _∷_)
  open import Data.Product using (Σ; Σ-syntax; _,_; _×_; proj₁; proj₂)
  open import Relation.Binary.PropositionalEquality
    using (_≡_; refl; sym; trans; cong; subst)
  import Data.List.Relation.Binary.Permutation.Propositional as Perm
  open Perm using (_↭_)
  import Data.List.Relation.Binary.Permutation.Propositional.Properties as PermProp

  private module H = Hypergraph H

  open Dec.StrictDecoder H
  open Run H using (edge-stack-agree)
  open EquivStep H using (pvv-transˢ; pvv-inverse-leftˢ)
  open DC.RunBlocks H using (coeCod)

  module Kmod = Support (Fin H.nV) H.vlab

  private
    m : List (Fin H.nV) → List X
    m = map vl

  module _ (permˢ-K : Kmod.PermK) where
    perm-rigidˢ = Kmod.perm-rigidˢ permˢ-K

    ----------------------------------------------------------------------
    -- ## The clean K-block frame.
    --
    -- `KCleanˢ es L s_R` is the clean target `idˢ {m L} ⊗ˢ <clean K-run on
    -- s_R>`, framed by the `map-++` casts (the strict twin of the non-strict
    -- `KClean`, where `BTC.uf++` is replaced by the trivial `map-++` cast — no
    -- `unflatten-++-≅` cone is needed in the strict world).
    --
    -- The clean K-run is `proj₂ (process-edgesˢ es s_R)` — the SAME `kblk`-run
    -- restricted to the pure-`s_R` stack.  Here `L` is the carried prefix and
    -- `s_R` the K-side stack; the actual mixed stack `↭`s `L ++ s_R`.

    KCleanˢ
      : ∀ (es : List (Fin H.nE)) (L s_R : List (Fin H.nV))
      → HomS (m (L ++ s_R))
             (m (L ++ proj₁ (process-edgesˢ es s_R)))
    KCleanˢ es L s_R =
      castˢ (sym (map-++ vl L s_R))
            (sym (map-++ vl L (proj₁ (process-edgesˢ es s_R))))
        (idˢ {m L} ⊗ˢ proj₂ (process-edgesˢ es s_R))

    ----------------------------------------------------------------------
    -- ## The per-edge HEAD reconciliation interface.
    --
    -- For a head C-edge `e` fired from the actual stack `s` (with the clean
    -- perm `pf : s ↭ L ++ s_R` and the advanced clean perm
    -- `pf1 : s1 ↭ L ++ s_R1`, where `s1`/`s_R1` are the post-edge actual /
    -- clean stacks), the actual head term `tH = proj₂ (edge-stepˢ s e)`
    -- reconciles to the clean single-edge block precomposed with the carried
    -- perm:
    --
    --   permuteˢ pf1 ∘ˢ tH ≈ˢ KCleanHeadˢ ∘ˢ permuteˢ pf
    --
    -- This packages the strict per-edge slide (`fire-slideˢ` — the carried-`L`
    -- prepend braid) together with the actual-→-clean routing
    -- (`process-edges-equivariantˢ` at a single edge).  It is supplied by the
    -- caller; the fold below is proven UNCONDITIONALLY against it.
    ----------------------------------------------------------------------

    HeadReconcileˢ
      : ∀ (e : Fin H.nE) (L s_R s s1 : List (Fin H.nV))
          (pf  : s  Perm.↭ L ++ s_R)
          (pf1 : s1 Perm.↭ L ++ proj₁ (edge-stepˢ s_R e))
          (KCleanHd : HomS (m (L ++ s_R))
                           (m (L ++ proj₁ (edge-stepˢ s_R e))))
          (tH : HomS (m s) (m s1))
      → Set
    HeadReconcileˢ e L s_R s s1 pf pf1 KCleanHd tH =
      permuteˢ pf1 ∘ˢ tH ≈ˢ KCleanHd ∘ˢ permuteˢ pf

    ----------------------------------------------------------------------
    -- ## `KCleanˢ` empty + cons telescoping.
    ----------------------------------------------------------------------

    -- `[]`: the clean block on `[]` edges collapses to a `map-++` round-trip
    -- cast of `idˢ {m L} ⊗ˢ idˢ` = `idˢ`.
    KCleanˢ-nil
      : ∀ (L s_R : List (Fin H.nV))
      → KCleanˢ [] L s_R ≈ˢ idˢ {m (L ++ s_R)}
    KCleanˢ-nil L s_R =
      -- KCleanˢ [] L s_R = castˢ (sym map++)(sym map++) (idˢ{L} ⊗ˢ idˢ)
      ≈-trans (cast-resp (sym (map-++ vl L s_R)) (sym (map-++ vl L s_R)) ⊗-id)
        (cast-id (sym (map-++ vl L s_R)) (sym (map-++ vl L s_R)))

    ----------------------------------------------------------------------
    -- ## The clean single-edge head block.
    --
    -- `KCleanHeadˢ e L s_R` is the clean head: `idˢ {m L} ⊗ˢ <clean head term
    -- on s_R>`, framed by `map-++` casts.  The clean head term is
    -- `proj₂ (edge-stepˢ s_R e)`.
    ----------------------------------------------------------------------

    KCleanHeadˢ
      : ∀ (e : Fin H.nE) (L s_R : List (Fin H.nV))
      → HomS (m (L ++ s_R)) (m (L ++ proj₁ (edge-stepˢ s_R e)))
    KCleanHeadˢ e L s_R =
      castˢ (sym (map-++ vl L s_R))
            (sym (map-++ vl L (proj₁ (edge-stepˢ s_R e))))
        (idˢ {m L} ⊗ˢ proj₂ (edge-stepˢ s_R e))

    ----------------------------------------------------------------------
    -- ## `KCleanˢ` cons telescoping.
    --
    -- The clean run `KCleanˢ (e ∷ es) L s_R` factors as the clean tail
    -- `KCleanˢ es L (edge-stepˢ s_R e).₁` post-composed with the clean head
    -- `KCleanHeadˢ e L s_R`.  Both reduce to the SAME `idˢ{L} ⊗ˢ (-)` framed
    -- form; the strict twin of `KClean-cons`, via `interchangeˢ` (the
    -- `idˢ{L} ∘ˢ idˢ{L} = idˢ{L}` middle insertion) + cast fusion.
    ----------------------------------------------------------------------

    private
      s_R1 : (e : Fin H.nE) (s_R : List (Fin H.nV)) → List (Fin H.nV)
      s_R1 e s_R = proj₁ (edge-stepˢ s_R e)

      -- the cons-stack of the clean run.
      s_Rfin : (e : Fin H.nE) (es : List (Fin H.nE)) (s_R : List (Fin H.nV))
             → List (Fin H.nV)
      s_Rfin e es s_R = proj₁ (process-edgesˢ es (s_R1 e s_R))

    KCleanˢ-cons
      : ∀ (e : Fin H.nE) (es : List (Fin H.nE)) (L s_R : List (Fin H.nV))
      → KCleanˢ (e ∷ es) L s_R
        ≈ˢ KCleanˢ es L (s_R1 e s_R) ∘ˢ KCleanHeadˢ e L s_R
    KCleanˢ-cons e es L s_R = goal
      where
        eh = proj₂ (edge-stepˢ s_R e)
        et = proj₂ (process-edgesˢ es (s_R1 e s_R))
        sR1 = s_R1 e s_R
        sRf = s_Rfin e es s_R

        -- the clean K-run on (e ∷ es) is `et ∘ˢ eh`.
        -- step 1: id{L} ⊗ (et ∘ eh) ≈ (id{L} ⊗ et) ∘ (id{L} ⊗ eh)  [interchange]
        ⊗-split
          : idˢ {m L} ⊗ˢ (et ∘ˢ eh)
            ≈ˢ (idˢ {m L} ⊗ˢ et) ∘ˢ (idˢ {m L} ⊗ˢ eh)
        ⊗-split =
          ≈-trans (⊗-resp (≈-sym idˡ) ≈-refl) (≈-sym interchangeˢ)

        Pi  = sym (map-++ vl L s_R)
        Po  = sym (map-++ vl L sRf)
        Pm  = sym (map-++ vl L sR1)

        goal
          : KCleanˢ (e ∷ es) L s_R
            ≈ˢ KCleanˢ es L sR1 ∘ˢ KCleanHeadˢ e L s_R
        goal =
          -- LHS = castˢ Pi Po (id{L} ⊗ (et ∘ eh))
          ≈-trans (cast-resp Pi Po ⊗-split)
          -- castˢ Pi Po ((id{L}⊗et) ∘ (id{L}⊗eh))
          (∘-cast-split Pi Pm Po (idˢ {m L} ⊗ˢ et) (idˢ {m L} ⊗ˢ eh))

    ----------------------------------------------------------------------
    -- ## The K-prepend braid round-trip cancellation.
    --
    -- `permuteˢ Br ∘ˢ permuteˢ pf ≈ˢ idˢ` when `pf : s ↭ c` and `Br : c ↭ s`
    -- compose round-trip on a `Unique s`.  The single keystone use: the
    -- composite `↭-trans pf Br : s ↭ s` is identified with `↭-refl` by
    -- `perm-rigidˢ` on the `Unique` stack.
    ----------------------------------------------------------------------

    pvv-cancelˢ
      : ∀ {s c : List (Fin H.nV)} → Unique s
      → (pf : s Perm.↭ c) (Br : c Perm.↭ s)
      → permuteˢ Br ∘ˢ permuteˢ pf ≈ˢ idˢ {m s}
    pvv-cancelˢ uniq pf Br =
      ≈-trans (≈-sym (pvv-transˢ pf Br))
        (perm-rigidˢ uniq (Perm.trans pf Br) Perm.↭-refl)

    ----------------------------------------------------------------------
    -- ## The per-edge head PROVIDER.
    --
    -- A `HeadProviderˢ L` is a uniform family supplying, for ANY running
    -- configuration `(e, s_R, s, pf)`, the advanced clean perm `pf1`, the
    -- post-edge `Unique`, and the head reconciliation `HeadReconcileˢ`.  Being
    -- closed over all configurations, it re-invokes on the advanced stacks
    -- inside the recursion with NO re-indexing.  This is the honest interface
    -- the per-edge slide (`fire-slideˢ` + equivariance) instantiates; the fold
    -- below is proven UNCONDITIONALLY against it.
    ----------------------------------------------------------------------

    HeadProviderˢ : (L : List (Fin H.nV)) → Set
    HeadProviderˢ L =
      ∀ (e : Fin H.nE) (s_R s : List (Fin H.nV))
        (pf : s Perm.↭ L ++ s_R)
      → Unique s
      → Σ[ pf1 ∈ (proj₁ (edge-stepˢ s e))
                   Perm.↭ (L ++ proj₁ (edge-stepˢ s_R e)) ]
          ( Unique (proj₁ (edge-stepˢ s e))
          × HeadReconcileˢ e L s_R s (proj₁ (edge-stepˢ s e))
              pf pf1 (KCleanHeadˢ e L s_R) (proj₂ (edge-stepˢ s e)) )

    -- The SLIM provider: as `HeadProviderˢ` but (a) WITHOUT the post-edge
    -- `Unique` component (which the reservoir-threaded fold derives for
    -- itself), and (b) GUARDED by a per-edge predicate `D e` (the
    -- disjointness `ein-disjⁱ e L`, supplied only for the edges actually
    -- fired — gblk-edge inputs are NOT disjoint from an `injL`-block, so the
    -- guard must NOT be universal).  Crucially, a `HeadProviderRˢ` can be
    -- supplied WITHOUT the FALSE per-edge `Unique`-preservation family `puq`.
    HeadProviderRˢ : (D : Fin H.nE → Set) (L : List (Fin H.nV)) → Set
    HeadProviderRˢ D L =
      ∀ (e : Fin H.nE) → D e → (s_R s : List (Fin H.nV))
        (pf : s Perm.↭ L ++ s_R)
      → Unique s
      → Σ[ pf1 ∈ (proj₁ (edge-stepˢ s e))
                   Perm.↭ (L ++ proj₁ (edge-stepˢ s_R e)) ]
          HeadReconcileˢ e L s_R s (proj₁ (edge-stepˢ s e))
            pf pf1 (KCleanHeadˢ e L s_R) (proj₂ (edge-stepˢ s e))

    ----------------------------------------------------------------------
    -- ## `kfac-genˢ` — the generalised K-side perm-tracking fold.
    --
    --   proj₂ (process-edgesˢ es s)
    --     ≈ˢ permuteˢ Br ∘ˢ (KCleanˢ es L s_R ∘ˢ permuteˢ pf)
    --
    -- with the actual stack `s` only `↭`-ing the clean form (`pf`) and the
    -- codomain `↭`-ing the clean target (`Br`).  Induction on `es`, mirroring
    -- `process-edgesˢ`:
    --
    --   * `[]`   — `idˢ`; collapse `permuteˢ Br ∘ permuteˢ pf` by `pvv-cancelˢ`
    --              and `KCleanˢ [] L s_R` by `KCleanˢ-nil`.
    --   * `e∷es` — `proj₂ (process es s1) ∘ tH`: rewrite the head by the
    --              `HeadProviderˢ`, the tail by the IH, telescope the clean
    --              blocks by `KCleanˢ-cons`.  `Br` is shared with the IH (the
    --              prepend braid threads through the cons telescoping
    --              unchanged).
    --
    -- The threaded `Unique` (the round-trip side-condition) is advanced one
    -- edge per recursion via the provider.
    ----------------------------------------------------------------------

    kfac-genˢ
      : ∀ (L : List (Fin H.nV)) (hp : HeadProviderˢ L)
          (es : List (Fin H.nE)) (s_R s : List (Fin H.nV))
          (pf : s Perm.↭ L ++ s_R)
          (Br : (L ++ proj₁ (process-edgesˢ es s_R))
                Perm.↭ proj₁ (process-edgesˢ es s))
      → Unique s
      → proj₂ (process-edgesˢ es s)
        ≈ˢ permuteˢ Br ∘ˢ (KCleanˢ es L s_R ∘ˢ permuteˢ pf)
    kfac-genˢ L hp [] s_R s pf Br uniq =
      -- proj₂ (process [] s) = idˢ.
      ≈-sym
        (≈-trans (∘-resp ≈-refl (∘-resp (KCleanˢ-nil L s_R) ≈-refl))
        (≈-trans (∘-resp ≈-refl idˡ)
          (pvv-cancelˢ uniq pf Br)))
    kfac-genˢ L hp (e ∷ es) s_R s pf Br uniq
      with hp e s_R s pf uniq
    ... | pf1 , uniq1 , head =
      -- proj₂ (process (e∷es) s) = proj₂ (process es s1) ∘ˢ tH.
      ≈-trans (∘-resp IH ≈-refl)
      -- (permuteˢ Br ∘ (KCleanˢ es L sR1 ∘ permuteˢ pf1)) ∘ tH
      (≈-trans assocˢ
        (∘-resp ≈-refl
          -- (KCleanˢ es L sR1 ∘ permuteˢ pf1) ∘ tH
          (≈-trans assocˢ
            -- KCleanˢ es L sR1 ∘ (permuteˢ pf1 ∘ tH)
            (≈-trans (∘-resp ≈-refl head)
              -- KCleanˢ es L sR1 ∘ (KCleanHeadˢ e L s_R ∘ permuteˢ pf)
              (≈-trans (≈-sym assocˢ)
                -- (KCleanˢ es L sR1 ∘ KCleanHeadˢ e L s_R) ∘ permuteˢ pf
                (∘-resp (≈-sym (KCleanˢ-cons e es L s_R)) ≈-refl))))))
      where
        s1  = proj₁ (edge-stepˢ s e)
        sR1 = proj₁ (edge-stepˢ s_R e)

        IH
          : proj₂ (process-edgesˢ es s1)
            ≈ˢ permuteˢ Br ∘ˢ (KCleanˢ es L sR1 ∘ˢ permuteˢ pf1)
        IH = kfac-genˢ L hp es sR1 s1 pf1 Br uniq1

    ----------------------------------------------------------------------
    -- ## `kfac-gen-resˢ` — the RESERVOIR-THREADED K-side perm-tracking fold.
    --
    -- Identical to `kfac-genˢ`, but the threaded per-step `Unique` is DERIVED
    -- (not assumed): instead of carrying a `Unique s` advanced by the
    -- provider's (FALSE-in-general) post-edge `Unique`, we carry the
    -- `StackUniqueReach.Reservoir≤1 H es s` freshness invariant along the
    -- run-order `es` at the running stack `s`.  Each step:
    --   * `Reservoir≤1⇒Unique` derives the round-trip `Unique s`;
    --   * the `HeadProviderˢ` is invoked with that derived `Unique s` (it still
    --     supplies `pf1` + the head reconciliation; its OWN post-edge `Unique`
    --     is discarded — the recursion does NOT consume it);
    --   * `edge-step-Reservoir≤1` advances the invariant one edge, bridged to
    --     the strict stack `proj₁ (edge-stepˢ s e)` by `edge-stack-agree`.
    -- This is the EXACT threading `process-edges-equivariantˢ` (StackEquiv)
    -- uses; the only constructive content beyond `kfac-genˢ` is the `Unique`
    -- SOURCE swap (no new braid/cast algebra).
    ----------------------------------------------------------------------

    kfac-gen-resˢ
      : ∀ {D : Fin H.nE → Set}
          (L : List (Fin H.nV)) (hp : HeadProviderRˢ D L)
          (es : List (Fin H.nE)) → All D es
      → ∀ (s_R s : List (Fin H.nV))
          (pf : s Perm.↭ L ++ s_R)
          (Br : (L ++ proj₁ (process-edgesˢ es s_R))
                Perm.↭ proj₁ (process-edgesˢ es s))
      → SUR.Reservoir≤1 H es s
      → proj₂ (process-edgesˢ es s)
        ≈ˢ permuteˢ Br ∘ˢ (KCleanˢ es L s_R ∘ˢ permuteˢ pf)
    kfac-gen-resˢ L hp [] [] s_R s pf Br res =
      ≈-sym
        (≈-trans (∘-resp ≈-refl (∘-resp (KCleanˢ-nil L s_R) ≈-refl))
        (≈-trans (∘-resp ≈-refl idˡ)
          (pvv-cancelˢ (SUR.Reservoir≤1⇒Unique H [] s res) pf Br)))
    kfac-gen-resˢ L hp (e ∷ es) (de ∷ des) s_R s pf Br res
      with hp e de s_R s pf (SUR.Reservoir≤1⇒Unique H (e ∷ es) s res)
    ... | pf1 , head =
      ≈-trans (∘-resp IH ≈-refl)
      (≈-trans assocˢ
        (∘-resp ≈-refl
          (≈-trans assocˢ
            (≈-trans (∘-resp ≈-refl head)
              (≈-trans (≈-sym assocˢ)
                (∘-resp (≈-sym (KCleanˢ-cons e es L s_R)) ≈-refl))))))
      where
        s1  = proj₁ (edge-stepˢ s e)
        sR1 = proj₁ (edge-stepˢ s_R e)

        res1 : SUR.Reservoir≤1 H es s1
        res1 = subst (SUR.Reservoir≤1 H es)
                     (sym (edge-stack-agree s e))
                     (SUR.edge-step-Reservoir≤1 H e es s res)

        IH
          : proj₂ (process-edgesˢ es s1)
            ≈ˢ permuteˢ Br ∘ˢ (KCleanˢ es L sR1 ∘ˢ permuteˢ pf1)
        IH = kfac-gen-resˢ L hp es des sR1 s1 pf1 Br res1

--------------------------------------------------------------------------------
-- THE CHAIN TO `KBlockσ`.
--
-- PROVEN HERE (green, postulate-free, `--safe --without-K`):
--   * `KCleanˢ` / `KCleanHeadˢ` — the strict clean K-block frame `idˢ {m L} ⊗ˢ
--     <clean run>`, framed by `map-++` casts.  (No `unflatten-++-≅` cone is
--     needed — the strict `⊗ˢ`/`idˢ` already give the framing on the nose; the
--     non-strict `BTC.uf++` machinery DISAPPEARS.)
--   * `KCleanˢ-nil` / `KCleanˢ-cons` — empty (`⊗-id` + `cast-id`) + cons
--     telescoping (`interchangeˢ` ⊗-split + `∘-cast-split`).
--   * `pvv-cancelˢ` — the K-prepend braid round-trip `permuteˢ Br ∘ permuteˢ pf
--     ≈ idˢ` on a `Unique` stack (the SINGLE `perm-rigidˢ`/keystone use).
--   * `kfac-genˢ` — THE GATING RECURSIVE CONSTRUCTION (part (c)).  The strict
--     K-prepend perm-tracking fold
--       proj₂ (process-edgesˢ es s)
--         ≈ˢ permuteˢ Br ∘ˢ (KCleanˢ es L s_R ∘ˢ permuteˢ pf),
--     by induction on `es` MIRRORING `process-edgesˢ`'s own recursion: `[]`
--     collapses the braid round-trip + `KCleanˢ-nil`; `e∷es` rewrites the head
--     by the `HeadProviderˢ`, the tail by the IH (same `Br`, threaded
--     unchanged), telescopes by `KCleanˢ-cons`.  UNCONDITIONAL against the
--     `HeadProviderˢ` interface.
--
-- THE `HeadProviderˢ` INTERFACE (`HeadReconcileˢ`) is an explicit, fully-typed
-- hypothesis — NOT a postulate.  It is the per-edge head reconciliation
--   permuteˢ pf1 ∘ˢ tH ≈ˢ KCleanHeadˢ e L s_R ∘ˢ permuteˢ pf.
--
-- THE ASSEMBLY TAIL TO `KBlockσ`:
--
--   (c′) DISCHARGE `HeadProviderˢ` at `L = map injL Gd.dom`, `e = ψK eK`.  This
--        is the genuine per-edge content, combining:
--          • the actual→clean ROUTING `StackEquiv.edge-step-equivariantˢ`
--            (conjugate `tH` on the actual stack `s` onto the clean stack
--            `L ++ s_R` by `pf`), and
--          • the clean SLIDE `TKB3.fire-slideˢ` (the proven per-layer brick:
--            on the clean stack `L ++ s_R` the K-edge fires with residual
--            `L ++ rest_R` — by `extract-prefix-↑ʳ-on-mixed`, the K `ein` is
--            disjoint from `L = map injL …` — so the clean fire IS
--            `fire-termˢ e (L ++ s_R) (L ++ rest_R) perm'`, exactly
--            `fire-slideˢ`'s LHS; it factors into the `idˢ{m L} ⊗ˢ
--            fire-termˢ e s_R rest_R p` framed form = `KCleanHeadˢ`, up to the
--            `obraid` output block-braid that is absorbed into `pf1`).
--        The advanced clean perm `pf1` is read off `edge-step-↑ʳ-on-perm`
--        (the term-free stack braid, reusable since the strict run walks the
--        SAME stacks via `Run.stacks-agree`).  This is cast/braid glue; NO new
--        math beyond `fire-slideˢ` + equivariance.
--
--   (d) EQUIVARIANCE — instantiate `kfac-genˢ` at the `Krun` of
--       `TensorBraid.Braid` (the actual post-G stack `proj₁ (process-edgesˢ
--       gblk Hf.dom)`), with `pf` the `gframe`/`stack-sepˢ` clean perm and
--       `Br` the accumulated K-prepend braid; relabel the clean K-run to
--       `decodePˢ g`'s run via `Kon-bridge`.
--
--   (e) FINAL RECONCILE — assemble with `gframe`/`Gon-bridge` (G-side =
--       `decodePˢ f ⊗ˢ idˢ`-ish), route the clean K-run into `decodePˢ g` via
--       `DecodeCompose.permuteˢ-X`, collapse the accumulated braid +
--       `permuteˢ cand` by `perm-rigidˢ` on `Unique Hf.cod`, producing the
--       `KBlockσ` witness fed to `TensorBraid.Braid.decodePˢ-⊗-cond` → the
--       UNCONDITIONAL `decodePˢ-⊗`.
--
-- The substrate this chain consumes — `fire-slideˢ`, `edge-step-equivariantˢ`,
-- `edge-step-↑ʳ-on-perm`, `Kon-bridge`/`Gon-bridge`/`gframe`, `permuteˢ-X`,
-- `perm-rigidˢ`, `run-split-atˢ` — is provided across this tree; the (c′)
-- per-edge head discharge and the (d)/(e) cast/stack collapse algebra assemble
-- into the `KBlockσ` witness.
--------------------------------------------------------------------------------

------------------------------------------------------------------------
-- ===== submodule TKB3 =====
------------------------------------------------------------------------
module TKB3 (H : Hypergraph FlatGen) where
  open import Categories.APROP.Hypergraph.Soundness.Strict.Decode.Decode sig _≟X_
  open import Categories.APROP.Hypergraph.Soundness.Strict.Perm.PermSupport sig _≟X_
  open import Categories.APROP.Hypergraph.Soundness.Strict.Separability sig _≟X_
    using (module StrictSep)
  open import Categories.APROP.Hypergraph.Soundness.Strict.Decode.DecodeSigma sig _≟X_
    using (module Scr)
  open import Data.Fin using (Fin)
  open import Data.List using (List; []; _∷_; _++_; map)
  open import Data.List.Properties using (map-++; ++-assoc)
  open import Data.List.Relation.Unary.Unique.Propositional using (Unique)
  open import Data.Product using (Σ; Σ-syntax; _,_; proj₁; proj₂)
  open import Relation.Binary.PropositionalEquality
    using (_≡_; refl; sym; trans; cong; subst)
  import Data.List.Relation.Binary.Permutation.Propositional as Perm
  open Perm using (_↭_)
  import Data.List.Relation.Binary.Permutation.Propositional.Properties as PermProp

  private module H = Hypergraph H

  open Dec.StrictDecoder H
  open StrictSep H using (permuteˢ-frameˡ)

  module Kmod = Support (Fin H.nV) H.vlab

  private
    m : List (Fin H.nV) → List X
    m = map vl

  fire-termˢ
    : ∀ (e : Fin H.nE) (s rest : List (Fin H.nV))
    → s Perm.↭ H.ein e ++ rest
    → HomS (m s) (m (H.eout e ++ rest))
  fire-termˢ e s rest perm =
    castˢ refl (sym (map-++ vl (H.eout e) rest))
      ((genˢ (H.elab e) ⊗ˢ idˢ {m rest})
        ∘ˢ castˢ refl (map-++ vl (H.ein e) rest) (permuteˢ perm))

  module _ (permˢ-K : Kmod.PermK) where
    open Kmod using (perm-rigidˢ)

    private
      module ScrH = Scr (Fin H.nV) H.vlab

    gen' : ∀ (e : Fin H.nE) → HomS (m (H.ein e)) (m (H.eout e))
    gen' e = genˢ (H.elab e)

    -- the canonical output block-braid (mirror of TKB2.obraid).
    obraid : ∀ (e : Fin H.nE) (L rest : List (Fin H.nV))
           → ((L ++ H.eout e) ++ rest) Perm.↭ ((H.eout e ++ L) ++ rest)
    obraid e L rest = PermProp.++⁺ʳ rest (ScrH.bswap L (H.eout e))

    odom : ∀ (e : Fin H.nE) (L rest : List (Fin H.nV))
         → m ((L ++ H.eout e) ++ rest) ≡ m L ++ m (H.eout e ++ rest)
    odom e L rest =
      trans (map-++ vl (L ++ H.eout e) rest)
        (trans (cong (_++ m rest) (map-++ vl L (H.eout e)))
          (trans (++-assoc (m L) (m (H.eout e)) (m rest))
            (cong (m L ++_) (sym (map-++ vl (H.eout e) rest)))))

    ocod : ∀ (e : Fin H.nE) (L rest : List (Fin H.nV))
         → m ((H.eout e ++ L) ++ rest) ≡ m (H.eout e ++ (L ++ rest))
    ocod e L rest =
      trans (map-++ vl (H.eout e ++ L) rest)
        (trans (cong (_++ m rest) (map-++ vl (H.eout e) L))
          (trans (++-assoc (m (H.eout e)) (m L) (m rest))
            (trans (cong (m (H.eout e) ++_) (sym (map-++ vl L rest)))
              (sym (map-++ vl (H.eout e) (L ++ rest))))))

    ------------------------------------------------------------------
    -- The canonical composite both sides reduce to.
    --   OUT  = σˢ (m L)(m eout) ⊗ˢ idˢ{m rest}
    --   MIDᵢ = idˢ{m L} ⊗ˢ (gen' ⊗ˢ idˢ{m rest})
    --   INP  = idˢ{m L} ⊗ˢ castˢ refl (map-++ vl ein rest)(permuteˢ p)
    ------------------------------------------------------------------
    private
      OUTb : ∀ (e : Fin H.nE) (L rest : List (Fin H.nV))
           → HomS ((m L ++ m (H.eout e)) ++ m rest) ((m (H.eout e) ++ m L) ++ m rest)
      OUTb e L rest = σˢ (m L) (m (H.eout e)) ⊗ˢ idˢ {m rest}

      -- the MID box in box-slide's native LEFT-assoc bracketing.
      MIDb : ∀ (e : Fin H.nE) (L rest : List (Fin H.nV))
           → HomS ((m L ++ m (H.ein e)) ++ m rest) ((m L ++ m (H.eout e)) ++ m rest)
      MIDb e L rest = (idˢ {m L} ⊗ˢ gen' e) ⊗ˢ idˢ {m rest}

      MIDib : ∀ (e : Fin H.nE) (L rest : List (Fin H.nV))
            → HomS (m L ++ m (H.ein e) ++ m rest) (m L ++ m (H.eout e) ++ m rest)
      MIDib e L rest = idˢ {m L} ⊗ˢ (gen' e ⊗ˢ idˢ {m rest})

      INPb : ∀ (e : Fin H.nE) (L xs rest : List (Fin H.nV))
             (p : xs Perm.↭ H.ein e ++ rest)
           → HomS (m L ++ m xs) (m L ++ m (H.ein e) ++ m rest)
      INPb e L xs rest p =
        idˢ {m L} ⊗ˢ castˢ refl (map-++ vl (H.ein e) rest) (permuteˢ p)

    ------------------------------------------------------------------
    -- ## RHS reduction.
    --
    -- The RHS `castˢ (odom)(ocod)(permuteˢ obraid) ∘ˢ (idˢ{m L} ⊗ fire-termˢ)`
    -- reduces — via `out-braid-σ` (first factor → cast of OUT) and
    -- `framed-fire-split` (second factor → cast of MIDᵢ ∘ INP), then a single
    -- cast-fusion through the shared middle `m L ++ m(eout++rest)` — to
    -- `castˢ refl OC (OUT ∘ˢ (MIDᵢ ∘ˢ INP))`.
    ------------------------------------------------------------------

    private
      -- the OUTPUT cast endpoints, as in `out-braid-σ`.
      OD : ∀ (e : Fin H.nE) (L rest : List (Fin H.nV))
         → (m L ++ m (H.eout e)) ++ m rest ≡ m L ++ m (H.eout e ++ rest)
      OD e L rest =
        trans (trans (cong (_++ m rest) (sym (map-++ vl L (H.eout e))))
                     (sym (map-++ vl (L ++ H.eout e) rest)))
              (odom e L rest)

      OC : ∀ (e : Fin H.nE) (L rest : List (Fin H.nV))
         → (m (H.eout e) ++ m L) ++ m rest ≡ m (H.eout e ++ (L ++ rest))
      OC e L rest =
        trans (trans (cong (_++ m rest) (sym (map-++ vl (H.eout e) L)))
                     (sym (map-++ vl (H.eout e ++ L) rest)))
              (ocod e L rest)

      -- the codomain-cast `framed-fire-split` puts on its inner composite.
      QF : ∀ (e : Fin H.nE) (L rest : List (Fin H.nV))
         → m L ++ m (H.eout e) ++ m rest ≡ m L ++ m (H.eout e ++ rest)
      QF e L rest = cong (m L ++_) (sym (map-++ vl (H.eout e) rest))

    -- the assoc cast inserted between OUT and the right-assoc MIDᵢ∘INP.
    private
      ASout : ∀ (e : Fin H.nE) (L rest : List (Fin H.nV))
            → m L ++ m (H.eout e) ++ m rest ≡ (m L ++ m (H.eout e)) ++ m rest
      ASout e L rest = sym (++-assoc (m L) (m (H.eout e)) (m rest))

    rhs-canon
      : ∀ (e : Fin H.nE) (L xs rest : List (Fin H.nV))
          (p : xs Perm.↭ H.ein e ++ rest)
      → castˢ (odom e L rest) (ocod e L rest) (permuteˢ (obraid e L rest))
          ∘ˢ (idˢ {m L} ⊗ˢ fire-termˢ e xs rest p)
        ≈ˢ castˢ refl (OC e L rest)
            (OUTb e L rest
              ∘ˢ castˢ refl (ASout e L rest)
                   (MIDib e L rest ∘ˢ INPb e L xs rest p))
    rhs-canon e L xs rest p =
      ≈-trans (∘-resp (TKB2.out-braid-σ H permˢ-K e L rest)
                      (TKB2.framed-fire-split H permˢ-K e L xs rest p))
        -- castˢ OD OC OUT ∘ castˢ refl QF (MIDᵢ ∘ INP)
        (≈-trans
          -- re-express the right cast as castˢ refl OD (castˢ refl ASout …)
          (∘-resp ≈-refl right-recast)
          -- castˢ OD OC OUT ∘ castˢ refl OD (castˢ refl ASout (MIDᵢ∘INP))
          (≈-sym (∘-cast-split refl (OD e L rest) (OC e L rest)
                    (OUTb e L rest)
                    (castˢ refl (ASout e L rest)
                       (MIDib e L rest ∘ˢ INPb e L xs rest p)))))
      where
        FF : HomS (m L ++ m xs) (m L ++ m (H.eout e) ++ m rest)
        FF = MIDib e L rest ∘ˢ INPb e L xs rest p

        fuse
          : castˢ refl (OD e L rest) (castˢ refl (ASout e L rest) FF)
            ≡ castˢ refl (trans (ASout e L rest) (OD e L rest)) FF
        fuse = cast-fuse refl refl (ASout e L rest) (OD e L rest) FF

        right-recast
          : castˢ refl (QF e L rest) FF
            ≈ˢ castˢ refl (OD e L rest) (castˢ refl (ASout e L rest) FF)
        right-recast =
          ≈-trans
            (≡⇒≈ˢ (cast-irrel refl refl (QF e L rest)
                     (trans (ASout e L rest) (OD e L rest)) FF))
            (≈-sym (≡⇒≈ˢ fuse))

    ------------------------------------------------------------------
    -- ## LHS reduction.
    ------------------------------------------------------------------

    -- the box block-slide brick, inherited from TensorKBlock.
    box-slide-restˢ′ = TKB.box-slide-restˢ H permˢ-K

    private
      INσb : ∀ (e : Fin H.nE) (L rest : List (Fin H.nV))
           → HomS ((m (H.ein e) ++ m L) ++ m rest) ((m L ++ m (H.ein e)) ++ m rest)
      INσb e L rest = σˢ (m (H.ein e)) (m L) ⊗ˢ idˢ {m rest}

      -- BOX as a back-cast of `(OUT ∘ MIDb) ∘ INσ` (box-slide-restˢ flipped,
      -- composed with the `cong (_ ++_)(map-++ L rest)` reframing flip).
      BOX : ∀ (e : Fin H.nE) (L rest : List (Fin H.nV))
          → HomS (m (H.ein e) ++ m (L ++ rest)) (m (H.eout e) ++ m (L ++ rest))
      BOX e L rest = genˢ (H.elab e) ⊗ˢ idˢ {m (L ++ rest)}

    -- box-slide-restˢ, with the box re-exposed: BOX as a two-sided cast of
    -- the slid composite `(OUT ∘ MIDb) ∘ INσ`.
    box-flip
      : ∀ (e : Fin H.nE) (L rest : List (Fin H.nV))
      → BOX e L rest
        ≈ˢ castˢ (sym (cong (m (H.ein e) ++_) (map-++ vl L rest)))
                 (sym (cong (m (H.eout e) ++_) (map-++ vl L rest)))
            (castˢ (++-assoc (m (H.ein e)) (m L) (m rest))
                   (++-assoc (m (H.eout e)) (m L) (m rest))
              ((OUTb e L rest ∘ˢ MIDb e L rest) ∘ˢ INσb e L rest))
    box-flip e L rest =
      cast-flip (cong (m (H.ein e) ++_) (map-++ vl L rest))
                (cong (m (H.eout e) ++_) (map-++ vl L rest))
        (box-slide-restˢ′ e L rest)

    private
      Pi : ∀ (e : Fin H.nE) (L rest : List (Fin H.nV))
         → m ((H.ein e ++ L) ++ rest) ≡ (m (H.ein e) ++ m L) ++ m rest
      Pi e L rest =
        sym (trans (cong (_++ m rest) (sym (map-++ vl (H.ein e) L)))
                   (sym (map-++ vl (H.ein e ++ L) rest)))

      Qi : ∀ (e : Fin H.nE) (L rest : List (Fin H.nV))
         → m ((L ++ H.ein e) ++ rest) ≡ (m L ++ m (H.ein e)) ++ m rest
      Qi e L rest =
        sym (trans (cong (_++ m rest) (sym (map-++ vl L (H.ein e))))
                   (sym (map-++ vl (L ++ H.ein e) rest)))

      -- the codomain cast `in-reconcile` produces on `idˢ{mL} ⊗ permuteˢ p`.
      Rcod : ∀ (e : Fin H.nE) (L rest : List (Fin H.nV))
           → m L ++ m (H.ein e ++ rest) ≡ m ((L ++ H.ein e) ++ rest)
      Rcod e L rest =
        trans (sym (map-++ vl L (H.ein e ++ rest)))
              (cong m (TKB2.brkL H permˢ-K e L rest))

    -- INPUT reconciliation: the σ-block braid composed with the (re-bracketed)
    -- layer permute collapses to the `idˢ{mL}`-framed inner permute.
    in-combined
      : ∀ (e : Fin H.nE) (L xs rest : List (Fin H.nV))
          (perm' : (L ++ xs) Perm.↭ H.ein e ++ (L ++ rest))
          (p : xs Perm.↭ H.ein e ++ rest)
      → Unique ((L ++ H.ein e) ++ rest)
      → INσb e L rest
          ∘ˢ castˢ refl (Pi e L rest)
                   (castˢ refl (cong m (TKB2.brkIn H permˢ-K e L rest)) (permuteˢ perm'))
        ≈ˢ castˢ (sym (map-++ vl L xs))
                 (trans (Rcod e L rest) (Qi e L rest))
            (idˢ {m L} ⊗ˢ permuteˢ p)
    in-combined e L xs rest perm' p uIn =
      ≈-trans (∘-resp (TKB2.in-σ-perm H permˢ-K e L rest) ≈-refl)
        -- castˢ Pi Qi (permuteˢ ibraid) ∘ castˢ refl Pi castP_brk
        (≈-trans
          (≈-sym (∘-cast-split refl (Pi e L rest) (Qi e L rest)
                    (permuteˢ (TKB2.ibraid H permˢ-K e L rest))
                    (castˢ refl (cong m (TKB2.brkIn H permˢ-K e L rest)) (permuteˢ perm'))))
          -- castˢ refl Qi (permuteˢ ibraid ∘ castP_brk)
          (≈-trans
            (cast-resp refl (Qi e L rest)
              (TKB2.in-reconcile H permˢ-K e L xs rest perm' p uIn))
            -- castˢ refl Qi (castˢ (sym map-++Lxs) Rcod (idˢ⊗permuteˢ p))
            (≡⇒≈ˢ
              (trans
                (cast-fuse (sym (map-++ vl L xs)) refl (Rcod e L rest) (Qi e L rest)
                   (idˢ {m L} ⊗ˢ permuteˢ p))
                (cast-irrel (trans (sym (map-++ vl L xs)) refl) (sym (map-++ vl L xs))
                   (trans (Rcod e L rest) (Qi e L rest))
                   (trans (Rcod e L rest) (Qi e L rest))
                   (idˢ {m L} ⊗ˢ permuteˢ p))))))

    ------------------------------------------------------------------
    -- ## MIDb → MIDib and INPb-core → INPb conversions.
    ------------------------------------------------------------------

    -- `idˢ{mL} ⊗ permuteˢ p` re-cast into `INPb` (the inner `castˢ` moved out
    -- of the ⊗ by `cast-⊗-frame`).
    inp-core→INPb
      : ∀ (e : Fin H.nE) (L xs rest : List (Fin H.nV))
          (p : xs Perm.↭ H.ein e ++ rest)
      → idˢ {m L} ⊗ˢ permuteˢ p
        ≈ˢ castˢ refl (sym (cong (m L ++_) (map-++ vl (H.ein e) rest)))
            (INPb e L xs rest p)
    inp-core→INPb e L xs rest p =
      cast-flip refl (cong (m L ++_) (map-++ vl (H.ein e) rest))
        (cast-⊗-frame (idˢ {m L}) refl (map-++ vl (H.ein e) rest) (permuteˢ p)
          refl (cong (m L ++_) (map-++ vl (H.ein e) rest)))

    -- `MIDb` re-cast into `MIDib` (the `⊗-assocˢ` of `mid-assoc`, flipped).
    midb→midib
      : ∀ (e : Fin H.nE) (L rest : List (Fin H.nV))
      → MIDb e L rest
        ≈ˢ castˢ (sym (++-assoc (m L) (m (H.ein e)) (m rest)))
                 (sym (++-assoc (m L) (m (H.eout e)) (m rest)))
            (MIDib e L rest)
    midb→midib e L rest =
      cast-flip (++-assoc (m L) (m (H.ein e)) (m rest))
                (++-assoc (m L) (m (H.eout e)) (m rest))
        (TKB2.mid-assoc H permˢ-K e L rest)

    ------------------------------------------------------------------
    -- ## MID + IN reconciliation: the carried-block box composed with the
    -- input σ-block and layer permute collapses to the canonical
    -- `castˢ refl ASout (MIDib ∘ INPb)` (the RHS-canon inner-inner term).
    ------------------------------------------------------------------
    private
      INin : ∀ (e : Fin H.nE) (L xs rest : List (Fin H.nV))
               (perm' : (L ++ xs) Perm.↭ H.ein e ++ (L ++ rest))
           → HomS (m (L ++ xs)) ((m (H.ein e) ++ m L) ++ m rest)
      INin e L xs rest perm' =
        castˢ refl (Pi e L rest)
          (castˢ refl (cong m (TKB2.brkIn H permˢ-K e L rest)) (permuteˢ perm'))

    mid-in-canon
      : ∀ (e : Fin H.nE) (L xs rest : List (Fin H.nV))
          (perm' : (L ++ xs) Perm.↭ H.ein e ++ (L ++ rest))
          (p : xs Perm.↭ H.ein e ++ rest)
      → Unique ((L ++ H.ein e) ++ rest)
      → MIDb e L rest ∘ˢ (INσb e L rest ∘ˢ INin e L xs rest perm')
        ≈ˢ castˢ (sym (map-++ vl L xs)) (ASout e L rest)
            (MIDib e L rest ∘ˢ INPb e L xs rest p)
    mid-in-canon e L xs rest perm' p uIn =
      ≈-trans (∘-resp (midb→midib e L rest)
                      (≈-trans (in-combined e L xs rest perm' p uIn)
                               (cast-resp (sym (map-++ vl L xs))
                                          (trans (Rcod e L rest) (Qi e L rest))
                                          (inp-core→INPb e L xs rest p))))
      -- castˢ (sym AFin')(sym AFout') MIDib ∘ castˢ (sym map-++Lxs)(trans Rcod Qi)(castˢ refl CC INPb)
      (≈-trans
        (∘-resp ≈-refl
          (≡⇒≈ˢ (cast-fuse refl (sym (map-++ vl L xs))
                   (sym (cong (m L ++_) (map-++ vl (H.ein e) rest)))
                   (trans (Rcod e L rest) (Qi e L rest))
                   (INPb e L xs rest p))))
        -- castˢ (sym AFin')(sym AFout') MIDib ∘ castˢ (trans refl (sym map-++Lxs)) CFI INPb
        (≈-trans
          -- normalise the right factor to (sym map-++Lxs) / (sym AFin')
          (∘-resp ≈-refl
            (≡⇒≈ˢ (cast-irrel (trans refl (sym (map-++ vl L xs))) (sym (map-++ vl L xs))
                     (trans (sym (cong (m L ++_) (map-++ vl (H.ein e) rest)))
                            (trans (Rcod e L rest) (Qi e L rest)))
                     (sym (++-assoc (m L) (m (H.ein e)) (m rest)))
                     (INPb e L xs rest p))))
          (≈-trans
            (≈-sym (∘-cast-split (sym (map-++ vl L xs))
                      (sym (++-assoc (m L) (m (H.ein e)) (m rest)))
                      (sym (++-assoc (m L) (m (H.eout e)) (m rest)))
                      (MIDib e L rest) (INPb e L xs rest p)))
            -- castˢ (sym map-++Lxs)(sym AFout') (MIDib ∘ INPb)
            (≡⇒≈ˢ (cast-irrel (sym (map-++ vl L xs)) (sym (map-++ vl L xs))
                     (sym (++-assoc (m L) (m (H.eout e)) (m rest))) (ASout e L rest)
                     (MIDib e L rest ∘ˢ INPb e L xs rest p))))))

    ------------------------------------------------------------------
    -- ## (b) `fire-slideˢ` — the gating brick.
    --
    --   fire-termˢ e (L ++ xs) (L ++ rest) perm'
    --     ≈ˢ castˢ (odom e L rest) (ocod e L rest) (permuteˢ (obraid e L rest))
    --         ∘ˢ (idˢ {m L} ⊗ˢ fire-termˢ e xs rest p)
    --
    -- Requires `Unique ((L ++ ein e) ++ rest)`.  Both sides reduce to the
    -- canonical `castˢ refl OC (OUT ∘ˢ castˢ refl ASout (MIDib ∘ INPb))`:
    -- the LHS via `box-flip` + reassoc + `mid-in-canon`, the RHS via
    -- `rhs-canon`.
    ------------------------------------------------------------------
    private
      Bd : ∀ (e : Fin H.nE) (L rest : List (Fin H.nV))
         → (m (H.ein e) ++ m L) ++ m rest ≡ m (H.ein e) ++ m (L ++ rest)
      Bd e L rest =
        trans (++-assoc (m (H.ein e)) (m L) (m rest))
              (sym (cong (m (H.ein e) ++_) (map-++ vl L rest)))

      Bc : ∀ (e : Fin H.nE) (L rest : List (Fin H.nV))
         → (m (H.eout e) ++ m L) ++ m rest ≡ m (H.eout e) ++ m (L ++ rest)
      Bc e L rest =
        trans (++-assoc (m (H.eout e)) (m L) (m rest))
              (sym (cong (m (H.eout e) ++_) (map-++ vl L rest)))

    fire-slideˢ
      : ∀ (e : Fin H.nE) (L xs rest : List (Fin H.nV))
          (perm' : (L ++ xs) Perm.↭ H.ein e ++ (L ++ rest))
          (p : xs Perm.↭ H.ein e ++ rest)
      → Unique ((L ++ H.ein e) ++ rest)
      → fire-termˢ e (L ++ xs) (L ++ rest) perm'
        ≈ˢ castˢ (sym (map-++ vl L xs)) refl
            ( castˢ (odom e L rest) (ocod e L rest) (permuteˢ (obraid e L rest))
                ∘ˢ (idˢ {m L} ⊗ˢ fire-termˢ e xs rest p) )
    fire-slideˢ e L xs rest perm' p uIn =
      ≈-trans lhs-to-canon
        (≈-sym
          (≈-trans
            (cast-resp (sym (map-++ vl L xs)) refl (rhs-canon e L xs rest p))
            (≡⇒≈ˢ (trans
              (cast-fuse refl (sym (map-++ vl L xs)) (OC e L rest) refl
                (OUTb e L rest
                  ∘ˢ castˢ refl (ASout e L rest)
                       (MIDib e L rest ∘ˢ INPb e L xs rest p)))
              (cast-irrel (trans refl (sym (map-++ vl L xs))) (sym (map-++ vl L xs))
                (trans (OC e L rest) refl) (OC e L rest)
                (OUTb e L rest
                  ∘ˢ castˢ refl (ASout e L rest)
                       (MIDib e L rest ∘ˢ INPb e L xs rest p)))))))
      where
        SLID : HomS ((m (H.ein e) ++ m L) ++ m rest)
                    ((m (H.eout e) ++ m L) ++ m rest)
        SLID = (OUTb e L rest ∘ˢ MIDb e L rest) ∘ˢ INσb e L rest

        -- the input permute, fed to INσb (≡ INin by cast-irrel).
        INp : HomS (m (L ++ xs)) ((m (H.ein e) ++ m L) ++ m rest)
        INp = castˢ refl (trans (map-++ vl (H.ein e) (L ++ rest)) (sym (Bd e L rest)))
                (permuteˢ perm')

        castP : HomS (m (L ++ xs)) (m (H.ein e) ++ m (L ++ rest))
        castP = castˢ refl (map-++ vl (H.ein e) (L ++ rest)) (permuteˢ perm')

        -- rewrite castP as `castˢ refl Bd INp`.
        castP-recast : castP ≈ˢ castˢ refl (Bd e L rest) INp
        castP-recast =
          ≈-trans
            (≡⇒≈ˢ (cast-irrel refl refl (map-++ vl (H.ein e) (L ++ rest))
                     (trans (trans (map-++ vl (H.ein e) (L ++ rest)) (sym (Bd e L rest)))
                            (Bd e L rest))
                     (permuteˢ perm')))
            (≈-sym (≡⇒≈ˢ (cast-fuse refl refl
                     (trans (map-++ vl (H.ein e) (L ++ rest)) (sym (Bd e L rest)))
                     (Bd e L rest) (permuteˢ perm'))))

        -- INp ≡ INin (same endpoints, UIP).
        INp≡INin : INp ≈ˢ INin e L xs rest perm'
        INp≡INin =
          ≈-trans
            (≡⇒≈ˢ (cast-irrel refl refl
                     (trans (map-++ vl (H.ein e) (L ++ rest)) (sym (Bd e L rest)))
                     (trans (cong m (TKB2.brkIn H permˢ-K e L rest)) (Pi e L rest))
                     (permuteˢ perm')))
            (≈-sym (≡⇒≈ˢ (cast-fuse refl refl (cong m (TKB2.brkIn H permˢ-K e L rest))
                     (Pi e L rest) (permuteˢ perm'))))

        -- BOX ∘ castP reduced to castˢ refl Bc (SLID ∘ INp).
        box∘castP
          : BOX e L rest ∘ˢ castP
            ≈ˢ castˢ refl (Bc e L rest) (SLID ∘ˢ INp)
        box∘castP =
          ≈-trans (∘-resp (box-flip e L rest) castP-recast)
          -- castˢ (sym CFin)(sym CFout)(castˢ AFin AFout SLID) ∘ castˢ refl Bd INp
          (≈-trans
            (∘-resp
              (≡⇒≈ˢ (cast-fuse (++-assoc (m (H.ein e)) (m L) (m rest))
                       (sym (cong (m (H.ein e) ++_) (map-++ vl L rest)))
                       (++-assoc (m (H.eout e)) (m L) (m rest))
                       (sym (cong (m (H.eout e) ++_) (map-++ vl L rest)))
                       SLID))
              ≈-refl)
            -- castˢ Bd Bc SLID ∘ castˢ refl Bd INp
            (≈-sym (∘-cast-split refl (Bd e L rest) (Bc e L rest) SLID INp)))

        CANON : HomS (m L ++ m xs) ((m (H.eout e) ++ m L) ++ m rest)
        CANON =
          OUTb e L rest
            ∘ˢ castˢ refl (ASout e L rest)
                 (MIDib e L rest ∘ˢ INPb e L xs rest p)

        lhs-to-canon
          : fire-termˢ e (L ++ xs) (L ++ rest) perm'
            ≈ˢ castˢ (sym (map-++ vl L xs)) (OC e L rest) CANON
        lhs-to-canon =
          -- fire-termˢ = castˢ refl COUT (BOX ∘ castP)
          ≈-trans (cast-resp refl (sym (map-++ vl (H.eout e) (L ++ rest))) box∘castP)
          -- castˢ refl COUT (castˢ refl Bc (SLID ∘ INp))
          (≈-trans
            (≡⇒≈ˢ (cast-fuse refl refl (Bc e L rest)
                     (sym (map-++ vl (H.eout e) (L ++ rest)))
                     (SLID ∘ˢ INp)))
            -- castˢ refl (trans Bc COUT) (SLID ∘ INp)
            (≈-trans
              (cast-resp refl (trans (Bc e L rest) (sym (map-++ vl (H.eout e) (L ++ rest))))
                slid-canon)
              -- castˢ refl (trans Bc COUT) (castˢ (sym map-++Lxs) refl CANON)
              (≈-trans
                (≡⇒≈ˢ (cast-fuse (sym (map-++ vl L xs)) refl refl
                         (trans (Bc e L rest) (sym (map-++ vl (H.eout e) (L ++ rest))))
                         CANON))
                -- castˢ (sym map-++Lxs)(trans Bc COUT) CANON → normalise cod to OC
                (≡⇒≈ˢ (cast-irrel (trans (sym (map-++ vl L xs)) refl) (sym (map-++ vl L xs))
                         (trans refl (trans (Bc e L rest)
                           (sym (map-++ vl (H.eout e) (L ++ rest)))))
                         (OC e L rest)
                         CANON)))))
          where
            -- SLID ∘ INp ≈ castˢ (sym map-++Lxs) refl CANON
            slid-canon
              : SLID ∘ˢ INp ≈ˢ castˢ (sym (map-++ vl L xs)) refl CANON
            slid-canon =
              -- ((OUT∘MIDb)∘INσb) ∘ INp → OUT∘(MIDb∘(INσb∘INp))
              ≈-trans assocˢ
              (≈-trans assocˢ
                -- OUT ∘ (MIDb ∘ (INσb ∘ INp))
                (≈-trans
                  (∘-resp ≈-refl
                    (≈-trans (∘-resp ≈-refl (∘-resp ≈-refl INp≡INin))
                      (mid-in-canon e L xs rest perm' p uIn)))
                  -- OUT ∘ castˢ (sym map-++Lxs) ASout (MIDib ∘ INPb)
                  (≈-trans
                    (∘-resp ≈-refl
                      (≈-trans
                        (≡⇒≈ˢ (cast-irrel (sym (map-++ vl L xs))
                                 (trans (sym (map-++ vl L xs)) refl)
                                 (ASout e L rest) (trans refl (ASout e L rest))
                                 (MIDib e L rest ∘ˢ INPb e L xs rest p)))
                        (≈-sym (≡⇒≈ˢ (cast-fuse (sym (map-++ vl L xs)) refl refl
                                 (ASout e L rest)
                                 (MIDib e L rest ∘ˢ INPb e L xs rest p))))))
                    -- re-shuffle the nested casts: castˢ refl ASout (castˢ (sym…) refl X)
                    --   ≈ castˢ (sym…) refl (castˢ refl ASout X)
                    (≈-trans
                      (∘-resp ≈-refl reassoc-cast)
                      -- OUT ∘ castˢ (sym map-++Lxs) refl (castˢ refl ASout (MIDib∘INPb))
                      (≈-sym (∘-cast-split (sym (map-++ vl L xs)) refl refl
                                (OUTb e L rest)
                                (castˢ refl (ASout e L rest)
                                   (MIDib e L rest ∘ˢ INPb e L xs rest p))))))))
              where
                reassoc-cast
                  : castˢ refl (ASout e L rest)
                      (castˢ (sym (map-++ vl L xs)) refl
                         (MIDib e L rest ∘ˢ INPb e L xs rest p))
                    ≈ˢ castˢ (sym (map-++ vl L xs)) refl
                        (castˢ refl (ASout e L rest)
                           (MIDib e L rest ∘ˢ INPb e L xs rest p))
                reassoc-cast =
                  ≈-trans
                    (≡⇒≈ˢ (cast-fuse (sym (map-++ vl L xs)) refl refl (ASout e L rest)
                             (MIDib e L rest ∘ˢ INPb e L xs rest p)))
                    (≈-trans
                      (≡⇒≈ˢ (cast-irrel (trans (sym (map-++ vl L xs)) refl)
                               (trans refl (sym (map-++ vl L xs)))
                               (trans refl (ASout e L rest)) (trans (ASout e L rest) refl)
                               (MIDib e L rest ∘ˢ INPb e L xs rest p)))
                      (≈-sym (≡⇒≈ˢ (cast-fuse refl (sym (map-++ vl L xs))
                               (ASout e L rest) refl
                               (MIDib e L rest ∘ˢ INPb e L xs rest p)))))

--------------------------------------------------------------------------------
-- OBSTRUCTION / RESIDUAL MAP — the remaining chain to `KBlockσ`.
--
-- PROVEN HERE (green, postulate-free, `--safe --without-K`):
--   * `rhs-canon`  — the fire-slide RHS `castₒ(permuteˢ obraid) ∘ (idˢ{L}⊗fire)`
--     reduced to the canonical `castˢ refl OC (OUT ∘ castˢ refl ASout
--     (MIDib ∘ INPb))` via `out-braid-σ` + `framed-fire-split` + cast-fusion.
--   * `box-flip`   — the box `genˢ ⊗ idˢ{m(L++rest)}` as a back-cast of the
--     box-slide composite `(OUT ∘ MIDb) ∘ INσ` (TKB.box-slide-restˢ flipped).
--   * `in-combined`— the INPUT σ-block braid composed with the (re-bracketed)
--     layer permute collapsed to the `idˢ{mL}`-framed inner permute, via
--     `in-σ-perm` + `in-reconcile` + cast-fusion (the single `perm-rigidˢ` use).
--   * `inp-core→INPb` / `midb→midib` — the ⊗-frame / `mid-assoc` bracket
--     conversions of the inner permute and the carried-block box.
--   * `mid-in-canon`— the MID box composed with the input σ-block + layer
--     permute reduced to `castˢ (sym map-++Lxs) ASout (MIDib ∘ INPb)`.
--   * `fire-slideˢ` — THE GATING BRICK (part (b)).  A single fired box on
--     `L ++ xs` slides past the carried block `L` up to the canonical OUTPUT
--     block-braid `permuteˢ (obraid e L rest)`.  Both sides reduce to the
--     common canonical form; assembled from the bricks above.  Requires
--     `Unique ((L ++ ein e) ++ rest)`.  NOTE the well-typed statement carries a
--     `castˢ (sym (map-++ vl L xs)) refl` on the RHS composite (its domain is
--     `m L ++ m xs`, the fired layer's is `m (L ++ xs)`).
--
-- REMAINING (the assembly tail to `KBlockσ`, NO new math beyond these bricks):
--
--   (c) `kblock-factorˢ` — fold `fire-slideˢ` over the K-edge list `kblk` by
--       induction (mirroring `process-edgesˢ`'s recursion).  Each FIRE layer
--       slides its box past the carried `Lpre`-block via `fire-slideˢ` and
--       accumulates the output block-braid `obraid` (telescoped through ∘ˢ into
--       a pure vertex-`↭` `KBraidˢ`); SKIP layers pass through `idˢ{Lpre}`-
--       framed.  The induction invariant tracks the growing prepended K-output
--       block.  This is a genuinely NEW recursive construction (not cast glue).
--
--   (d) EQUIVARIANCE — conjugate `TensorBraid.Braid.Krun` (on the actual
--       post-G stack) onto the clean mixed stack via the proven
--       `StackEquiv.process-edges-equivariantˢ`; relabel via `Kon-bridge`.
--
--   (e) FINAL RECONCILE — assemble with `gframe`/`Gon-bridge`, route block runs
--       into `decodePˢ f`/`decodePˢ g` via `DecodeCompose.permuteˢ-X`, collapse
--       accumulated braids + `permuteˢ cand` by `perm-rigidˢ` on `Unique
--       Hf.cod`, producing the `KBlockσ` witness fed to
--       `TensorBraid.Braid.decodePˢ-⊗-cond` → UNCONDITIONAL `decodePˢ-⊗`.
--------------------------------------------------------------------------------

------------------------------------------------------------------------
-- ===== submodule TKB5 =====
------------------------------------------------------------------------
module TKB5 (H : Hypergraph FlatGen) where
  open import Categories.APROP.Hypergraph.Soundness.Strict.Decode.Decode sig _≟X_
  open import Categories.APROP.Hypergraph.Soundness.Strict.Perm.PermSupport sig _≟X_
  open import Categories.APROP.Hypergraph.Soundness.Strict.Interchange.StackEquiv sig _≟X_
    using (module EquivStep)
  open import Data.Fin using (Fin)
  open import Data.List using (List; []; _∷_; _++_; map)
  open import Data.List.Properties using (map-++; ++-assoc)
  open import Data.List.Relation.Unary.Unique.Propositional using (Unique)
  open import Data.Product using (Σ; Σ-syntax; _,_; _×_; proj₁; proj₂)
  open import Relation.Binary.PropositionalEquality
    using (_≡_; refl; sym; trans; cong; subst)
  import Data.List.Relation.Binary.Permutation.Propositional as Perm
  open Perm using (_↭_)
  import Data.List.Relation.Binary.Permutation.Propositional.Properties as PermProp

  private module H = Hypergraph H

  open Dec.StrictDecoder H
  open EquivStep H using ( pvv-transˢ; pvv-inverse-leftˢ; pvv-inverse-rightˢ
                         ; edge-stepˢ-graph; edge-step-equivariantˢ )

  module Kmod = Support (Fin H.nV) H.vlab

  private
    m : List (Fin H.nV) → List X
    m = map vl

  module _ (permˢ-K : Kmod.PermK) where
    KCleanHeadˢ = TKB4.KCleanHeadˢ H permˢ-K
    HeadReconcileˢ = TKB4.HeadReconcileˢ H permˢ-K
    HeadProviderˢ = TKB4.HeadProviderˢ H permˢ-K

    ----------------------------------------------------------------------
    -- ## The clean per-edge SLIDE interface.
    --
    -- For a head edge `e` whose inputs are disjoint from the carried block
    -- `L`, fired on the CLEAN stack `L ++ s_R`, there is a braid `β` from the
    -- clean post-edge stack to `L ++ (edge-stepˢ s_R e).₁` such that the clean
    -- fired head, braided by `β`, IS the framed clean head `KCleanHeadˢ`.
    --
    -- This is the genuine per-edge content (`fire-slideˢ` + the `↑ʳ`-disjoint
    -- skip/fire dispatch); the equivariance conjugation below is built on it.
    ----------------------------------------------------------------------

    HeadSlideˢ : (e : Fin H.nE) (L s_R : List (Fin H.nV)) → Set
    HeadSlideˢ e L s_R =
      Σ[ β ∈ (proj₁ (edge-stepˢ (L ++ s_R) e))
               Perm.↭ (L ++ proj₁ (edge-stepˢ s_R e)) ]
        ( permuteˢ β ∘ˢ proj₂ (edge-stepˢ (L ++ s_R) e)
          ≈ˢ KCleanHeadˢ e L s_R )

    ----------------------------------------------------------------------
    -- ## The equivariance conjugation glue.
    --
    -- Given `HeadSlideˢ` and the post-edge `Unique`, `HeadReconcileˢ` follows
    -- by conjugating the actual fired head onto the clean stack via
    -- `edge-step-equivariantˢ` and reassociating.
    ----------------------------------------------------------------------

    head-reconcile-from-slide
      : ∀ (e : Fin H.nE) (L s_R s : List (Fin H.nV))
          (pf : s Perm.↭ L ++ s_R)
      → Unique s
      → HeadSlideˢ e L s_R
      → Σ[ pf1 ∈ (proj₁ (edge-stepˢ s e))
                   Perm.↭ (L ++ proj₁ (edge-stepˢ s_R e)) ]
          HeadReconcileˢ e L s_R s (proj₁ (edge-stepˢ s e))
            pf pf1 (KCleanHeadˢ e L s_R) (proj₂ (edge-stepˢ s e))
    head-reconcile-from-slide e L s_R s pf us (β , slide)
      with edge-step-equivariantˢ e pf
             (edge-stepˢ-graph (L ++ s_R) e) (edge-stepˢ-graph s e) us
    ... | ρf , eq =
      Perm.trans ρf β , goal
      where
        tH      = proj₂ (edge-stepˢ s e)
        tHclean = proj₂ (edge-stepˢ (L ++ s_R) e)

        -- eq : tH ≈ permuteˢ (↭-sym ρf) ∘ (tHclean ∘ permuteˢ pf)
        -- goal : permuteˢ (trans ρf β) ∘ tH ≈ KCleanHeadˢ ∘ permuteˢ pf
        goal
          : permuteˢ (Perm.trans ρf β) ∘ˢ tH
            ≈ˢ KCleanHeadˢ e L s_R ∘ˢ permuteˢ pf
        goal =
          -- permuteˢ (trans ρf β) = permuteˢ β ∘ permuteˢ ρf  (definitional)
          ≈-trans (∘-resp (pvv-transˢ ρf β) ≈-refl)
          -- (permuteˢ β ∘ permuteˢ ρf) ∘ tH
          (≈-trans (∘-resp ≈-refl eq)
          -- (permuteˢ β ∘ permuteˢ ρf) ∘ (permuteˢ(↭-sym ρf) ∘ (tHclean ∘ permuteˢ pf))
          (≈-trans assocˢ
          -- permuteˢ β ∘ (permuteˢ ρf ∘ (permuteˢ(↭-sym ρf) ∘ (tHclean ∘ permuteˢ pf)))
          (≈-trans (∘-resp ≈-refl (≈-sym assocˢ))
          -- permuteˢ β ∘ ((permuteˢ ρf ∘ permuteˢ(↭-sym ρf)) ∘ (tHclean ∘ permuteˢ pf))
          (≈-trans (∘-resp ≈-refl (∘-resp (pvv-inverse-rightˢ ρf) ≈-refl))
          -- permuteˢ β ∘ (idˢ ∘ (tHclean ∘ permuteˢ pf))
          (≈-trans (∘-resp ≈-refl idˡ)
          -- permuteˢ β ∘ (tHclean ∘ permuteˢ pf)
          (≈-trans (≈-sym assocˢ)
          -- (permuteˢ β ∘ tHclean) ∘ permuteˢ pf
          (∘-resp slide ≈-refl)))))))

--------------------------------------------------------------------------------
-- OBSTRUCTION / RESIDUAL MAP — the remaining chain to `KBlockσ`.
--
-- PROVEN HERE (green, postulate-free, `--safe --without-K`):
--
--   * `HeadSlideˢ` — the per-edge CLEAN-SLIDE interface: for a head edge `e`
--     fired on the clean stack `L ++ s_R`, a braid `β` such that the clean
--     fired head braided by `β` IS the framed clean head `KCleanHeadˢ`.  This
--     is the `fire-slideˢ` + `↑ʳ`-disjoint content, ABSTRACTED so the
--     equivariance conjugation is independent of the concrete layout.
--
--   * `head-reconcile-from-slide` — THE GATE REDUCTION.  Discharges the per-edge
--     `HeadReconcileˢ` of `TKB4` from `HeadSlideˢ`, by conjugating the actual
--     fired head `tH` onto the clean stack `L ++ s_R` via
--     `StackEquiv.edge-step-equivariantˢ` (at `ρ = pf`) and reassociating.
--     The advanced clean perm is `pf1 = trans ρf β` (the equivariance braid
--     `ρf` chained with the slide braid `β`); `permuteˢ` splits over `trans`
--     DEFINITIONALLY (`pvv-transˢ`), and the round-trip `permuteˢ ρf ∘
--     permuteˢ (↭-sym ρf)` collapses by `pvv-inverse-rightˢ`.  UNCONDITIONAL
--     against `HeadSlideˢ`.
--
-- The equivariance conjugation (c′-glue) is therefore COMPLETE and generic; the
-- gate is reduced to the two uniform families.
--
-- REMAINING (the genuine concrete content + the assembly tail):
--
--   (c′-slide) DISCHARGE `HeadSlideˢ` at the `hTensor` layout: `H = ⟪f⊗₁g⟫`,
--        `L = map injL Gd.dom`, `s_R = map injR ys`, `e = ψK eK = Gd.nE ↑ʳ eK`.
--        FIRE case: `edge-stepˢ (L ++ s_R) (ψK eK)` reduces (strict twin of
--        `extract-prefix-↑ʳ-on-mixed-just`, needed) to
--          `fire-termˢ (ψK eK) (L ++ s_R) (L ++ map injR rest) q`,
--        whose residual is LITERALLY `L ++ (edge-stepˢ s_R (ψK eK)).₁` because
--        K's `ein = map injR (K.ein eK)` is disjoint from `L = map injL …`.
--        This is exactly `fire-slideˢ`'s LHS at `xs = s_R`, `rest = map injR
--        rest`; `fire-slideˢ` rewrites it to `castₒ(permuteˢ (obraid)) ∘
--        (idˢ{m L} ⊗ˢ fire-termˢ … s_R …)`, and the framed `idˢ{m L} ⊗ˢ …`
--        factor IS `KCleanHeadˢ` (definitional).  The slide braid `β` is read
--        off `obraid` (the output block-braid sliding K's eout back past `L`),
--        absorbed via the cast algebra into the `HeadSlideˢ` Σ.  SKIP case:
--        both `edge-stepˢ` reduce to `idˢ` (via the strict twin of
--        `extract-prefix-↑ʳ-on-mixed-nothing`), and `KCleanHeadˢ` collapses by
--        `⊗-id`/`cast-id`; `β = ↭-refl`.  Estimated ~250-350 LOC; the only NEW
--        substrate is the strict twin of the term-FREE `edge-step-↑ʳ-on-mixed-
--        {just,nothing}` stack reductions (the non-strict ones live in
--        `Soundness/DecodeAttempt`); they transfer because the strict and
--        non-strict runs walk the SAME stacks (`Run.stacks-agree`).  The
--        `Unique`-advance family is the strict-run reservoir freshness from
--        `Discharge/Sub/StackUniqueReach` (as in `process-edges-equivariantˢ`).
--
--   (d) INSTANTIATE `kfac-genˢ` at `TensorBraid.Braid.Krun` (the K-block run on
--        the actual post-G stack `proj₁ (process-edgesˢ gblk Hf.dom)`), with
--        `L = Lpre`, `s_R = Rsuf`, `pf` the `gframe`/`stack-sepˢ` clean perm,
--        and `Br` the accumulated K-prepend braid; relabel the clean K-run to
--        `decodePˢ g` via `Kon-bridge` + `DecodeCompose.permuteˢ-X`.
--
--   (e) RECONCILE with `gframe`/`Gon-bridge` (G-side = `decodePˢ f`), collapse
--        the accumulated `Br` braid + `permuteˢ cand` (final extract-exact
--        permute) by `perm-rigidˢ` on `Unique Hf.cod` → the `KBlockσ` witness;
--        feed to `TensorBraid.Braid.decodePˢ-⊗-cond` → the UNCONDITIONAL
--        `decodePˢ-⊗`.
--
-- STATUS: the per-edge GATE (`HeadReconcileˢ` ⇐ `HeadSlideˢ`) and its packaging
-- into `HeadProviderˢ` are PROVEN and generic; the K-block fold `kfac-genˢ`
-- (TKB4) consumes the result UNCONDITIONALLY.  `decodePˢ-⊗` is NOT YET
-- unconditional: it still rests on (c′-slide) [the concrete strict
-- `edge-step-↑ʳ-on-mixed` term reductions + `fire-slideˢ` alignment] and the
-- (d)/(e) reconcile to `KBlockσ`.  NO postulate is introduced.
--------------------------------------------------------------------------------

------------------------------------------------------------------------
-- ===== submodule TKB6 =====
------------------------------------------------------------------------
module TKB6 (H : Hypergraph FlatGen) where
  open import Categories.APROP.Hypergraph.Model.FromAPROP sig
    using (FlatGen; hTensor; module hTensor-impl)
  open import Categories.APROP.Hypergraph.Soundness.Decode.Decode sig
    using (extract-elem; extract-prefix)
  open import Categories.APROP.Hypergraph.Soundness.Strict.Decode.Decode sig _≟X_
  open import Categories.APROP.Hypergraph.Soundness.Strict.Perm.PermSupport sig _≟X_
  open import Categories.APROP.Hypergraph.Soundness.Strict.Interchange.StackEquiv sig _≟X_
    using (module EquivStep)
  open import Categories.APROP.Hypergraph.Soundness.Strict.Separability sig _≟X_
    using (module StrictSep)
  open import Categories.APROP.Hypergraph.Soundness.Strict.Decode.DecodeSigma sig _≟X_
    using (module Scr)
  import Categories.APROP.Hypergraph.Soundness.Discharge.Sub.StackUnique sig as SU
  import Categories.APROP.Hypergraph.Soundness.Discharge.Sub.StackUniqueReach sig as SUR
  open import Data.Fin using (Fin; _↑ˡ_; _↑ʳ_; splitAt)
  open import Data.Fin.Properties using (splitAt-↑ˡ; splitAt-↑ʳ)
  import Data.Fin.Properties as FinP
  open import Data.Empty using (⊥; ⊥-elim)
  open import Relation.Nullary using (yes; no)
  open import Data.List using (List; []; _∷_; _++_; map)
  open import Data.List.Properties using (map-++; ++-assoc)
  open import Data.List.Relation.Unary.Unique.Propositional using (Unique)
  open import Data.List.Relation.Unary.All using (All; []; _∷_)
  open import Data.Maybe using (Maybe; just; nothing)
  open import Data.Product using (Σ; Σ-syntax; _,_; _×_; proj₁; proj₂)
  open import Relation.Binary.PropositionalEquality
    using (_≡_; refl; sym; trans; cong; subst)
  import Data.List.Relation.Binary.Permutation.Propositional as Perm
  open Perm using (_↭_)
  import Data.List.Relation.Binary.Permutation.Propositional.Properties as PermProp

  private module H = Hypergraph H

  open Dec.StrictDecoder H
  open StrictSep H using (extract-prefix-++ˡ-left; extract-prefix-++ˡ-left-nothing)
  open EquivStep H using (pvv-transˢ; pvv-inverse-leftˢ; pvv-inverse-rightˢ)

  module Kmod = Support (Fin H.nV) H.vlab

  private
    m : List (Fin H.nV) → List X
    m = map vl

    module ScrH = Scr (Fin H.nV) H.vlab

  -- an `idˢ` cast can move its single non-trivial endpoint to the other side.
  idcast-flip
    : ∀ {a b : List X} (q : a ≡ b)
    → castˢ refl q (idˢ {a}) ≈ˢ castˢ (sym q) refl (idˢ {b})
  idcast-flip refl = ≈-refl

  module _ (permˢ-K : Kmod.PermK) where
    KCleanHeadˢ = TKB5.KCleanHeadˢ H permˢ-K
    HeadSlideˢ  = TKB5.HeadSlideˢ  H permˢ-K
    fire-slideˢ = TKB3.fire-slideˢ H permˢ-K
    obraid      = TKB3.obraid      H permˢ-K
    odom        = TKB3.odom        H permˢ-K
    ocod        = TKB3.ocod        H permˢ-K
    fire-termˢ  = TKB3.fire-termˢ  H
    HeadProviderRˢ = TKB4.HeadProviderRˢ H permˢ-K
    head-reconcile-from-slide = TKB5.head-reconcile-from-slide H permˢ-K
    KCleanˢ   = TKB4.KCleanˢ   H permˢ-K
    kfac-gen-resˢ = TKB4.kfac-gen-resˢ H permˢ-K

    private
      ein-disjⁱ : Fin H.nE → List (Fin H.nV) → Set
      ein-disjⁱ e L = All (λ k → extract-elem k L ≡ nothing) (H.ein e)

    ----------------------------------------------------------------------
    -- ## SKIP case of `HeadSlideˢ`.
    --
    -- When `e` does NOT fire on the clean K-side `s_R` (and `H.ein e`
    -- disjoint from `L`), it does not fire on `L ++ s_R` either
    -- (`extract-prefix-++ˡ-left-nothing`); both `edge-stepˢ` are `idˢ`,
    -- `β = ↭-refl`, and `KCleanHeadˢ` collapses to `idˢ` by `⊗-id`/`cast-id`.
    ----------------------------------------------------------------------

    -- The SKIP `HeadSlideˢ`, stated against ABSTRACT edge-step results so the
    -- two propositional SKIP equalities can be discharged by pattern matching.
    -- With both edge-steps SKIPped (`proj₁ = its stack`, `proj₂ = idˢ`), the
    -- slide equation is `idˢ ∘ˢ idˢ ≈ KCleanHeadˢ`, and `KCleanHeadˢ` is a
    -- same-endpoint cast of `idˢ {m L} ⊗ˢ idˢ`, which collapses by `⊗-id`
    -- then `cast-id`.
    private
      -- With both `extract-prefix` calls rewritten to `nothing`, the two
      -- `edge-stepˢ`-`with` blocks reduce, exposing `proj₁ = its stack`,
      -- `proj₂ = idˢ`; `KCleanHeadˢ` becomes a same-endpoint cast of
      -- `idˢ {m L} ⊗ˢ idˢ`.
      head-slide-skip-core
        : ∀ (e : Fin H.nE) (L s_R : List (Fin H.nV))
        → extract-prefix (H.ein e) s_R ≡ nothing
        → extract-prefix (H.ein e) (L ++ s_R) ≡ nothing
        → HeadSlideˢ e L s_R
      head-slide-skip-core e L s_R eqn eqn-LR
        rewrite eqn | eqn-LR = Perm.↭-refl , slide
        where
          q : m (L ++ s_R) ≡ m L ++ m s_R
          q = map-++ vl L s_R

          slide
            : permuteˢ {xs = L ++ s_R} Perm.↭-refl ∘ˢ idˢ {m (L ++ s_R)}
              ≈ˢ castˢ (sym q) (sym q) (idˢ {m L} ⊗ˢ idˢ {m s_R})
          slide =
            ≈-trans idˡ
              (≈-sym (≈-trans (cast-resp (sym q) (sym q) ⊗-id)
                              (cast-id (sym q) (sym q))))

    head-slide-skip
      : ∀ (e : Fin H.nE) (L s_R : List (Fin H.nV))
      → ein-disjⁱ e L
      → extract-prefix (H.ein e) s_R ≡ nothing
      → HeadSlideˢ e L s_R
    head-slide-skip e L s_R disj eqn =
      head-slide-skip-core e L s_R eqn
        (extract-prefix-++ˡ-left-nothing (H.ein e) L s_R disj eqn)

    ----------------------------------------------------------------------
    -- ## FIRE case of `HeadSlideˢ`.
    --
    -- When `e` fires on the clean K-side `s_R` (residual `rest_R`, perm `p`)
    -- and `H.ein e` is disjoint from `L`, `extract-prefix-++ˡ-left` pins the
    -- `(L ++ s_R)`-fire to residual `L ++ rest_R` with derivation `D`, so
    -- `proj₂ (edge-stepˢ (L ++ s_R) e) = fire-termˢ e (L ++ s_R) (L ++ rest_R) D`
    -- DEFINITIONALLY.  `fire-slideˢ` factors this into the output block-braid
    -- `castₒ = castˢ (odom)(ocod)(permuteˢ (obraid e L rest_R))` composed with
    -- the framed clean head `idˢ {m L} ⊗ˢ fire-termˢ e s_R rest_R p` — and that
    -- framed factor IS the body of `KCleanHeadˢ`.  We absorb `castₒ` by the
    -- slide braid `β` whose `permuteˢ` is a cast of `permuteˢ (↭-sym obraid)`,
    -- collapsing `permuteˢ β ∘ˢ castₒ` to a pure cast by `pvv-inverse-leftˢ`.
    --
    -- Requires `Unique ((L ++ H.ein e) ++ rest_R)` (the `fire-slideˢ` side
    -- condition; sourced by the caller from the run reservoir freshness).
    ----------------------------------------------------------------------

    private
      -- the slide braid: move the fired output block `H.eout e` past `L`,
      -- framed by `rest_R` (assoc-glued `↭-sym (obraid e L rest_R)`).
      slideβ
        : (e : Fin H.nE) (L rest_R : List (Fin H.nV))
        → (H.eout e ++ (L ++ rest_R)) Perm.↭ (L ++ (H.eout e ++ rest_R))
      slideβ e L rest_R =
        Perm.trans (Perm.↭-reflexive (sym (++-assoc (H.eout e) L rest_R)))
          (Perm.trans (Perm.↭-sym (obraid e L rest_R))
                      (Perm.↭-reflexive (++-assoc L (H.eout e) rest_R)))

      ----------------------------------------------------------------------
      -- ## `slide-braid-cancel` — the slide braid absorbs `castₒ`.
      --
      -- `permuteˢ β ∘ˢ castˢ (odom)(ocod)(permuteˢ obraid)` collapses to a pure
      -- identity-cast, because `β`'s middle factor is `↭-sym obraid`, cancelled
      -- against `castₒ`'s `permuteˢ obraid` by `pvv-inverse-leftˢ`.  The
      -- surrounding `↭-reflexive` braids + `odom`/`ocod` casts combine (UIP) into
      -- the single endpoint cast `castˢ refl (sym (map-++ vl L (eout++rest))) idˢ`.
      ----------------------------------------------------------------------

      slide-braid-cancel
        : ∀ (e : Fin H.nE) (L rest_R : List (Fin H.nV))
        → permuteˢ (slideβ e L rest_R)
            ∘ˢ castˢ (odom e L rest_R) (ocod e L rest_R)
                     (permuteˢ (obraid e L rest_R))
          ≈ˢ castˢ refl (sym (map-++ vl L (H.eout e ++ rest_R)))
                   (idˢ {m L ++ m (H.eout e ++ rest_R)})
      slide-braid-cancel e L rest_R =
        -- permuteˢ β = permuteˢ C ∘ˢ (permuteˢ B ∘ˢ permuteˢ A)
        ≈-trans (∘-resp (pvv-transˢ (Perm.↭-reflexive (sym aEO))
                                    (Perm.trans B C)) ≈-refl)
        (≈-trans (∘-resp (∘-resp (pvv-transˢ B C) ≈-refl) ≈-refl)
        -- ((permuteˢ C ∘ permuteˢ B) ∘ permuteˢ A) ∘ castₒ : reassociate fully
        (≈-trans assocˢ
        (≈-trans assocˢ
          -- permuteˢ C ∘ (permuteˢ B ∘ (permuteˢ A ∘ castₒ))
          (≈-trans (∘-resp ≈-refl (∘-resp ≈-refl A∘castₒ))
          (≈-trans (∘-resp ≈-refl B∘rest)
            C∘rest)))))
        where
          EO  = H.eout e
          aEO = ++-assoc EO L rest_R
          aL  = ++-assoc L EO rest_R
          obr = obraid e L rest_R
          B   = Perm.↭-sym obr
          C   = Perm.↭-reflexive aL

          castₒ : HomS (m L ++ m (EO ++ rest_R)) (m (EO ++ (L ++ rest_R)))
          castₒ = castˢ (odom e L rest_R) (ocod e L rest_R) (permuteˢ obr)

          -- permuteˢ A ≈ castˢ (ocod) refl idˢ  (refl-trivial + idcast-flip + UIP).
          permA-cast
            : permuteˢ (Perm.↭-reflexive (sym aEO))
              ≈ˢ castˢ (ocod e L rest_R) refl (idˢ {m ((EO ++ L) ++ rest_R)})
          permA-cast =
            ≈-trans (ScrH.refl-trivial (sym aEO))
            (≈-trans (idcast-flip (cong m (sym aEO)))
              (≡⇒≈ˢ (cast-irrel (sym (cong m (sym aEO))) (ocod e L rest_R)
                       refl refl (idˢ {m ((EO ++ L) ++ rest_R)}))))

          -- permuteˢ A ∘ castₒ ≈ castˢ (odom) refl (permuteˢ obr)
          A∘castₒ
            : permuteˢ (Perm.↭-reflexive (sym aEO)) ∘ˢ castₒ
              ≈ˢ castˢ (odom e L rest_R) refl (permuteˢ obr)
          A∘castₒ =
            ≈-trans (∘-resp permA-cast ≈-refl)
            -- castˢ (ocod) refl idˢ ∘ castˢ (odom)(ocod)(permuteˢ obr)
            (≈-trans
              (≈-sym (∘-cast-split (odom e L rest_R) (ocod e L rest_R) refl
                        (idˢ {m ((EO ++ L) ++ rest_R)}) (permuteˢ obr)))
              (cast-resp (odom e L rest_R) refl idˡ))

          -- permuteˢ B ∘ castˢ (odom) refl (permuteˢ obr)
          --   ≈ castˢ (odom) refl idˢ   (pvv-inverse-leftˢ obr)
          B∘rest
            : permuteˢ B ∘ˢ castˢ (odom e L rest_R) refl (permuteˢ obr)
              ≈ˢ castˢ (odom e L rest_R) refl (idˢ {m ((L ++ EO) ++ rest_R)})
          B∘rest =
            ≈-trans
              (≈-sym (∘-cast-split (odom e L rest_R) refl refl
                        (permuteˢ B) (permuteˢ obr)))
              (cast-resp (odom e L rest_R) refl
                (≈-trans (∘-resp (≡⇒≈ˢ refl) ≈-refl)
                         (pvv-inverse-leftˢ obr)))

          -- permuteˢ C ∘ castˢ (odom) refl idˢ ≈ castˢ (odom)(cong m aL) idˢ.
          C∘rest
            : permuteˢ C ∘ˢ castˢ (odom e L rest_R) refl (idˢ {m ((L ++ EO) ++ rest_R)})
              ≈ˢ castˢ refl (sym (map-++ vl L (EO ++ rest_R)))
                       (idˢ {m L ++ m (EO ++ rest_R)})
          C∘rest =
            ≈-trans (∘-resp (ScrH.refl-trivial aL) ≈-refl)
            -- castˢ refl (cong m aL) idˢ ∘ castˢ (odom) refl idˢ  (merge, idˡ)
            (≈-trans
              (≈-sym (∘-cast-split (odom e L rest_R) refl (cong m aL)
                        (idˢ {m ((L ++ EO) ++ rest_R)})
                        (idˢ {m ((L ++ EO) ++ rest_R)})))
            (≈-trans
              (cast-resp (odom e L rest_R) (cong m aL) idˡ)
              -- castˢ (odom)(cong m aL) idˢ{X₀} → bridge to castᴵ via idˢ{Y₀}.
              end-bridge))
            where
              X₀ = m ((L ++ EO) ++ rest_R)
              Y₀ = m L ++ m (EO ++ rest_R)
              od = odom e L rest_R   -- od : X ≡ Y

              -- castˢ od (cong m aL) idˢ{X}
              --   ≈ castˢ refl (trans (sym od)(cong m aL)) (castˢ od od idˢ{X})
              --   ≈ castˢ refl (trans (sym od)(cong m aL)) idˢ{Y}
              --   ≈ castᴵ
              end-bridge
                : castˢ od (cong m aL) (idˢ {X₀})
                  ≈ˢ castˢ refl (sym (map-++ vl L (EO ++ rest_R))) (idˢ {Y₀})
              end-bridge =
                ≈-trans
                  (≡⇒≈ˢ (sym
                    (trans (cast-fuse od refl od (trans (sym od) (cong m aL))
                              (idˢ {X₀}))
                           (cast-irrel (trans od refl) od
                              (trans od (trans (sym od) (cong m aL))) (cong m aL)
                              (idˢ {X₀})))))
                (≈-trans
                  (cast-resp refl (trans (sym od) (cong m aL)) (cast-id od od))
                  (≡⇒≈ˢ (cast-irrel refl refl (trans (sym od) (cong m aL))
                           (sym (map-++ vl L (EO ++ rest_R))) (idˢ {Y₀}))))

    head-slide-fire
      : ∀ (e : Fin H.nE) (L s_R rest_R : List (Fin H.nV))
          (p : s_R Perm.↭ H.ein e ++ rest_R)
      → ein-disjⁱ e L
      → extract-prefix (H.ein e) s_R ≡ just (rest_R , p)
      → Unique ((L ++ H.ein e) ++ rest_R)
      → HeadSlideˢ e L s_R
    head-slide-fire e L s_R rest_R p disj eqR uIn
      with extract-prefix-++ˡ-left (H.ein e) L s_R disj eqR
    ... | D , eqLR
      rewrite eqR | eqLR = slideβ e L rest_R , slide-eq
      where
        EO   = H.eout e
        mLs  = map-++ vl L s_R
        mLo  = map-++ vl L (EO ++ rest_R)
        Xf   = idˢ {m L} ⊗ˢ fire-termˢ e s_R rest_R p
        castₒ : HomS (m L ++ m (EO ++ rest_R)) (m (EO ++ (L ++ rest_R)))
        castₒ = castˢ (odom e L rest_R) (ocod e L rest_R)
                      (permuteˢ (obraid e L rest_R))

        slide-eq
          : permuteˢ (slideβ e L rest_R)
              ∘ˢ fire-termˢ e (L ++ s_R) (L ++ rest_R) D
            ≈ˢ castˢ (sym mLs) (sym mLo) Xf
        slide-eq =
          -- rewrite the fired layer by `fire-slideˢ`.
          ≈-trans (∘-resp ≈-refl (fire-slideˢ e L s_R rest_R D p uIn))
          -- permuteˢ β ∘ castˢ (sym mLs) refl (castₒ ∘ Xf)
          (≈-trans (∘-resp ≈-refl
                     (≈-trans (∘-cast-split (sym mLs) refl refl castₒ Xf)
                              (∘-resp (≡⇒≈ˢ refl) ≈-refl)))
          -- permuteˢ β ∘ (castₒ ∘ castˢ (sym mLs) refl X)
          (≈-trans (≈-sym assocˢ)
          -- (permuteˢ β ∘ castₒ) ∘ castˢ (sym mLs) refl X
          (≈-trans (∘-resp (slide-braid-cancel e L rest_R) ≈-refl)
          -- castᴵ ∘ castˢ (sym mLs) refl X  →  merge to castˢ (sym mLs)(sym mLo)(idˢ ∘ Xf)
          (≈-trans
            (≈-sym (∘-cast-split (sym mLs) refl (sym mLo)
                      (idˢ {m L ++ m (EO ++ rest_R)}) Xf))
            (cast-resp (sym mLs) (sym mLo) idˡ)))))

    ----------------------------------------------------------------------
    -- ## The FIRE/SKIP dispatcher → a uniform `HeadSlideˢ` family.
    --
    -- For a fixed disjoint block `L`, dispatch on whether `e` fires on `s_R`:
    -- FIRE uses `head-slide-fire` (needs `Unique ((L++ein e)++rest_R)`, supplied
    -- per-configuration by `fuq`), SKIP uses `head-slide-skip`.
    ----------------------------------------------------------------------

    head-slide
      : ∀ (L : List (Fin H.nV)) (e : Fin H.nE) (s_R : List (Fin H.nV))
      → ein-disjⁱ e L
      → (∀ (rest_R : List (Fin H.nV)) (p : s_R Perm.↭ H.ein e ++ rest_R)
         → extract-prefix (H.ein e) s_R ≡ just (rest_R , p)
         → Unique ((L ++ H.ein e) ++ rest_R))
      → HeadSlideˢ e L s_R
    head-slide L e s_R disj fuq = aux (extract-prefix (H.ein e) s_R) refl
      where
        aux : (w : Maybe (Σ[ rest ∈ List (Fin H.nV) ] s_R Perm.↭ H.ein e ++ rest))
            → extract-prefix (H.ein e) s_R ≡ w
            → HeadSlideˢ e L s_R
        aux (just (rest_R , p)) eqR =
          head-slide-fire e L s_R rest_R p disj eqR (fuq rest_R p eqR)
        aux nothing eqn = head-slide-skip e L s_R disj eqn

    private
      -- `s ↭ (L ++ ein e) ++ rest_R` from `pf : s ↭ L ++ s_R` and the fire perm.
      fire-stack-perm
        : ∀ (e : Fin H.nE) (L s_R s rest_R : List (Fin H.nV))
        → s Perm.↭ L ++ s_R → s_R Perm.↭ H.ein e ++ rest_R
        → s Perm.↭ (L ++ H.ein e) ++ rest_R
      fire-stack-perm e L s_R s rest_R pf p =
        Perm.trans pf
          (Perm.trans (PermProp.++⁺ˡ L p)
            (Perm.↭-reflexive (sym (++-assoc L (H.ein e) rest_R))))

    ----------------------------------------------------------------------
    -- ## `head-provider-res` — the SLIM `HeadProviderRˢ` from disjointness
    -- ALONE.  It needs NO post-edge `Unique` family
    -- `puq` (which is false in general): the reservoir-threaded fold derives
    -- each step's `Unique` itself.  The FIRE side-condition `Unique
    -- ((L++ein e)++rest_R)` is still derived in-place from the round-trip
    -- `Unique s` along `fire-stack-perm`.
    ----------------------------------------------------------------------

    head-provider-res
      : ∀ (L : List (Fin H.nV))
      → HeadProviderRˢ (λ e → ein-disjⁱ e L) L
    head-provider-res L e disj s_R s pf us =
      let slide = head-slide L e s_R disj fuq
          pf1 , hr = head-reconcile-from-slide e L s_R s pf us slide
      in pf1 , hr
      where
        fuq : ∀ (rest_R : List (Fin H.nV)) (p : s_R Perm.↭ H.ein e ++ rest_R)
              → extract-prefix (H.ein e) s_R ≡ just (rest_R , p)
              → Unique ((L ++ H.ein e) ++ rest_R)
        fuq rest_R p _ =
          SU.Unique-resp-↭ (fire-stack-perm e L s_R s rest_R pf p) us

    ----------------------------------------------------------------------
    -- ## `kblock-factorize-res` — the WHOLE K-block run factorization,
    -- UNCONDITIONAL except for the disjointness + the run-order RESERVOIR
    -- freshness `SUR.Reservoir≤1 H es s` (a TRUE invariant along the actual
    -- run, sourced from linearity by `dom-reservoir-prov`/`reservoir-split`).
    -- This is the (d)-core with the false `puq` ELIMINATED: it feeds the slim
    -- `head-provider-res` to the reservoir-threaded fold `kfac-gen-resˢ`.
    ----------------------------------------------------------------------

    kblock-factorize-res
      : ∀ (L : List (Fin H.nV))
      → ∀ (es : List (Fin H.nE)) → All (λ e → ein-disjⁱ e L) es
      → ∀ (s_R s : List (Fin H.nV))
          (pf : s Perm.↭ L ++ s_R)
          (Br : (L ++ proj₁ (process-edgesˢ es s_R))
                Perm.↭ proj₁ (process-edgesˢ es s))
      → SUR.Reservoir≤1 H es s
      → proj₂ (process-edgesˢ es s)
        ≈ˢ permuteˢ Br ∘ˢ (KCleanˢ es L s_R ∘ˢ permuteˢ pf)
    kblock-factorize-res L es disj s_R s pf Br res =
      kfac-gen-resˢ L (head-provider-res L) es disj s_R s pf Br res

--------------------------------------------------------------------------------
-- ## K-block disjointness at the concrete `hTensor` layout.
--
-- The K-edge inputs `H.ein (ψK eK) = map injR (K.ein eK)` are disjoint from any
-- `injL`-block `map injL P` — the side condition `head-provider`/`head-slide`
-- need at `L = Lpre = map injL Gd.dom`, `e = ψK eK`.  Mirror of
-- `TensorBraid.Braid.g-disjoint`/`injL∉injRs`, on the K-side (`injR∉injLs`).
--------------------------------------------------------------------------------


------------------------------------------------------------------------
-- ===== submodule KBlockDisjoint =====
------------------------------------------------------------------------
open import Categories.APROP.Hypergraph.Model.FromAPROP sig hiding (FlatGen)
open import Categories.APROP.Hypergraph.Soundness.Decode.Decode sig using (extract-elem)
open import Data.Fin using (Fin; _↑ˡ_; _↑ʳ_; splitAt)
open import Data.Fin.Properties using (splitAt-↑ˡ; splitAt-↑ʳ)
import Data.Fin.Properties as FinP
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (yes; no)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.List using (List; []; _∷_; _++_; map)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Relation.Binary.PropositionalEquality

module KBlockDisjoint (G K : Hypergraph FlatGen) where
  private
    module G = Hypergraph G
    module K = Hypergraph K
    module C = Hypergraph (hTensor G K)
  open hTensor-impl G K using (injL; injR; ein-c-inj₂-red)
  open Dec.StrictDecoder (hTensor G K) using (vl)

  ψK : Fin K.nE → Fin C.nE
  ψK eK = G.nE ↑ʳ eK

  -- `injR j ≢ injL k` (split lands in `inj₂` vs `inj₁`).
  injR≢injL : ∀ {j : Fin K.nV} {k : Fin G.nV} → injR j ≡ injL k → ⊥
  injR≢injL {j} {k} eq with trans (sym (splitAt-↑ʳ G.nV K.nV j))
                            (trans (cong (splitAt G.nV) eq)
                                   (splitAt-↑ˡ G.nV k K.nV))
  ... | ()

  -- `injR j` is absent from any `injL`-block.
  injR∉injLs : ∀ (j : Fin K.nV) (P : List (Fin G.nV))
             → extract-elem (injR j) (map injL P) ≡ nothing
  injR∉injLs j []       = refl
  injR∉injLs j (k ∷ ks) with injL k FinP.≟ injR j
  ... | yes p  = ⊥-elim (injR≢injL (sym p))
  ... | no  _  rewrite injR∉injLs j ks = refl

  -- `ein-disjⁱ (ψK eK) (map injL P)` at `H = hTensor G K`.
  kblock-ein-disjoint
    : ∀ (eK : Fin K.nE) (P : List (Fin G.nV))
    → All (λ k → extract-elem k (map injL P) ≡ nothing)
          (C.ein (ψK eK))
  kblock-ein-disjoint eK P =
    subst (λ ks → All (λ k → extract-elem k (map injL P) ≡ nothing) ks)
          (sym (ein-c-inj₂-red eK))
          (all-injR (K.ein eK))
    where
      all-injR : ∀ (js : List (Fin K.nV))
               → All (λ k → extract-elem k (map injL P) ≡ nothing)
                     (map injR js)
      all-injR []       = []
      all-injR (j ∷ js) = injR∉injLs j P ∷ all-injR js

--------------------------------------------------------------------------------
-- STATUS / OBSTRUCTION MAP — postulate-free, `--safe --without-K`.
--
-- PROVEN HERE (the genuine remaining mathematical content of (c′) + (c′-Unique)
-- + the (d)-core):
--   * `idcast-flip` — move an `idˢ`-cast's single endpoint across `≈ˢ`.
--   * `head-slide-skip` — the SKIP `HeadSlideˢ` (both `edge-stepˢ` are `idˢ`;
--     `KCleanHeadˢ` collapses by `⊗-id`/`cast-id`; `β = ↭-refl`).
--   * `slideβ` + `slide-braid-cancel` + `head-slide-fire` — the FIRE
--     `HeadSlideˢ`.  `extract-prefix-++ˡ-left` pins the `(L++s_R)`-fire to
--     residual `L++rest_R`, so the actual head IS `fire-termˢ e (L++s_R)
--     (L++rest_R) D`; `fire-slideˢ` factors it into the framed clean head up to
--     `castₒ = castˢ(odom)(ocod)(permuteˢ obraid)`, which `slideβ` absorbs by
--     `pvv-inverse-leftˢ` (`slide-braid-cancel`).  THE GENUINE NEW PER-EDGE
--     CONTENT of (c′), fully discharged.
--   * `head-slide` — the FIRE/SKIP dispatcher → a uniform `HeadSlideˢ` family.
--   * `head-provider-res` / `kblock-factorize-res` — the WHOLE K-block run
--     factorization
--       proj₂ (process-edgesˢ es s) ≈ˢ permuteˢ Br ∘ˢ (KCleanˢ es L s_R ∘ˢ permuteˢ pf)
--     UNCONDITIONAL against disjointness + the run-order reservoir freshness
--     (the instantiation of the proven fold `TKB4.kfac-gen-resˢ`).
--   * `KBlockDisjoint.kblock-ein-disjoint` — the K-edge inputs `map injR
--     (K.ein eK)` are disjoint from `map injL P` (mirror of `TensorBraid`'s
--     `injL∉injRs`), connecting `kblock-factorize` to the concrete K-block
--     `L = map injL Gd.dom`, `e = ψK eK`.
--
-- REMAINING to UNCONDITIONAL `decodePˢ-⊗` (NO new mathematics; pure plumbing,
-- BLOCKED only by module privacy — NOT by any unproven fact):
--
--   (d-tail/e) The reconcile to `TensorBraid.Braid.KBlockσ` requires the
--     `Braid`-LOCAL bindings `Krun`, `Gon`, `stkQ`, `Lpre`, `Rsuf`, `coeCod`,
--     `stkSplit₀`, `gframe`, `Kon-bridge`, `Gon-bridge` — all declared
--     `private` inside `TensorBraid.Braid`.  `KBlockσ`'s BODY (and hence any
--     inhabitant) mentions `Krun`/`Gon`/`stkSplit₀`, and the (e)-reconcile
--     algebra needs `gframe`/`Kon-bridge`/`run-split-atˢ`, none of which are
--     in scope from a separate module.  `kblock-factorize` supplies exactly the
--     K-prepend factorization that `KBlockσ` packages, and the post-edge
--     `Unique` family `puq` is the strict-run reservoir freshness
--     (`StackUniqueReach`, as in `process-edges-equivariantˢ`); the FIRE
--     post-edge `Unique (H.eout e ++ rest_R)` is the one fact NOT derivable from
--     bare `Unique s` (it needs `eout`-freshness, i.e. the reservoir — the
--     documented `kfac-genˢ`/`Unique`-threading design point).
--
--     CLOSING `decodePˢ-⊗` therefore needs ONE edit to `TensorBraid` (expose
--     `Krun`/`Gon`/`gframe`/`Kon-bridge`/`Rsuf`/`Lpre`/`stkQ`/`stkSplit₀`, or
--     inline the `KBlockσ` construction there feeding `kblock-factorize` + the
--     reservoir `puq`).  This file is "NEW file only", so that edit is out of
--     scope; the K-block factorization it would consume is COMPLETE and green
--     here.  `decodePˢ-⊗` is consequently NOT YET unconditional — it rests
--     solely on the (d-tail/e) plumbing, with the entire (c′) content closed.
--------------------------------------------------------------------------------

