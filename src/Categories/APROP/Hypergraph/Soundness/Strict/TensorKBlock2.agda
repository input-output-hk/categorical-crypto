{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- Discharge of the LAST ⊗-shape residual `KBlockσ` of `Strict.TensorBraidS`.
--
-- Builds on the box-slide bricks of `Strict.TensorKBlock` (`box-slide-restˢ`,
-- `box-block-slideˢ`, `box-conjˡ`).  The remaining chain (per the TensorKBlock
-- foot-of-file obstruction map):
--
--   (b) `fire-slideˢ`   — a single fired box on `L ++ xs` (`L` disjoint from
--       the fired residual) slides past the carried block `L`, up to an output
--       block-braid `permuteˢ (shifts L (eout e))`.  Built from
--       `box-slide-restˢ` by absorbing the output σ into `permuteˢ (shifts …)`
--       (`perm-rigidˢ` on the `Unique` output stack) and reconciling the input
--       σ + `idˢ{L} ⊗ permuteˢ p` against `perm'` (`perm-rigidˢ` on the `Unique`
--       input stack).  Framings by `permuteˢ-frameˡ` / `Perm′.permuteˢ-frame`.
--
-- (c)–(e) — `kblock-factorˢ`, equivariance, final reconcile → `KBlockσ`.
--------------------------------------------------------------------------------

open import Categories.APROP
open import Relation.Binary using (DecidableEquality)

module Categories.APROP.Hypergraph.Soundness.Strict.TensorKBlock2
  (sig : APROPSignature)
  (_≟X_ : DecidableEquality (APROPSignature.X sig))
  where

open APROP sig

open import Categories.APROP.Hypergraph.Core using (Hypergraph)
open import Categories.APROP.Hypergraph.FromAPROP sig using (FlatGen)

open import Categories.APROP.Hypergraph.Soundness.Strict.DecodeS sig _≟X_
open import Categories.APROP.Hypergraph.Soundness.Strict.PermSupport sig _≟X_
open import Categories.APROP.Hypergraph.Soundness.Strict.Separability sig _≟X_
  using (module StrictSep)
open import Categories.APROP.Hypergraph.Soundness.Strict.DecodeSigmaS sig _≟X_
  using (module Scr)
open import Categories.APROP.Hypergraph.Soundness.Strict.BlockSwapComm sig _≟X_
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

--------------------------------------------------------------------------------
-- The per-hypergraph K-block braid machinery.

module _ (H : Hypergraph FlatGen) where
  private module H = Hypergraph H

  open StrictDecoder H
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
-- OBSTRUCTION / RESIDUAL MAP — the remaining chain to `KBlockσ`.
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
-- REMAINING (the assembly tail, NO new math, ALL substrate present):
--
--   (b) `fire-slideˢ` — the single fired box on `L ++ xs` (statement above,
--       well-typed).  The remaining work is the cast/assoc GLUE joining the
--       proven sub-bricks: rewrite the box via `box-slide-restˢ′`, reassociate
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
--   (d) EQUIVARIANCE — conjugate `TensorBraidS.Braid.Krun` (on the actual
--       post-G stack) onto the clean mixed stack via the proven
--       `StackEquivS.process-edges-equivariantˢ`; relabel via `Kon-bridge`.
--
--   (e) FINAL RECONCILE — assemble with `gframe`/`Gon-bridge`, route block runs
--       into `decodePˢ f`/`decodePˢ g` via `DecodeComposeS.permuteˢ-X`, and
--       collapse the accumulated braids + `permuteˢ cand` by `perm-rigidˢ` on
--       the `Unique` cod `Hf.cod`, producing the `KBlockσ` witness fed to
--       `TensorBraidS.Braid.decodePˢ-⊗-cond` → UNCONDITIONAL `decodePˢ-⊗`.
--------------------------------------------------------------------------------

