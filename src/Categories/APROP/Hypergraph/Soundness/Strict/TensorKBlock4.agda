{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- Phase 5: the K-BLOCK PREPEND FOLD (`kfac-genˢ` / `kblock-factorˢ`) — the
-- recursive fold that turns the per-layer slide brick `TKB3.fire-slideˢ` into
-- the whole-K-block factorization, the last constructive residual of part-Iˢ
-- (the strict ⊗-shape).
--
-- The strict twin of the non-strict `DecodeTensorShape.kfac-gen`/`kblock-factor`
-- (the K-prepend perm-tracking induction).  K-edges PREPEND their `eout` to the
-- FRONT of the running stack, before the carried `Lpre = map injL G.dom`
-- prefix, so the actual post-edge stack only `↭`s the clean
-- `Lpre ++ K-stack` form.  We therefore thread the actual stack `s` with a perm
-- `pf : s ↭ Lpre ++ map vl s_R` to the clean form and accumulate a braid `Br`
-- from the clean target back to the actual run codomain, exactly as the
-- non-strict `kfac-gen` does.
--
-- The recursion MIRRORS `process-edgesˢ`'s own structure (`StrictDecoder`):
--   * `[]`   — the empty run is `idˢ`; `pf`/`Br` round-trip collapses by
--              `perm-rigidˢ` on the `Unique` stack (the single keystone use).
--   * `e ∷ es` — fire the head C-edge `ψK e`, reconcile the actual stack to the
--              clean prefix via `kfac-headˢ` (built on `fire-slideˢ` +
--              `process-edges-equivariantˢ`), then recurse on the tail with the
--              advanced clean perm `pf1`.
--
-- THE PER-EDGE HEAD `kfac-headˢ` is supplied as an explicit, fully-typed
-- interface (`HeadReconcileˢ`).  It is NOT a postulate: it is a hypothesis of
-- the fold, discharged by the caller from `fire-slideˢ` + equivariance.  The
-- fold itself — the gating recursive construction — is proven UNCONDITIONALLY
-- below.
--------------------------------------------------------------------------------

open import Categories.APROP
open import Relation.Binary using (DecidableEquality)

module Categories.APROP.Hypergraph.Soundness.Strict.TensorKBlock4
  (sig : APROPSignature)
  (_≟X_ : DecidableEquality (APROPSignature.X sig))
  where

open APROP sig

open import Categories.APROP.Hypergraph.Core using (Hypergraph)
open import Categories.APROP.Hypergraph.FromAPROP sig using (FlatGen)

open import Categories.APROP.Hypergraph.Soundness.Decode sig
  using (edge-step; process-edges)
open import Categories.APROP.Hypergraph.Soundness.Strict.DecodeS sig _≟X_
open import Categories.APROP.Hypergraph.Soundness.Strict.PermSupport sig _≟X_
open import Categories.APROP.Hypergraph.Soundness.Strict.StackEquivS sig _≟X_
  using (module EquivStep)
import Categories.APROP.Hypergraph.Soundness.Strict.DecodeComposeS sig _≟X_ as DC
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

--------------------------------------------------------------------------------

module _ (H : Hypergraph FlatGen) where
  private module H = Hypergraph H

  open StrictDecoder H
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
    -- This is the EXACT threading `process-edges-equivariantˢ` (StackEquivS)
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
-- OBSTRUCTION / RESIDUAL MAP — the remaining chain to `KBlockσ`.
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
-- REMAINING (the assembly tail to `KBlockσ`):
--
--   (c′) DISCHARGE `HeadProviderˢ` at `L = map injL Gd.dom`, `e = ψK eK`.  This
--        is the genuine remaining per-edge content, combining:
--          • the actual→clean ROUTING `StackEquivS.edge-step-equivariantˢ`
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
--        SAME stacks via `Run.stacks-agree`).  Estimated ~250-400 LOC of
--        cast/braid glue; NO new math beyond `fire-slideˢ` + equivariance.
--
--   (d) EQUIVARIANCE — instantiate `kfac-genˢ` at the `Krun` of
--       `TensorBraidS.Braid` (the actual post-G stack `proj₁ (process-edgesˢ
--       gblk Hf.dom)`), with `pf` the `gframe`/`stack-sepˢ` clean perm and
--       `Br` the accumulated K-prepend braid; relabel the clean K-run to
--       `decodePˢ g`'s run via `Kon-bridge`.
--
--   (e) FINAL RECONCILE — assemble with `gframe`/`Gon-bridge` (G-side =
--       `decodePˢ f ⊗ˢ idˢ`-ish), route the clean K-run into `decodePˢ g` via
--       `DecodeComposeS.permuteˢ-X`, collapse the accumulated braid +
--       `permuteˢ cand` by `perm-rigidˢ` on `Unique Hf.cod`, producing the
--       `KBlockσ` witness fed to `TensorBraidS.Braid.decodePˢ-⊗-cond` → the
--       UNCONDITIONAL `decodePˢ-⊗`.
--
-- All substrate (`fire-slideˢ`, `edge-step-equivariantˢ`, `edge-step-↑ʳ-on-perm`,
-- `Kon-bridge`/`Gon-bridge`/`gframe`, `permuteˢ-X`, `perm-rigidˢ`,
-- `run-split-atˢ`) is in place; the remaining work is the (c′) per-edge head
-- discharge + the (d)/(e) cast/stack collapse algebra.
--------------------------------------------------------------------------------
