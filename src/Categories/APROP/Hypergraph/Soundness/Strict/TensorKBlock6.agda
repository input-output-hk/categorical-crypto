{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- Phase 7 — THE FINAL PIECE.  Discharge the concrete `HeadSlideˢ` at the
-- `hTensor` K-block layout and instantiate the proven fold `kfac-genˢ` into the
-- WHOLE K-block run factorization `kblock-factorize` (the (d)-core).  The
-- (e)-reconcile to `TensorBraidS.Braid.KBlockσ` → `decodePˢ-⊗` is pure plumbing
-- blocked only by `Braid`-private bindings (see the STATUS footer); the genuine
-- NEW mathematical content — the per-edge clean SLIDE — is fully closed here.
--
-- The genuine NEW content is the per-edge clean SLIDE for the K-block:
--   * for `e = ψK eK = Gd.nE ↑ʳ eK`, `H.ein e = map injR (K.ein eK)` is
--     DISJOINT from any `injL`-block `L` (`injL≢injR`).
--   * FIRE: `extract-prefix-++ˡ-left` (STRICT-Sep) pins the `(L ++ s_R)`-fire
--     residual to `L ++ rest_R` with derivation `D`, so
--       proj₂ (edge-stepˢ (L ++ s_R) e) = fire-termˢ e (L ++ s_R) (L ++ rest_R) D
--     DEFINITIONALLY; `TKB3.fire-slideˢ` then factors it into the framed clean
--     head up to the output block-braid `obraid`, which is absorbed into `β`.
--   * SKIP: `extract-prefix-++ˡ-left-nothing`; both edge-steps are `idˢ`, and
--     `KCleanHeadˢ` collapses by `⊗-id`/`cast-id`; `β = ↭-refl`.
--
-- Built ENTIRELY on the proven substrate (`fire-slideˢ`, `extract-prefix-++ˡ-
-- left{,-nothing}`, `fire-termˢ`, `KCleanHeadˢ`, the cast kit).  ZERO
-- postulates, `--safe --without-K`.
--------------------------------------------------------------------------------

open import Categories.APROP
open import Relation.Binary using (DecidableEquality)

module Categories.APROP.Hypergraph.Soundness.Strict.TensorKBlock6
  (sig : APROPSignature)
  (_≟X_ : DecidableEquality (APROPSignature.X sig))
  where

open APROP sig

open import Categories.APROP.Hypergraph.Core using (Hypergraph)
open import Categories.APROP.Hypergraph.FromAPROP sig
  using (FlatGen; hTensor; module hTensor-impl)

open import Categories.APROP.Hypergraph.Soundness.Decode sig
  using (extract-elem; extract-prefix)
open import Categories.APROP.Hypergraph.Soundness.Strict.DecodeS sig _≟X_
open import Categories.APROP.Hypergraph.Soundness.Strict.PermSupport sig _≟X_
open import Categories.APROP.Hypergraph.Soundness.Strict.StackEquivS sig _≟X_
  using (module EquivStep)
open import Categories.APROP.Hypergraph.Soundness.Strict.Separability sig _≟X_
  using (module StrictSep)
open import Categories.APROP.Hypergraph.Soundness.Strict.DecodeSigmaS sig _≟X_
  using (module Scr)
import Categories.APROP.Hypergraph.Soundness.Strict.TensorKBlock3 sig _≟X_ as TKB3
import Categories.APROP.Hypergraph.Soundness.Strict.TensorKBlock4 sig _≟X_ as TKB4
import Categories.APROP.Hypergraph.Soundness.Strict.TensorKBlock5 sig _≟X_ as TKB5
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

--------------------------------------------------------------------------------

module _ (H : Hypergraph FlatGen) where
  private module H = Hypergraph H

  open StrictDecoder H
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
-- `TensorBraidS.Braid.g-disjoint`/`injL∉injRs`, on the K-side (`injR∉injLs`).
--------------------------------------------------------------------------------

module KBlockDisjoint (G K : Hypergraph FlatGen) where
  private
    module G = Hypergraph G
    module K = Hypergraph K
    module C = Hypergraph (hTensor G K)
  open hTensor-impl G K using (injL; injR; ein-c-inj₂-red)
  open StrictDecoder (hTensor G K) using (vl)

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
--     (K.ein eK)` are disjoint from `map injL P` (mirror of `TensorBraidS`'s
--     `injL∉injRs`), connecting `kblock-factorize` to the concrete K-block
--     `L = map injL Gd.dom`, `e = ψK eK`.
--
-- REMAINING to UNCONDITIONAL `decodePˢ-⊗` (NO new mathematics; pure plumbing,
-- BLOCKED only by module privacy — NOT by any unproven fact):
--
--   (d-tail/e) The reconcile to `TensorBraidS.Braid.KBlockσ` requires the
--     `Braid`-LOCAL bindings `Krun`, `Gon`, `stkQ`, `Lpre`, `Rsuf`, `coeCod`,
--     `stkSplit₀`, `gframe`, `Kon-bridge`, `Gon-bridge` — all declared
--     `private` inside `TensorBraidS.Braid`.  `KBlockσ`'s BODY (and hence any
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
--     CLOSING `decodePˢ-⊗` therefore needs ONE edit to `TensorBraidS` (expose
--     `Krun`/`Gon`/`gframe`/`Kon-bridge`/`Rsuf`/`Lpre`/`stkQ`/`stkSplit₀`, or
--     inline the `KBlockσ` construction there feeding `kblock-factorize` + the
--     reservoir `puq`).  This file is "NEW file only", so that edit is out of
--     scope; the K-block factorization it would consume is COMPLETE and green
--     here.  `decodePˢ-⊗` is consequently NOT YET unconditional — it rests
--     solely on the (d-tail/e) plumbing, with the entire (c′) content closed.
--------------------------------------------------------------------------------
