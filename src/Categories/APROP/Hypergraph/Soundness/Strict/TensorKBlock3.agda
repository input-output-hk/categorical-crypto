{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- Phase 4: the FIRE-SLIDE assembly (`fire-slideˢ`) — the gating brick of the
-- K-block prepend braid.  A single fired box on `L ++ xs` (`L` disjoint from
-- the residual) slides past the carried block `L`, up to the canonical OUTPUT
-- block-braid `permuteˢ (obraid e L rest)`:
--
--   fire-termˢ e (L ++ xs) (L ++ rest) perm'
--     ≈ˢ castˢ (odom e L rest) (ocod e L rest) (permuteˢ (obraid e L rest))
--         ∘ˢ (idˢ {m L} ⊗ˢ fire-termˢ e xs rest p)
--
-- Assembled from the proven `Strict.TensorKBlock` box-slide brick
-- (`box-slide-restˢ`) and the `Strict.TensorKBlock2` σ-block / reconciliation
-- bricks (`blockσ-perm`, `out-braid-σ`, `in-σ-perm`, `in-reconcile`,
-- `mid-assoc`, `framed-fire-split`).  This file holds ONLY the cast/assoc glue.
--------------------------------------------------------------------------------

open import Categories.APROP
open import Relation.Binary using (DecidableEquality)

module Categories.APROP.Hypergraph.Soundness.Strict.TensorKBlock3
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
import Categories.APROP.Hypergraph.Soundness.Strict.TensorKBlock sig _≟X_ as TKB
import Categories.APROP.Hypergraph.Soundness.Strict.TensorKBlock2 sig _≟X_ as TKB2

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

module _ (H : Hypergraph FlatGen) where
  private module H = Hypergraph H

  open StrictDecoder H
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
--   (d) EQUIVARIANCE — conjugate `TensorBraidS.Braid.Krun` (on the actual
--       post-G stack) onto the clean mixed stack via the proven
--       `StackEquivS.process-edges-equivariantˢ`; relabel via `Kon-bridge`.
--
--   (e) FINAL RECONCILE — assemble with `gframe`/`Gon-bridge`, route block runs
--       into `decodePˢ f`/`decodePˢ g` via `DecodeComposeS.permuteˢ-X`, collapse
--       accumulated braids + `permuteˢ cand` by `perm-rigidˢ` on `Unique
--       Hf.cod`, producing the `KBlockσ` witness fed to
--       `TensorBraidS.Braid.decodePˢ-⊗-cond` → UNCONDITIONAL `decodePˢ-⊗`.
--------------------------------------------------------------------------------
