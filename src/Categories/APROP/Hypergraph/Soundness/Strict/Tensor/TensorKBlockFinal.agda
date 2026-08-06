{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- Phase 8 — THE FINAL WIRING.  Closes the strict ⊗-shape
--
--     decodePˢ-⊗ : decodePˢ (f ⊗₁ g) ≈ˢ decodePˢ f ⊗ˢ decodePˢ g    (UNCOND.)
--
-- by supplying the LAST residual — the K-block braid `KBlockσ` of
-- `TensorBraid.Braid` — from the RESERVOIR-THREADED K-block factorization
-- `TensorKBlock.TKB6.kblock-factorize-res` (the false per-edge `Unique`-family
-- `puq` is GONE: each step's `Unique` is DERIVED from the run-order freshness
-- invariant `StackUniqueReach.Reservoir≤1`).
--
-- The two ingredients fed to `Braid.Reconcile-e.KBlockσ-from-factorization`:
--   * the K-prepend braid `Br`, read off the term-free stack permutation
--     `DecodeAttempt.process-edges-↑ʳ-on-perm` (the K-edge `eout`s prepend to
--     the stack front), bridged strict↔non-strict by `Run.stacks-agree`;
--   * the factorization equation, from `kblock-factorize-res` at the concrete
--     K-block layout (`L = sG`, `s = aG`, `s_R = Rsuf`, `es = kblk`), with the
--     disjointness `All (ein-disjⁱ · sG) kblk` from `kblock-ein-disjoint`, and
--     the reservoir `Reservoir≤1 ⟪f⊗g⟫ kblk aG` from `dom-reservoir-prov`
--     (⇐ linearity) + `reservoir-split` at the `gblk ++ kblk` range split.
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

open import Categories.APROP.Hypergraph.Model.Core using (Hypergraph)
open import Categories.APROP.Hypergraph.Model.FromAPROP sig
  using (FlatGen; range; module hTensor-impl)
open import Categories.APROP.Hypergraph.Model.Translation sig using (⟪_⟫)
open import Categories.APROP.Hypergraph.Model.Invariant sig using (range-++)

open import Categories.APROP.Hypergraph.Soundness.Decode.Decode sig
  using (extract-elem; process-edges)
open import Categories.APROP.Hypergraph.Soundness.Strict.Decode.Decode sig _≟X_
open import Categories.APROP.Hypergraph.Soundness.Strict.Perm.PermSupport sig _≟X_
import Categories.APROP.Hypergraph.Soundness.Strict.Tensor.TensorBraid sig _≟X_ as TB
open import Categories.APROP.Hypergraph.Soundness.Strict.Tensor.TensorKBlock sig _≟X_
  using (module TKB6; module KBlockDisjoint)
import Categories.APROP.Hypergraph.Soundness.Decode.DecodeAttempt sig as DA
import Categories.APROP.Hypergraph.Soundness.Discharge.DecodeAttemptLinearP sig as DAL
import Categories.APROP.Hypergraph.Soundness.Discharge.Sub.StackUniqueReach sig as SUR

open import Data.Fin using (Fin; _↑ˡ_; _↑ʳ_; splitAt)
open import Data.Fin.Properties using (splitAt-↑ˡ; splitAt-↑ʳ)
import Data.Fin.Properties as FinP
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (yes; no)
open import Data.Maybe using (nothing)
open import Data.List using (List; []; _∷_; _++_; map)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.Product using (proj₁; proj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; cong₂; subst)
import Data.List.Relation.Binary.Permutation.Propositional as Perm
open Perm using (_↭_)

--------------------------------------------------------------------------------

module _
  (permˢ-K : ∀ (V : Set) (_≟V_ : DecidableEquality V) (vlab : V → X)
           → Support.PermK V vlab)
  where

  module _ {A B C D : ObjTerm} (f : HomTerm A B) (g : HomTerm C D) where
    private
      G K : Hypergraph FlatGen
      G = ⟪ f ⟫
      K = ⟪ g ⟫

      module Gd = Hypergraph G
      module Kd = Hypergraph K

    Hf : Hypergraph FlatGen
    Hf = ⟪ f ⊗₁ g ⟫

    private
      module Hfm = Hypergraph Hf

      open hTensor-impl G K using (injL; injR)
      open StrictDecoder Hf
        using (process-edgesˢ; stack-sepˢ; permuteˢ)
      open Run Hf using (stacks-agree)

      open import Data.Fin.Properties using () renaming (_≟_ to _≟F_)
      permˢ-K-fg : Support.PermK (Fin Hfm.nV) Hfm.vlab
      permˢ-K-fg = permˢ-K (Fin Hfm.nV) _≟F_ Hfm.vlab

      module Brd  = TB.Braid permˢ-K {A} {B} {C} {D} f g
      module Rec  = Brd.Reconcile-e
      module KBD  = KBlockDisjoint G K

      -- the K-block layout (definitionally Braid's private bindings).
      gblk kblk : List (Fin Hfm.nE)
      gblk = map (_↑ˡ Kd.nE) (range Gd.nE)
      kblk = map (Gd.nE ↑ʳ_) (range Kd.nE)

      Lpre Rsuf : List (Fin Hfm.nV)
      Lpre = map injL Gd.dom
      Rsuf = map injR Kd.dom

      sG aG : List (Fin Hfm.nV)
      sG = Rec.sGᴾ
      aG = Rec.aGᴾ

      ------------------------------------------------------------------
      -- ### G-block disjointness `block-disjoint gblk Rsuf` (mirror of
      -- `TensorBraid.Braid.g-disjoint` / `KBlockDisjoint` on the G-side:
      -- `injL k ≢ injR j`, so `injL k` is absent from any `injR`-block).

      injL≢injR : ∀ {k : Fin Gd.nV} {j : Fin Kd.nV} → injL k ≡ injR j → ⊥
      injL≢injR {k} {j} eq with trans (sym (splitAt-↑ˡ Gd.nV k Kd.nV))
                                (trans (cong (splitAt Gd.nV) eq)
                                       (splitAt-↑ʳ Gd.nV Kd.nV j))
      ... | ()

      injL∉injRs : ∀ (k : Fin Gd.nV) (ys : List (Fin Kd.nV))
                 → extract-elem (injL k) (map injR ys) ≡ nothing
      injL∉injRs k []       = refl
      injL∉injRs k (y ∷ ys) with injR y FinP.≟ injL k
      ... | yes p = ⊥-elim (injL≢injR (sym p))
      ... | no  _ rewrite injL∉injRs k ys = refl

      open hTensor-impl G K using (ein-c-inj₁-red)

      g-disjoint : StrictDecoder.block-disjoint Hf gblk Rsuf
      g-disjoint = all-gblk (range Gd.nE)
        where
          ein-disjointG
            : ∀ (eG : Fin Gd.nE)
            → All (λ k → extract-elem k Rsuf ≡ nothing) (Hfm.ein (eG ↑ˡ Kd.nE))
          ein-disjointG eG =
            subst (λ ks → All (λ k → extract-elem k Rsuf ≡ nothing) ks)
                  (sym (ein-c-inj₁-red eG))
                  (all-injL (Gd.ein eG))
            where
              all-injL : ∀ (ks : List (Fin Gd.nV))
                       → All (λ k → extract-elem k Rsuf ≡ nothing) (map injL ks)
              all-injL []       = []
              all-injL (k ∷ ks) = injL∉injRs k Kd.dom ∷ all-injL ks
          all-gblk : ∀ (es : List (Fin Gd.nE))
                   → All (λ e → StrictDecoder.ein-disjoint Hf e Rsuf)
                         (map (_↑ˡ Kd.nE) es)
          all-gblk []       = []
          all-gblk (e ∷ es) = ein-disjointG e ∷ all-gblk es

      -- `aG ≡ sG ++ Rsuf` (rebuilt `sep`; `Hf.dom = Lpre ++ Rsuf` definitional).
      sep : aG ≡ sG ++ Rsuf
      sep = stack-sepˢ gblk Lpre Rsuf g-disjoint

      ------------------------------------------------------------------
      -- ### K-block disjointness `All (ein-disjⁱ · sG) kblk`, transported
      -- from `kblock-ein-disjoint` (stated at `map injL s_G_final`) along
      -- `sG≡ : sG ≡ map injL s_G_final`.

      sG≡ : sG ≡ map injL Rec.s_G_final
      sG≡ = Rec.sG≡

      disj-kblk : All (λ e → All (λ k → extract-elem k sG ≡ nothing) (Hfm.ein e)) kblk
      disj-kblk = aux (range Kd.nE)
        where
          aux : ∀ (es : List (Fin Kd.nE))
              → All (λ e → All (λ k → extract-elem k sG ≡ nothing) (Hfm.ein e))
                    (map (Gd.nE ↑ʳ_) es)
          aux []       = []
          aux (e ∷ es) =
            subst (λ z → All (λ k → extract-elem k z ≡ nothing)
                             (Hfm.ein (Gd.nE ↑ʳ e)))
                  (sym sG≡)
                  (KBD.kblock-ein-disjoint e Rec.s_G_final)
            ∷ aux es

      ------------------------------------------------------------------
      -- ### The run-order reservoir `Reservoir≤1 Hf kblk aG`.
      -- Full-run reservoir from linearity (`dom-reservoir-prov` at the trivial
      -- `range ↭ range`), split at the `gblk ++ kblk` edge-range, bridged to
      -- the strict post-G stack `aG` by `stacks-agree`.

      range≡ : range Hfm.nE ≡ gblk ++ kblk
      range≡ = range-++ Gd.nE Kd.nE

      res-full : SUR.Reservoir≤1 Hf (range Hfm.nE) Hfm.dom
      res-full = SUR.dom-reservoir-prov Hf (proj₂ (DAL.⟪⟫-LinearP (f ⊗₁ g)))
                   (range Hfm.nE) Perm.↭-refl

      res-split : SUR.Reservoir≤1 Hf kblk ((process-edges Hf gblk Hfm.dom))
      res-split =
        SUR.reservoir-split Hf gblk kblk Hfm.dom
          (subst (λ z → SUR.Reservoir≤1 Hf z Hfm.dom) range≡ res-full)

      res-kblk : SUR.Reservoir≤1 Hf kblk aG
      res-kblk =
        subst (SUR.Reservoir≤1 Hf kblk) (sym (stacks-agree gblk Hfm.dom)) res-split

      ------------------------------------------------------------------
      -- ### The K-prepend braid `Br`, from `process-edges-↑ʳ-on-perm`.
      -- The actual mixed K-run stack `proj₁ (process-edgesˢ kblk aG)` ↭
      -- `sG ++ Kfin` (K-edge eouts prepend to the front).  Read off the
      -- term-free stack permutation at the identity input perm, bridged
      -- strict↔non-strict by `stacks-agree` and through `sG≡`/`Kfin≡`.

      -- input perm: `aG ↭ map injL s_G_final ++ map injR Kd.dom`
      aG↭std : aG Perm.↭ map (_↑ˡ Kd.nV) Rec.s_G_final ++ map (Gd.nV ↑ʳ_) Kd.dom
      aG↭std = Perm.↭-reflexive (trans sep (cong (_++ Rsuf) sG≡))

      Br↭-data = DA.process-edges-↑ʳ-on-perm G K (range Kd.nE) aG
                   Rec.s_G_final Kd.dom aG↭std

      -- `(process-edges Hf kblk aG) ↭ sG ++ Kfin`
      Kfin≡ : Rec.Kfinᴾ ≡ map injR Rec.s_K_final
      Kfin≡ = Rec.Kfin≡

      -- the C-level non-strict K-run final stack ≡ map injR (K-subrun stack).
      nsKfin≡ : (process-edges K (range Kd.nE) Kd.dom) ≡ Rec.s_K_final
      nsKfin≡ = sym (Run.stacks-agree K (range Kd.nE) Kd.dom)

      -- assemble Br : (sG ++ Kfin) ↭ proj₁ (process-edgesˢ kblk aG)
      Br : (sG ++ Rec.Kfinᴾ) Perm.↭ proj₁ (process-edgesˢ kblk aG)
      Br =
        -- bridge the strict run stack to the non-strict via `stacks-agree`;
        -- `Br↭-data` is now directly the term-free stack permutation.
        subst (sG ++ Rec.Kfinᴾ Perm.↭_)
              (sym (stacks-agree kblk aG))
              (Perm.↭-sym (subst (s' Perm.↭_) rhs≡ Br↭-data))
        where
          s' = process-edges Hf kblk aG

          -- the perm target `map injL s_G_final ++ map injR (K-subrun)` rewrites
          -- to `sG ++ Kfin` via `sG≡` (reversed) and `Kfin≡`/`nsKfin≡` (reversed).
          rhs≡ : map (_↑ˡ Kd.nV) Rec.s_G_final
                   ++ map (Gd.nV ↑ʳ_) ((process-edges K (range Kd.nE) Kd.dom))
                 ≡ sG ++ Rec.Kfinᴾ
          rhs≡ = cong₂ _++_ (sym sG≡) (trans (cong (map injR) nsKfin≡) (sym Kfin≡))

    ------------------------------------------------------------------
    -- ### The K-block factorization (the `KFacHyp` discharge), and the
    -- final ⊗-shape.

    private
      kfac
        : proj₂ (process-edgesˢ kblk aG)
          ≈ˢ permuteˢ Br ∘ˢ (Rec.KClnᴾ ∘ˢ permuteˢ Rec.pf₀ᴾ)
      kfac =
        TKB6.kblock-factorize-res Hf permˢ-K-fg sG kblk disj-kblk
          Rsuf aG Rec.pf₀ᴾ Br res-kblk

      kblockσ : Brd.KBlockσ
      kblockσ = Rec.KBlockσ-from-factorization Br kfac

    decodePˢ-⊗ : decodePˢ (f ⊗₁ g) ≈ˢ decodePˢ f ⊗ˢ decodePˢ g
    decodePˢ-⊗ = Brd.decodePˢ-⊗-cond kblockσ

--------------------------------------------------------------------------------
-- ## The UNCONDITIONAL ⊗-shape at the CONCRETE Kelly residual `PK.permˢ-K`
-- (axiom-free, discharged by `Strict.Perm.PermK` ⇐ `Strict.Braid`).  This has
-- the EXACT type of `PartI`'s / `Soundness`'s `decodePˢ-⊗` parameter, so
-- it closes the last residual of the strict soundness assembly.

import Categories.APROP.Hypergraph.Soundness.Strict.Perm.PermK sig _≟X_ as PK

decodePˢ-⊗-concrete
  : ∀ {A B C D} (f : HomTerm A B) (g : HomTerm C D)
  → decodePˢ (f ⊗₁ g) ≈ˢ decodePˢ f ⊗ˢ decodePˢ g
decodePˢ-⊗-concrete f g = decodePˢ-⊗ PK.permˢ-K f g
