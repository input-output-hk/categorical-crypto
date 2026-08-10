{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- Phase 8 — THE FINAL WIRING.  Closes the strict ⊗-shape
--
--     decodePˢ-⊗ : decodePˢ (f ⊗₁ g) ≈ˢ decodePˢ f ⊗ˢ decodePˢ g    (UNCOND.)
--
-- by supplying the LAST residual — the K-block braid `KBlockσ` of
-- `TensorBraid.Braid` — from THREE ALREADY-PROVEN THEOREMS, at a DERIVED braid
-- `Br` (`KBlockσ-from-factorization` quantifies `Br` universally, cancelling it
-- against `cand` by `pvv-inverse-leftˢ`, so any braid does):
--
--   1. EQUIVARIANCE (`StackEquiv.process-edges-equivariantˢ`) — conjugate the
--      K-block run from the actual post-G stack `aG` onto the BLOCK-SWAPPED
--      clean stack `Rsuf ++ sG`, along `ρ = sep ⨟ bswap sG Rsuf`;
--   2. RIGHT-frame SEPARABILITY (`Decoder.stack-sepˢ`/`term-sepᵛ`) — on
--      `Rsuf ++ sG` the inert G-output block `sG` is a SUFFIX, so the run there
--      is `Kclean ⊗ᵛ idᵛ {sG}`;
--   3. σ-CONJUGATION (`Restrict.box-conjᵛ` + `BlockSwapComm.block-swap-comm`) —
--      turn that right frame into the LEFT frame `KCln = idᵛ {sG} ⊗ᵛ Kclean`
--      that `Braid` consumes, with both σ-blocks realised as `permuteˢ (bswap …)`.
--
-- The right-factor mismatch (`pf'` vs `Braid`'s reflexive `pf₀ᴾ`) is closed by
-- one `perm-rigidˢ` on the `Unique` stack (`Reservoir≤1⇒Unique`).  Putting the
-- inert block on the RIGHT is what makes the frame clean: the naive LEFT-frame
-- separability is FALSE (fired outputs push in front of the untouched prefix),
-- which is why the reconciliation is by the final permute.
--
-- The two disjointness/freshness side conditions:
--   * `All (ein-disjⁱ · sG) kblk` from `KBlockDisjoint.kblock-ein-disjoint`;
--   * `Reservoir≤1 ⟪f⊗g⟫ kblk aG` from `dom-reservoir-prov` (⇐ linearity) +
--     `reservoir-split` at the `gblk ++ kblk` range split.
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

open import Categories.APROP.Hypergraph.Soundness.Decode.Decode sig
  using (extract-elem; process-edges)
open import Categories.APROP.Hypergraph.Soundness.Strict.Decode.Decode sig _≟X_
open import Categories.APROP.Hypergraph.Soundness.Strict.Perm.PermSupport sig _≟X_
open import Categories.APROP.Hypergraph.Soundness.Strict.Interchange.StackEquiv sig _≟X_
  using (module EquivStep)
import Categories.APROP.Hypergraph.Soundness.Strict.Interchange.BlockSwapComm sig _≟X_ as BSC
import Categories.APROP.Hypergraph.Soundness.Strict.Decode.DecodeSigma sig _≟X_ as DSS
import Categories.APROP.Hypergraph.Soundness.Strict.Tensor.TensorBraid sig _≟X_ as TB
open import Categories.APROP.Hypergraph.Soundness.Strict.Tensor.TensorKBlock sig _≟X_
  using (module KBlockDisjoint)
import Categories.APROP.Hypergraph.Soundness.Discharge.DecodeAttemptLinearP sig as DAL
import Categories.APROP.Hypergraph.Soundness.Stack.StackUnique sig as SU
import Categories.APROP.Hypergraph.Soundness.Stack.StackUniqueReach sig as SUR

open import Data.Fin using (Fin; _↑ˡ_; _↑ʳ_)
open import Data.Maybe using (nothing)
open import Data.List using (List; []; _∷_; _++_; map)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.Product using (proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)
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
        using (process-edgesˢ; permuteˢ; stack-sepˢ; term-sepᵛ; vl)
      open Restrict (Fin Hfm.nV) vl
        using ( HomV; idᵛ; _∘ᵛ_; _⊗ᵛ_; σᵛ; castᵛ; _≈ᵛ_; permuteᵛ
              ; cast-flipᵛ; cast-respᵛ; box-conjᵛ )
      open Run Hf using (stacks-agree)
      open EquivStep Hf using (process-edges-equivariantˢ)
      open DSS.Scr (Fin Hfm.nV) Hfm.vlab using (bswap)

      open import Data.Fin.Properties using () renaming (_≟_ to _≟F_)
      permˢ-K-fg : Support.PermK (Fin Hfm.nV) Hfm.vlab
      permˢ-K-fg = permˢ-K (Fin Hfm.nV) _≟F_ Hfm.vlab

      module Kmod = Support (Fin Hfm.nV) Hfm.vlab
      perm-rigidᴾ = Kmod.perm-rigidˢ permˢ-K-fg

      module Brd  = TB.Braid permˢ-K {A} {B} {C} {D} f g
      module Rec  = Brd.Reconcile-e
      module KBD  = KBlockDisjoint G K

      -- the K-block layout (definitionally Braid's private bindings).
      gblk kblk : List (Fin Hfm.nE)
      gblk = map (_↑ˡ Kd.nE) (range Gd.nE)
      kblk = map (Gd.nE ↑ʳ_) (range Kd.nE)

      Rsuf : List (Fin Hfm.nV)
      Rsuf = map injR Kd.dom

      sG aG : List (Fin Hfm.nV)
      sG = Rec.sGᴾ
      aG = Rec.aGᴾ

      -- `aG ≡ sG ++ Rsuf`: `Braid` already proves this from the G-block
      -- disjointness `KBD.gblock-disjoint` and `stack-sepˢ`.
      sep : aG ≡ sG ++ Rsuf
      sep = Rec.sepᴾ

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
      range≡ = Rec.range≡ᴾ

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
      -- ### The clean K-run pieces (`Braid`'s `Kfinᴾ`/`KClnᴾ`, definitionally).

      Kfin : List (Fin Hfm.nV)
      Kfin = proj₁ (process-edgesˢ kblk Rsuf)

      Kclean : HomV Rsuf Kfin
      Kclean = proj₂ (process-edgesˢ kblk Rsuf)

      ------------------------------------------------------------------
      -- ### (1) EQUIVARIANCE: conjugate the K-run from the actual stack `aG`
      -- onto the BLOCK-SWAPPED clean stack `Rsuf ++ sG`.

      ρ : aG ↭ Rsuf ++ sG
      ρ = Perm.trans (Perm.↭-reflexive sep) (bswap sG Rsuf)

      equiv = process-edges-equivariantˢ kblk {s = Rsuf ++ sG} {s' = aG} ρ res-kblk

      ρf : proj₁ (process-edgesˢ kblk aG) ↭ proj₁ (process-edgesˢ kblk (Rsuf ++ sG))
      ρf = proj₁ equiv

      equiv-eq
        : proj₂ (process-edgesˢ kblk aG)
          ≈ˢ permuteˢ (Perm.↭-sym ρf)
               ∘ˢ (proj₂ (process-edgesˢ kblk (Rsuf ++ sG)) ∘ˢ permuteˢ ρ)
      equiv-eq = proj₂ equiv

      ------------------------------------------------------------------
      -- ### (2) RIGHT-frame separability on the swapped stack, and (3) the
      -- σ-conjugation into the left-frame + permute-realised form, all kept
      -- HOMOGENEOUS under the single `castᵛ refl (sym sepK)`.

      sepK : proj₁ (process-edgesˢ kblk (Rsuf ++ sG)) ≡ Kfin ++ sG
      sepK = stack-sepˢ kblk Rsuf sG disj-kblk

      σ-in : permuteᵛ (bswap Rsuf sG) ≈ᵛ σᵛ Rsuf sG
      σ-in = BSC.block-swap-comm (Fin Hfm.nV) Hfm.vlab Rsuf sG

      σ-out : permuteᵛ (bswap sG Kfin) ≈ᵛ σᵛ sG Kfin
      σ-out = BSC.block-swap-comm (Fin Hfm.nV) Hfm.vlab sG Kfin

      -- W: the σ-conjugated clean form, with the σs realised as permutes.
      W : HomV (Rsuf ++ sG) (Kfin ++ sG)
      W = permuteᵛ (bswap sG Kfin) ∘ᵛ (Rec.KClnᴾ ∘ᵛ permuteᵛ (bswap Rsuf sG))

      mid-form
        : proj₂ (process-edgesˢ kblk (Rsuf ++ sG))
          ≈ˢ castᵛ refl (sym sepK) W
      mid-form =
        ≈-trans (cast-flipᵛ refl sepK (term-sepᵛ kblk Rsuf sG disj-kblk sepK))
          (cast-respᵛ refl (sym sepK)
            (≈-trans (box-conjᵛ Kclean sG)
              (∘-resp (≈-sym σ-out) (∘-resp ≈-refl (≈-sym σ-in)))))

      ------------------------------------------------------------------
      -- ### (4) absorb the separation cast into the equivariance permute, as a
      -- reflexive reindexing factor of the derivation.

      perm-cast-absorb
        : ∀ {as s s' ys : List (Fin Hfm.nV)}
            (eq : s ≡ s') (p : s' ↭ ys) (T : HomV as s)
        → permuteˢ p ∘ˢ castᵛ refl eq T
          ≈ˢ permuteˢ (Perm.trans (Perm.↭-reflexive eq) p) ∘ˢ T
      perm-cast-absorb refl p T = ≈-sym (∘-resp idʳ ≈-refl)

      ------------------------------------------------------------------
      -- ### (5) the derived braid + locating perm, and the rigidity that
      -- reconciles the derived `pf'` to `Braid`'s reflexive `pf₀ᴾ`.

      Br : (sG ++ Kfin) ↭ proj₁ (process-edgesˢ kblk aG)
      Br = Perm.trans (bswap sG Kfin)
             (Perm.trans (Perm.↭-reflexive (sym sepK)) (Perm.↭-sym ρf))

      pf' : aG ↭ sG ++ Rsuf
      pf' = Perm.trans ρ (bswap Rsuf sG)

      pf-rigid : permuteˢ pf' ≈ˢ permuteˢ Rec.pf₀ᴾ
      pf-rigid =
        perm-rigidᴾ
          (SU.Unique-resp-↭ (Perm.↭-reflexive sep)
            (SUR.Reservoir≤1⇒Unique Hf kblk aG res-kblk))
          pf' Rec.pf₀ᴾ

      -- pure homogeneous regrouping:
      --   (H ∘ (O ∘ (M ∘ I))) ∘ P  ≈ˢ  (H ∘ O) ∘ (M ∘ (I ∘ P))
      regroup
        : ∀ {o1 o2 o3 o4 o5 o6 : List X}
            {H : HomS o5 o6} {O : HomS o4 o5} {M : HomS o3 o4}
            {I : HomS o2 o3} {P : HomS o1 o2}
        → (H ∘ˢ (O ∘ˢ (M ∘ˢ I))) ∘ˢ P
          ≈ˢ (H ∘ˢ O) ∘ˢ (M ∘ˢ (I ∘ˢ P))
      regroup =
        ≈-trans (∘-resp (≈-sym assocˢ) ≈-refl)
        (≈-trans assocˢ (∘-resp ≈-refl assocˢ))

    ------------------------------------------------------------------
    -- ### The K-block factorization (the `KFacHyp` discharge), and the
    -- final ⊗-shape.

    private
      kfac
        : proj₂ (process-edgesˢ kblk aG)
          ≈ˢ permuteˢ Br ∘ˢ (Rec.KClnᴾ ∘ˢ permuteˢ Rec.pf₀ᴾ)
      kfac =
        ≈-trans equiv-eq
        (≈-trans (∘-resp ≈-refl (∘-resp mid-form ≈-refl))
        -- perm(↭-sym ρf) ∘ (castᵛ refl (sym sepK) W ∘ perm ρ)
        (≈-trans (≈-sym assocˢ)
        -- (perm(↭-sym ρf) ∘ castᵛ refl (sym sepK) W) ∘ perm ρ
        (≈-trans (∘-resp (perm-cast-absorb (sym sepK) (Perm.↭-sym ρf) W) ≈-refl)
        -- (perm(trans refl' (↭-sym ρf)) ∘ W) ∘ perm ρ
        (≈-trans regroup
        -- (perm … ∘ perm bswapOut) ∘ (KCln ∘ (perm bswapIn ∘ perm ρ))
          (∘-resp ≈-refl (∘-resp ≈-refl pf-rigid))))))

      kblockσ : Brd.KBlockσ
      kblockσ = Rec.KBlockσ-from-factorization Br kfac

    decodePˢ-⊗ : decodePˢ (f ⊗₁ g) ≈ˢ decodePˢ f ⊗ˢ decodePˢ g
    decodePˢ-⊗ = Brd.decodePˢ-⊗-cond kblockσ

--------------------------------------------------------------------------------
-- ## The UNCONDITIONAL ⊗-shape at the CONCRETE Kelly residual `PK.permˢ-K`
-- (axiom-free, discharged by `Strict.Perm.PermK` ⇐ `Strict.Perm.Braid`).  This has
-- the EXACT type of `PartI`'s / `Soundness`'s `decodePˢ-⊗` parameter, so
-- it closes the last residual of the strict soundness assembly.

import Categories.APROP.Hypergraph.Soundness.Strict.Perm.PermK sig _≟X_ as PK

decodePˢ-⊗-concrete
  : ∀ {A B C D} (f : HomTerm A B) (g : HomTerm C D)
  → decodePˢ (f ⊗₁ g) ≈ˢ decodePˢ f ⊗ˢ decodePˢ g
decodePˢ-⊗-concrete f g = decodePˢ-⊗ PK.permˢ-K f g
