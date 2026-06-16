{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- Discharge of `FireMidInterchangeˢ` — the STRICT both-fire two-edge
-- interchange core, building on the foundations of `Strict.FireMidS`
-- (`cross-NFˢ`, `box-resid3ˢ`) and the now-PROVEN keystone
-- `Strict.BlockSwapComm.block-swap-comm` (the σ-block identity that the two
-- located-input/located-output coherences `vin-cohˢ`/`vout-cohˢ` bottom out
-- in).
--
-- STATUS — PROVEN GREEN (postulate-free, --safe --without-K):
--
--   * `swap-block` / `swap-block-sym` — the `++⁺ʳ Rl`-framed block-swap
--     derivation `bswap L R` is, under `permuteˢ`, the strict block braiding
--     `σˢ (m L) (m R) ⊗ˢ idˢ{m Rl}` (both cast orientations).  Direct
--     corollary of `BlockSwapComm.block-swap-comm` + `permuteˢ-frame`.
--   * `Located` module: the per-pair located frames `Lin₁/Lin₂/Lout₁/Lout₂/Pr`
--     (cast to the `(A++A')++Rl` block shape `cross-NFˢ` expects), together
--     with the TWO coherences that feed `cross-NFˢ`:
--       - `vin-cohˢ  : Lin₁ ≈ˢ (σˢ A' A ⊗ˢ idˢ{Rl}) ∘ˢ Lin₂`
--       - `vout-cohˢ : Pr ∘ˢ Lout₁ ≈ˢ Lout₂ ∘ˢ (σˢ B B' ⊗ˢ idˢ{Rl})`
--     Both discharge via `perm-rigidˢ′` (the two block-located derivations
--     `loc₁` vs `trans loc₂ (bswap-frame)`, resp. `trans vout-loc₁ r-stk` vs
--     `trans (bswap-frame) vout-loc₂`, agree into the common `Unique`
--     codomain `us-sp`-image / `us-cod`) + `swap-block(-sym)`.  These are the
--     pieces the `FireMidS` obstruction map flagged as "now tractable via
--     bswap-σ", and they are the strict twins of `BVC.vin-coh`/`vout-coh`.
--
-- REMAINING OBSTRUCTION — `nf₁-eqˢ`/`nf₂-eqˢ` + the `cross-NFˢ` assembly into
-- `fire-mid-interchangeˢ`.  Each per-order located normal form
--   fire-termˢ′ b (eout a++s₁) s₂ q-second ∘ˢ fire-termˢ′ a sp s₁ q-first
--     ≈ˢ Lout ∘ˢ (((genˢ a ⊗ˢ genˢ b) ⊗ˢ idˢ{Rl}) ∘ˢ Lin)
-- is the strict twin of the non-strict `BlockNFNf2.block-bracket-pf` (a
-- generic single-order ~300-LOC chase, here REUSED for both orders).  The
-- residual `idˢ{m s₁}` of box `a` does NOT collapse into a cast — `s₁ ↭
-- ein b ++ R` is a PERMUTATION, so `box-resid3ˢ′` exposes a genuine
-- `permuteˢ (↭-sym ρ₁)` factor; box `b` is then slid onto the `ein b`-part
-- of that residual via `box-commute-ˢ`/`interchangeˢ`, after which ALL
-- permute factors (`q-first, q-second, ρ₁, ρ₂` + the relocation pre/post
-- permutes) merge into the two single `permuteˢ` frames `loc`/`vout-loc`,
-- reconciled by `perm-rigidˢ′` at the three `Unique` codomains
-- (`us-sp`-image / `us-mid` / `us-cod`).  This is the heaviest remaining
-- cast-bookkeeping (the prompt's own estimate: ~200–400 LOC/order); the
-- `≈ˢ`-content is all K-free except the final `perm-rigidˢ′` reconciliations.
-- Once `nf₁-eqˢ`/`nf₂-eqˢ` land, `fire-mid-interchangeˢ` is the 5-line
-- `cross-NFˢ′ … vin-cohˢ vout-cohˢ` assembly (mirroring the non-strict
-- `fire-mid-interchange`'s `collapse`/`goal`), and instantiating
-- `SwapCoreRun.RunInterchange` with it yields the UNCONDITIONAL
-- `run-interchange₀ˢ`.
--
-- TECHNIQUE: explicit fully-typed `private` lemmas (the method that
-- CONVERGED for `bswap-σ`); both-sides-to-cast-NF + `cast-irrel`/`cast-fuse`
-- under UIP.  Mirrors `Strict.Decoder.layer-sepˢ`/`term-sepˢ` and
-- `Strict.BlockSwapComm`.
--------------------------------------------------------------------------------

open import Categories.APROP
open import Relation.Binary using (DecidableEquality)

module Categories.APROP.Hypergraph.Soundness.Strict.FireMidS2
  (sig : APROPSignature)
  (_≟X_ : DecidableEquality (APROPSignature.X sig))
  where

open APROP sig using (X)

open import Categories.APROP.Hypergraph.Core using (Hypergraph)
open import Categories.APROP.Hypergraph.FromAPROP sig using (FlatGen)
open import Categories.APROP.Hypergraph.Soundness.Linearity sig using (Linear)

open import Categories.APROP.Hypergraph.Soundness.Discharge.EdgeDependency
  using (Dep)

open import Categories.APROP.Hypergraph.Soundness.Strict.Decoder sig _≟X_
open import Categories.APROP.Hypergraph.Soundness.Strict.PermSupport sig _≟X_
open import Categories.APROP.Hypergraph.Soundness.Strict.SwapCore sig _≟X_

import Categories.APROP.Hypergraph.Soundness.Strict.PermK sig _≟X_ as PK
import Categories.APROP.Hypergraph.Soundness.Strict.BlockSwapComm sig _≟X_ as BSC
import Categories.APROP.Hypergraph.Soundness.Strict.DecodeSigmaS sig _≟X_ as DSS

import Categories.APROP.Hypergraph.Soundness.Discharge.Sub.FireMidInterchangeComb sig
  as FMIC
import Categories.APROP.Hypergraph.Soundness.Discharge.Sub.StackUnique sig
  as SU

open import Data.Fin using (Fin)
open import Data.Fin.Properties using () renaming (_≟_ to _≟F_)
open import Data.List using (List; _++_; map)
open import Data.List.Properties using (map-++)
open import Data.List.Relation.Unary.Unique.Propositional using (Unique)
import Data.List.Relation.Binary.Permutation.Propositional as Perm
import Data.List.Relation.Binary.Permutation.Propositional.Properties as PermProp
open import Data.Product using (_,_; proj₁; proj₂)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong)

--------------------------------------------------------------------------------

module _ (H : Hypergraph FlatGen)
         (dih : ∀ {e} → ¬ (Dep H e e))
         (lin : Linear H)
         where
  private module H = Hypergraph H

  open StrictDecoder H

  permˢ-K : Support.PermK (Fin H.nV) vl
  permˢ-K = PK.permˢ-K (Fin H.nV) _≟F_ vl

  -- SwapCore brick aliases.
  Incompˢ      = Incomp H dih lin
  perm-rigidˢ′ = perm-rigidˢ H dih lin permˢ-K

  -- block-swap-comm at this hypergraph's vertex set.
  block-swap-comm = BSC.block-swap-comm (Fin H.nV) H.vlab
  open DSS.Scr (Fin H.nV) H.vlab using (bswap)

  private
    m : List (Fin H.nV) → List X
    m = map vl

  ------------------------------------------------------------------------
  -- A block-swap-comm corollary: the `++⁺ʳ Rl`-framed canonical block-swap
  -- derivation `bswap L R` is, under `permuteˢ`, the strict block braiding
  -- `σˢ (m L) (m R) ⊗ˢ idˢ{m Rl}` up to a `castˢ`.
  ------------------------------------------------------------------------

  private
    swap-block
      : ∀ (L R Rl : List (Fin H.nV))
      → permuteˢ (PermProp.++⁺ʳ Rl (bswap L R))
        ≈ˢ castˢ (trans (cong (_++ m Rl) (sym (map-++ vl L R)))
                        (sym (map-++ vl (L ++ R) Rl)))
                 (trans (cong (_++ m Rl) (sym (map-++ vl R L)))
                        (sym (map-++ vl (R ++ L) Rl)))
            (σˢ (m L) (m R) ⊗ˢ idˢ {m Rl})
    swap-block L R Rl =
      ≈-trans (cast-flip (map-++ vl (L ++ R) Rl) (map-++ vl (R ++ L) Rl)
                 (permuteˢ-frame Rl (bswap L R)))
        (≈-trans (cast-resp (sym (map-++ vl (L ++ R) Rl))
                            (sym (map-++ vl (R ++ L) Rl))
                   (≈-trans (⊗-resp (block-swap-comm L R) ≈-refl)
                     (≡⇒≈ˢ (cast-⊗ˡ (sym (map-++ vl L R)) (sym (map-++ vl R L))
                              (σˢ (m L) (m R))))))
          (≡⇒≈ˢ (cast-fuse (cong (_++ m Rl) (sym (map-++ vl L R)))
                           (sym (map-++ vl (L ++ R) Rl))
                           (cong (_++ m Rl) (sym (map-++ vl R L)))
                           (sym (map-++ vl (R ++ L) Rl))
                           (σˢ (m L) (m R) ⊗ˢ idˢ {m Rl}))))

    -- The flipped orientation (σˢ ≈ castˢ(...)(permuteˢ swp)), built from
    -- `swap-block` by re-casting and cancelling.
    swap-block-sym
      : ∀ (L R Rl : List (Fin H.nV))
      → σˢ (m L) (m R) ⊗ˢ idˢ {m Rl}
        ≈ˢ castˢ (trans (map-++ vl (L ++ R) Rl)
                        (cong (_++ m Rl) (map-++ vl L R)))
                 (trans (map-++ vl (R ++ L) Rl)
                        (cong (_++ m Rl) (map-++ vl R L)))
            (permuteˢ (PermProp.++⁺ʳ Rl (bswap L R)))
    swap-block-sym L R Rl =
      ≈-sym
        (≈-trans (cast-resp dom' cod' (swap-block L R Rl))
        (≈-trans (≡⇒≈ˢ (cast-fuse dom-i dom' cod-i cod'
                          (σˢ (m L) (m R) ⊗ˢ idˢ {m Rl})))
          (≡⇒≈ˢ (cast-irrel (trans dom-i dom') refl (trans cod-i cod') refl
                            (σˢ (m L) (m R) ⊗ˢ idˢ {m Rl})))))
      where
        dom-i = trans (cong (_++ m Rl) (sym (map-++ vl L R)))
                      (sym (map-++ vl (L ++ R) Rl))
        cod-i = trans (cong (_++ m Rl) (sym (map-++ vl R L)))
                      (sym (map-++ vl (R ++ L) Rl))
        dom' = trans (map-++ vl (L ++ R) Rl) (cong (_++ m Rl) (map-++ vl L R))
        cod' = trans (map-++ vl (R ++ L) Rl) (cong (_++ m Rl) (map-++ vl R L))

  ------------------------------------------------------------------------
  -- The per-pair located frames + coherences.  `SimLoc` (from FMIC) is
  -- opened, and `Lin₁/Lin₂/Lout₁/Lout₂/Pr` are the `permuteˢ`-of-located-
  -- derivation frames (cast to the `(A++A')++Rl` block shape `cross-NFˢ`
  -- expects).  `vin-cohˢ`/`vout-cohˢ` discharge the two `cross-NFˢ`
  -- hypotheses via `perm-rigidˢ′` + `swap-block`.
  ------------------------------------------------------------------------

  module Located
    {e e' : Fin H.nE} (inc : Incompˢ e e')
    (sp : List (Fin H.nV))
    (r₁  : List (Fin H.nV)) (p₁  : sp Perm.↭ H.ein e ++ r₁)
    (r₂  : List (Fin H.nV)) (p₂  : H.eout e ++ r₁ Perm.↭ H.ein e' ++ r₂)
    (r₂' : List (Fin H.nV)) (p₂' : sp Perm.↭ H.ein e' ++ r₂')
    (r₁' : List (Fin H.nV)) (p₁' : H.eout e' ++ r₂' Perm.↭ H.ein e ++ r₁')
    (us-sp : Unique sp)
    (us-cod : Unique (H.eout e ++ r₁'))
    where

    SL : FMIC.SimLoc H dih lin (proj₁ inc) (proj₂ inc)
                     sp r₁ p₁ r₂ p₂ r₂' p₂' r₁' p₁'
    SL = FMIC.sim-loc H dih lin (proj₁ inc) (proj₂ inc)
                      sp r₁ p₁ r₂ p₂ r₂' p₂' r₁' p₁'
    open FMIC.SimLoc SL

    -- Block-shape abbreviations (object level).
    A  = m (H.ein e)  ; A' = m (H.ein e')
    B  = m (H.eout e) ; B' = m (H.eout e')
    Rl = m Rlist

    -- Map-distribution casts: the located-derivation codomain
    -- `m((X ++ Y) ++ Rlist)` is `(m X ++ m Y) ++ Rl`.
    in-mc  : m ((H.ein e ++ H.ein e') ++ Rlist) ≡ (A ++ A') ++ Rl
    in-mc  = trans (map-++ vl (H.ein e ++ H.ein e') Rlist)
                   (cong (_++ Rl) (map-++ vl (H.ein e) (H.ein e')))
    in-mc' : m ((H.ein e' ++ H.ein e) ++ Rlist) ≡ (A' ++ A) ++ Rl
    in-mc' = trans (map-++ vl (H.ein e' ++ H.ein e) Rlist)
                   (cong (_++ Rl) (map-++ vl (H.ein e') (H.ein e)))
    out-mc  : m ((H.eout e ++ H.eout e') ++ Rlist) ≡ (B ++ B') ++ Rl
    out-mc  = trans (map-++ vl (H.eout e ++ H.eout e') Rlist)
                    (cong (_++ Rl) (map-++ vl (H.eout e) (H.eout e')))
    out-mc' : m ((H.eout e' ++ H.eout e) ++ Rlist) ≡ (B' ++ B) ++ Rl
    out-mc' = trans (map-++ vl (H.eout e' ++ H.eout e) Rlist)
                    (cong (_++ Rl) (map-++ vl (H.eout e') (H.eout e)))

    -- The located frames.
    Lin₁ : HomS (m sp) ((A ++ A') ++ Rl)
    Lin₁ = castˢ refl in-mc (permuteˢ loc₁)
    Lin₂ : HomS (m sp) ((A' ++ A) ++ Rl)
    Lin₂ = castˢ refl in-mc' (permuteˢ loc₂)
    Lout₁ : HomS ((B ++ B') ++ Rl) (m (H.eout e' ++ r₂))
    Lout₁ = castˢ out-mc refl (permuteˢ vout-loc₁)
    Lout₂ : HomS ((B' ++ B) ++ Rl) (m (H.eout e ++ r₁'))
    Lout₂ = castˢ out-mc' refl (permuteˢ vout-loc₂)
    Pr : HomS (m (H.eout e' ++ r₂)) (m (H.eout e ++ r₁'))
    Pr = permuteˢ r-stk

    --------------------------------------------------------------------
    -- vin-cohˢ : Lin₁ ≈ (σˢ A' A ⊗ˢ idˢ{Rl}) ∘ˢ Lin₂.
    --------------------------------------------------------------------

    private
      -- The block-swap derivation slotted after `loc₂`.
      swp-in : (H.ein e' ++ H.ein e) ++ Rlist Perm.↭ (H.ein e ++ H.ein e') ++ Rlist
      swp-in = PermProp.++⁺ʳ Rlist (bswap (H.ein e') (H.ein e))

      -- `loc₁` and `trans loc₂ swp-in` are two derivations into the SAME
      -- `Unique` codomain (`Unique-resp-↭ loc₁ us-sp`); identified by K.
      rigid-in : permuteˢ loc₁
                 ≈ˢ permuteˢ (Perm.trans loc₂ swp-in)
      rigid-in = perm-rigidˢ′ (SU.Unique-resp-↭ loc₁ us-sp)
                   loc₁ (Perm.trans loc₂ swp-in)

    private
      -- σˢ A' A ⊗ id ≈ castˢ Din Cin (permuteˢ swp-in), the flipped block-swap.
      Din = trans (map-++ vl (H.ein e' ++ H.ein e) Rlist)
                  (cong (_++ Rl) (map-++ vl (H.ein e') (H.ein e)))
      Cin = trans (map-++ vl (H.ein e ++ H.ein e') Rlist)
                  (cong (_++ Rl) (map-++ vl (H.ein e) (H.ein e')))

      σ-as-swp : σˢ A' A ⊗ˢ idˢ {Rl} ≈ˢ castˢ Din Cin (permuteˢ swp-in)
      σ-as-swp = swap-block-sym (H.ein e') (H.ein e) Rlist

    vin-cohˢ : Lin₁ ≈ˢ (σˢ A' A ⊗ˢ idˢ {Rl}) ∘ˢ Lin₂
    vin-cohˢ = ≈-sym
      (≈-trans (∘-resp σ-as-swp ≈-refl)
      (≈-trans (∘-resp ≈-refl (≡⇒≈ˢ (cast-irrel refl refl in-mc' Din
                                       (permuteˢ loc₂))))
      (≈-trans (≈-sym (∘-cast-split refl Din Cin
                         (permuteˢ swp-in) (permuteˢ loc₂)))
      (≈-trans (cast-resp refl Cin (≈-sym rigid-in))
        (≡⇒≈ˢ (cast-irrel refl refl Cin in-mc (permuteˢ loc₁)))))))

    --------------------------------------------------------------------
    -- vout-cohˢ : Pr ∘ˢ Lout₁ ≈ Lout₂ ∘ˢ (σˢ B B' ⊗ˢ idˢ{Rl}).
    --------------------------------------------------------------------

    private
      swp-out : (H.eout e ++ H.eout e') ++ Rlist Perm.↭ (H.eout e' ++ H.eout e) ++ Rlist
      swp-out = PermProp.++⁺ʳ Rlist (bswap (H.eout e) (H.eout e'))

      -- `trans vout-loc₁ r-stk` and `trans swp-out vout-loc₂` are two
      -- derivations into `Unique (eout e ++ r₁')` (`us-cod`).
      rigid-out : permuteˢ (Perm.trans vout-loc₁ r-stk)
                  ≈ˢ permuteˢ (Perm.trans swp-out vout-loc₂)
      rigid-out = perm-rigidˢ′ us-cod
                    (Perm.trans vout-loc₁ r-stk) (Perm.trans swp-out vout-loc₂)

      -- σˢ B B' ⊗ id ≈ castˢ Dout Cout (permuteˢ swp-out).
      Dout = trans (map-++ vl (H.eout e ++ H.eout e') Rlist)
                   (cong (_++ Rl) (map-++ vl (H.eout e) (H.eout e')))
      Cout = trans (map-++ vl (H.eout e' ++ H.eout e) Rlist)
                   (cong (_++ Rl) (map-++ vl (H.eout e') (H.eout e)))

      σ-as-swp-out : σˢ B B' ⊗ˢ idˢ {Rl} ≈ˢ castˢ Dout Cout (permuteˢ swp-out)
      σ-as-swp-out = swap-block-sym (H.eout e) (H.eout e') Rlist

    vout-cohˢ : Pr ∘ˢ Lout₁ ≈ˢ Lout₂ ∘ˢ (σˢ B B' ⊗ˢ idˢ {Rl})
    vout-cohˢ = ≈-sym
      (≈-trans (∘-resp ≈-refl σ-as-swp-out)
      (≈-trans (∘-resp ≈-refl (≡⇒≈ˢ (cast-irrel Dout Dout Cout out-mc'
                                       (permuteˢ swp-out))))
      (≈-trans (≈-sym (∘-cast-split Dout out-mc' refl
                         (permuteˢ vout-loc₂) (permuteˢ swp-out)))
      (≈-trans (cast-resp Dout refl (≈-sym rigid-out))
      (≈-trans (∘-cast-split Dout refl refl
                  (permuteˢ r-stk) (permuteˢ vout-loc₁))
        (∘-resp ≈-refl
          (≡⇒≈ˢ (cast-irrel Dout out-mc refl refl (permuteˢ vout-loc₁)))))))))
