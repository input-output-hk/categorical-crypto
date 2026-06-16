{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- Discharge of the `FireMidInterchangeˢ` residual of `Strict.SwapCoreRun` —
-- the STRICT both-fire two-edge interchange core.
--
-- Strict twin of `Discharge/Sub/FireMidInterchange.fire-mid-interchange`.
-- The combinatorial heart (`SimLoc`: a shared residual `Rlist`, the two
-- block-located input/output permutes `loc₁/loc₂`, `vout-loc₁/₂`, the
-- output reshuffle `r-stk`) is REUSED AS-IS from `FireMidInterchangeComb`.
--
-- In the strict SMC `S` (`FreeStrictSMC.Build` at `FlatGen`), `⊗ˢ = ++` on
-- the nose, so the non-strict `BlockNF` view frames `view-in≅`/`view-out≅`
-- (the `unflatten-++-≅` Mac-Lane conjugations) become the UIP-trivial
-- `castˢ` kit, and the both-box commutation is the located `box-crossˢ`.
--
-- Each firing order's two-fire composite is driven into the LOCATED normal
-- form
--   castˢ(O) (permuteˢ vout-locᵢ)
--     ∘ˢ castˢ(M) ((genˢ e ⊗ˢ genˢ e') ⊗ˢ idˢ{Rlist})
--     ∘ˢ castˢ(I) (permuteˢ locᵢ)
-- via `relocate-box` (= `box-residual-split`) on each box (exposing the
-- shared `Rlist`), then the two orders are related by `box-crossˢ`, with
-- the locating permutes reconciled by `perm-rigidˢ` against the SimLoc-chosen
-- derivations into the `Unique` mid/cod stacks.
--
-- STATUS (this file): the two REUSABLE, K-free cores are proven green:
--
--   * `cross-NFˢ` — the abstract located-interchange N-core.  Given two
--     boxes side by side over a residual, the two firing orders' located
--     normal forms (`Lout₂ ∘ (((g' ⊗ g) ⊗ id) ∘ Lin₂)` and
--     `Lout₁ ∘ (((g ⊗ g') ⊗ id) ∘ Lin₁)`), modulo the two strict coherence
--     equations `vin-cohˢ`/`vout-cohˢ`, are equal up to the reshuffle `Pr`.
--     This is the strict twin of `FireMidInterchange`'s `collapse`/`goal`
--     and the consumer of `box-crossˢ`.
--   * `box-resid3ˢ` — the three-factor residual relocation of a single fire
--     box: `genˢ e ⊗ idˢ{m rest} ≈ (id ⊗ permuteˢ(↭-sym q)) ∘ ((genˢ e ⊗
--     idˢ{m (C ++ Rl)}) ∘ (id ⊗ permuteˢ q))`, exposing the relocated box.
--
-- REMAINING OBSTRUCTION — the two single-order located normal forms
-- (`nf₁-eqˢ`, `nf₂-eqˢ`) and the two strict coherences (`vin-cohˢ`,
-- `vout-cohˢ`) that feed `cross-NFˢ`.  Concretely:
--
--   nf₁-eqˢ :  fire-termˢ′ e' (eout e ++ r₁) r₂ p₂ ∘ˢ fire-termˢ′ e sp r₁ p₁
--              ≈ˢ castˢ(O₁) (permuteˢ vout-loc₁)
--                   ∘ˢ ( castˢ(M₁) ((genˢ (elab e) ⊗ˢ genˢ (elab e'))
--                                     ⊗ˢ idˢ{m Rlist})
--                          ∘ˢ castˢ(I₁) (permuteˢ loc₁) )
--   (and its `e'`-first mirror).  This is the strict twin of the non-strict
--   `BlockNFNf2.nf-bracket-proof` chase; in the strict SMC the view-frame
--   isos are `castˢ`, so the chase reduces to: expand both `fire-termˢ′`
--   (two `map-++` casts each), relocate both residuals by `box-resid3ˢ`
--   (`q₁ : r₁ ↭ ein e' ++ Rlist` from `extract-ein'`; `q₂ : r₂ ↭ eout e ++
--   Rlist` from `eout-residual`), slide `genˢ (elab e')` past T1's residual
--   via `box-commute-ˢ`/`interchangeˢ` to bring the two boxes side by side,
--   and merge ALL permute factors (`p₁,p₂,q₁,q₂` + the box-resid3ˢ pre/post
--   relocations) into the two single `permuteˢ` frames, reconciled to
--   `loc₁`/`vout-loc₁` by `perm-rigidˢ′` (into `Unique-resp-↭`-derived
--   `Unique` codomains from `us-sp`/`us-cod`).  This is ~200-400 LOC of
--   explicit `castˢ`-threading per order (the cast-bookkeeping the prior
--   agent stopped at); the `≈ˢ`-content is all K-free except the final
--   `perm-rigidˢ′` reconciliations.  `vin-cohˢ`/`vout-cohˢ` are pure
--   `perm-rigidˢ′` facts (the strict braid `σˢ (m A') (m A)` equals
--   `permuteˢ` of the block-swap derivation; non-strict twin: `BVC.vin-coh`/
--   `vout-coh` via `coh-in`/`coh-out`).
--------------------------------------------------------------------------------

open import Categories.APROP
open import Relation.Binary using (DecidableEquality)

module Categories.APROP.Hypergraph.Soundness.Strict.FireMidS
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

open import Data.Fin using (Fin)
open import Data.Fin.Properties using () renaming (_≟_ to _≟F_)
open import Data.List using (List; _++_; map)
import Data.List.Relation.Binary.Permutation.Propositional as Perm
open import Relation.Nullary using (¬_)

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
  box-crossˢ′  = box-crossˢ H dih lin permˢ-K
  perm-invˡ′   = permuteˢ-inv-left H dih lin permˢ-K

  ------------------------------------------------------------------------
  -- THE ABSTRACT LOCATED-INTERCHANGE CORE (the genuine N-content).
  --
  -- Two boxes `g , g'` sitting side by side over a residual `R`, located by
  -- the two firing orders' input frames `Lin₁ / Lin₂` and output frames
  -- `Lout₁ / Lout₂`, with the reshuffle `Pr` between the two codomains.
  -- Given the two strict coherence equations
  --     vin-cohˢ  : Lin₁ ≈ˢ (σ ⊗ˢ id) ∘ˢ Lin₂
  --     vout-cohˢ : Pr ∘ˢ Lout₁ ≈ˢ Lout₂ ∘ˢ (σ ⊗ˢ id)
  -- the two located composites are equal up to `Pr`.  This is the strict
  -- twin of `FireMidInterchange.fire-mid-interchange`'s `collapse`/`goal`
  -- algebra: K-FREE, the σ-swap provided by `box-crossˢ`.
  ------------------------------------------------------------------------

  cross-NFˢ
    : ∀ {A B A' B' Rl : List X} {sp Cod₁ Cod₂ : List X}
        (g : HomS A B) (g' : HomS A' B')
        (Lin₁  : HomS sp ((A ++ A') ++ Rl))
        (Lin₂  : HomS sp ((A' ++ A) ++ Rl))
        (Lout₁ : HomS ((B ++ B') ++ Rl) Cod₁)
        (Lout₂ : HomS ((B' ++ B) ++ Rl) Cod₂)
        (Pr    : HomS Cod₁ Cod₂)
      → Lin₁ ≈ˢ (σˢ A' A ⊗ˢ idˢ {Rl}) ∘ˢ Lin₂
      → Pr ∘ˢ Lout₁ ≈ˢ Lout₂ ∘ˢ (σˢ B B' ⊗ˢ idˢ {Rl})
      → ( Lout₂ ∘ˢ (((g' ⊗ˢ g) ⊗ˢ idˢ {Rl}) ∘ˢ Lin₂) )
        ≈ˢ Pr ∘ˢ ( Lout₁ ∘ˢ (((g ⊗ˢ g') ⊗ˢ idˢ {Rl}) ∘ˢ Lin₁) )
  cross-NFˢ {A} {B} {A'} {B'} {Rl} g g' Lin₁ Lin₂ Lout₁ Lout₂ Pr vinc voutc =
    -- core-swap : (g' ⊗ˢ g) ⊗ˢ id ≈ Sout ∘ ((g ⊗ˢ g') ⊗ˢ id) ∘ Sin
    -- with Sin = σ A' A ⊗ˢ id, Sout = σ B B' ⊗ˢ id (from `box-crossˢ`).
    -- (0) rewrite the box block by box-crossˢ:
    --     (g' ⊗ g) ⊗ id  ≈  (Sout ∘ C) ∘ Sin
    --   with C = (g ⊗ g') ⊗ id, Sin = σ A' A ⊗ id, Sout = σ B B' ⊗ id.
    ≈-trans (∘-resp ≈-refl (∘-resp (box-crossˢ′ g g' Rl) ≈-refl))
    -- LHS now: Lout₂ ∘ ((((Sout ∘ C) ∘ Sin)) ∘ Lin₂)
    -- (1) reassociate the inner block to  Sout ∘ (C ∘ (Sin ∘ Lin₂))
    (≈-trans (∘-resp ≈-refl assocˢ)
    -- Lout₂ ∘ ((Sout ∘ C) ∘ (Sin ∘ Lin₂))
    (≈-trans (∘-resp ≈-refl assocˢ)
    -- Lout₂ ∘ (Sout ∘ (C ∘ (Sin ∘ Lin₂)))
    (≈-trans (∘-resp ≈-refl (∘-resp ≈-refl (∘-resp ≈-refl (≈-sym vinc))))
    -- (2) Sin ∘ Lin₂ ≈ Lin₁  (vinc) :  Lout₂ ∘ (Sout ∘ (C ∘ Lin₁))
    (≈-trans (≈-sym assocˢ)
    -- (Lout₂ ∘ Sout) ∘ (C ∘ Lin₁)
    (≈-trans (∘-resp (≈-sym voutc) ≈-refl)
    -- (Pr ∘ Lout₁) ∘ (C ∘ Lin₁)
      assocˢ)))))

  ------------------------------------------------------------------------
  -- THREE-FACTOR RESIDUAL RELOCATION of a fire box.  The residual identity
  -- `idˢ{m rest}` is conjugated by a relocation `q : rest ↭ C ++ Rl` into a
  -- pre-box permute, the relocated box `genˢ ⊗ˢ idˢ{m (C ++ Rl)}`, and a
  -- post-box permute:
  --   genˢ e ⊗ˢ idˢ{m rest}
  --     ≈ˢ (idˢ{m B} ⊗ˢ permuteˢ (↭-sym q))
  --          ∘ˢ ( (genˢ e ⊗ˢ idˢ{m (C ++ Rl)}) ∘ˢ (idˢ{m A} ⊗ˢ permuteˢ q) )
  -- K-FREE (interchange + `perm-invˡ′`).
  ------------------------------------------------------------------------

  box-resid3ˢ
    : ∀ (e : Fin H.nE) {rest C Rl : List (Fin H.nV)}
        (q : rest Perm.↭ C ++ Rl)
    → genˢ (H.elab e) ⊗ˢ idˢ {map vl rest}
      ≈ˢ (idˢ {map vl (H.eout e)} ⊗ˢ permuteˢ (Perm.↭-sym q))
           ∘ˢ ( (genˢ (H.elab e) ⊗ˢ idˢ {map vl (C ++ Rl)})
                  ∘ˢ (idˢ {map vl (H.ein e)} ⊗ˢ permuteˢ q) )
  box-resid3ˢ e {rest} {C} {Rl} q =
    ≈-trans (⊗-resp (≈-sym idˡ) (≈-sym (perm-invˡ′ q)))
    -- genˢ ⊗ (permuteˢ(↭q) ∘ permuteˢ q)  with genˢ = idˢ ∘ genˢ
    (≈-trans (≈-sym interchangeˢ)
    -- (idˢ ⊗ permuteˢ(↭q)) ∘ (genˢ ⊗ permuteˢ q)
    (∘-resp ≈-refl
      (≈-trans (⊗-resp (≈-sym idʳ) (≈-sym idˡ))
        (≈-sym interchangeˢ))))
