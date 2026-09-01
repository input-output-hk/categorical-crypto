{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- The σ-SHAPE of the strict decoder `decodePˢ`.
--
--   decodePˢ-σ : decodePˢ (σ {A}{B}) ≈ˢ σˢ (flatten A) (flatten B)
--
-- `⟪ σ {A}{B} ⟫ = hSwap A B` has `nE` LITERALLY `0`, so the run reduces to
-- `idˢ` and `decodePˢ σ` to `castˢ (boundary) (permuteˢ (finalPermˢ σ))` — with
-- no stack equality to transport along.  And `finalPermˢ σ` reduces in turn to
-- the CANONICAL block-swap derivation `bswap Lblk Rblk`, because that is how
-- `DecodeAttempt.decode-attempt-hSwap` (which `decode-attempt-LinearP`'s
-- `q-swap` branch IS) is spelled.  So this shape pays no rigidity at all; what
-- is left is `permuteˢ (bswap Lblk Rblk) ≈ σˢ`.
--
-- That last fact — the strict vertex-level block-swap-commutes keystone,
-- whose two inductive steps carry the hexagon-reconciliation content — is
-- `Strict/Interchange/BlockSwapComm.block-swap-comm`, taken directly.
--------------------------------------------------------------------------------

open import Categories.APROP
open import Relation.Binary using (DecidableEquality)

module Categories.APROP.Hypergraph.Soundness.Strict.Decode.DecodeSigma
  (sig : APROPSignature)
  (_≟X_ : DecidableEquality (APROPSignature.X sig))
  where

open APROP sig

open import Categories.APROP.Hypergraph.Model.Core using (Hypergraph)
open import Categories.APROP.Hypergraph.Model.FromAPROP sig
  using (flatten; module hGenSwap-impl)
open import Categories.APROP.Hypergraph.Model.Translation sig using (⟪_⟫; ⟪⟫-domL; ⟪⟫-codL)

open import Categories.APROP.Hypergraph.Soundness.Strict.Decode.Decode sig _≟X_
import Categories.APROP.Hypergraph.Soundness.Strict.Decode.DecodeShapes sig _≟X_
  as DShapes
import Categories.APROP.Hypergraph.Soundness.Strict.Interchange.BlockSwapComm sig _≟X_
  as BSC

open import Data.Fin using (Fin)
open Perm using (_↭_)

--------------------------------------------------------------------------------
-- The σ-shape, assembled from `BlockSwapComm.block-swap-comm` (the block-swap
-- keystone) alone: the `nE = 0` collapse is definitional.

module Sigma (A B : ObjTerm) where
  private
    f : HomTerm (A ⊗₀ B) (B ⊗₀ A)
    f = σ {A} {B}

    module RF = Run ⟪ f ⟫
    module Hf = Hypergraph ⟪ f ⟫
    open Restrict (Fin Hf.nV) Hf.vlab using (_∘ᵛ_; σᵛ; _≈ᵛ_; σᵛ-≈̂)

    -- The hSwap blocks and their vertex-label evaluations, taken from the
    -- constructor's own `where`-module: `⟪ σ ⟫ = hSwap A B`, so `Hf.vlab` IS
    -- `hGenSwap-impl`'s `vlab-c` and `Hf.dom = Lblk ++ Rblk`,
    -- `Hf.cod = Rblk ++ Lblk` hold definitionally.
    open hGenSwap-impl A B using (Lblk; Rblk; lem-L; lem-R)
    open DShapes.Scr (Fin Hf.nV) Hf.vlab using (bswap)

    -- the canonical derivation `dom ↭ cod`.  `finalPermˢ f` REDUCES to it:
    -- `⟪ σ ⟫ = hSwap A B`, so `decode-attempt-LinearP` takes its `q-swap`
    -- branch, and `decode-attempt-hSwap` is spelled as `bswap`.
    bsw : Hf.dom ↭ Hf.cod
    bsw = bswap Lblk Rblk

  -- the block-swap identity at the hSwap blocks (the residual `bswap-σ`),
  -- V-level: `Hf.dom = Lblk ++ Rblk` and `Hf.cod = Rblk ++ Lblk` hold
  -- definitionally, so the braiding needs no frame cast.
  σ-block-≈ : RF.permuteˢ bsw ≈ᵛ σᵛ Lblk Rblk
  σ-block-≈ = BSC.block-swap-comm (Fin Hf.nV) Hf.vlab Lblk Rblk

  -- the inner term `permuteˢ (finalPermˢ σ) ∘ᵛ proj₂ runˢ` IS the block
  -- braiding, on the nose: `Hf.nE` is literally `0`, so the run reduces to
  -- `idᵛ` with no stack-equality to transport along, and `finalPermˢ f`
  -- reduces to `bsw`.  Only the unit law is left to say.
  inner≈ : RF.permuteˢ (finalPermˢ f) ∘ᵛ proj₂ RF.runˢ ≈ᵛ σᵛ Lblk Rblk
  inner≈ = ≈-trans idʳ σ-block-≈

  -- the full σ-shape.  `decodePˢ f` IS `castˢ (⟪⟫-domL f) (⟪⟫-codL f) inner`
  -- and every remaining endpoint mismatch is a cast the `≈̂` layer carries:
  -- `σᵛ-≈̂` peels `σᵛ`'s own `map-++` frame, `σ-≈̂` re-indexes the braiding
  -- from the hSwap blocks to `flatten A`/`flatten B`, and `≈̂⇒castˢ` re-pins
  -- the boundary.  (The former `cast-fuse`/`cast-irrel` pair and its
  -- refl-matching `where` worker are exactly what that absorbs.)
  decodePˢ-σ : decodePˢ f ≈ˢ σˢ (flatten A) (flatten B)
  decodePˢ-σ =
    ≈̂⇒castˢ
      (≈̂-trans (≈ˢ⇒≈̂ inner≈)
               (≈̂-trans (σᵛ-≈̂ Lblk Rblk) (σ-≈̂ lem-L lem-R)))
      (⟪⟫-domL f) (⟪⟫-codL f)

--------------------------------------------------------------------------------
-- The σ-shape rests on the block-swap keystone `BlockSwapComm.block-swap-comm`
-- (whose `[]` base is `DecodeShapes.Scr.bswap-σ-base`; the `(v ∷ L)` step is
-- the σ-hexˢ reconciliation) — `finalPermˢ σ` already IS `bswap`, so the
-- keystone plus one unit law gives `decodePˢ (σ {A}{B}) ≈ σˢ (flatten A) (flatten B)`.
--------------------------------------------------------------------------------
