{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- The σ-SHAPE of the strict decoder `decodePˢ`.
--
--   decodePˢ-σ : decodePˢ (σ {A}{B}) ≈ˢ σˢ (flatten A) (flatten B)
--
-- `⟪ σ {A}{B} ⟫ = hSwap A B` has `nE ≡ 0`, so (exactly as in
-- `DecodeShapes.Atom`) the run collapses to `idˢ` and `decodePˢ σ` reduces to
-- `castˢ (boundary) (permuteˢ (finalPermˢ σ))`.  `finalPermˢ σ` is a derivation
-- `dom(hSwap) ↭ cod(hSwap)` into the `Unique` codomain `cod`; via `rigidˢ`
-- it is identified with the CANONICAL block-swap derivation `bswap Lblk Rblk`
-- (`DecodeShapes.Scr`), whose `permuteˢ` is the strict block braiding `σˢ`.
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
  using (flatten; range; module hGenSwap-impl)
open import Categories.APROP.Hypergraph.Model.Translation sig using (⟪_⟫; ⟪⟫-domL; ⟪⟫-codL)
open import Categories.APROP.Hypergraph.Soundness.Stack.StackUnique
  sig using (⟪⟫-cod-Unique)

open import Categories.APROP.Hypergraph.Soundness.Strict.Decode.Decode sig _≟X_
import Categories.APROP.Hypergraph.Soundness.Strict.Decode.DecodeShapes sig _≟X_
  as DShapes
import Categories.APROP.Hypergraph.Soundness.Strict.Interchange.BlockSwapComm sig _≟X_
  as BSC

open import Data.Fin using (Fin; _↑ˡ_; _↑ʳ_)
open import Data.List.Properties using (++-identityʳ)
open Perm using (_↭_)

--------------------------------------------------------------------------------
-- The σ-shape, assembled from `BlockSwapComm.block-swap-comm` (the block-swap
-- keystone) via the `nE ≡ 0` collapse and `rigidˢ`.

module Sigma (A B : ObjTerm) where
  private
    f : HomTerm (A ⊗₀ B) (B ⊗₀ A)
    f = σ {A} {B}

    module RF = Run ⟪ f ⟫
    module Hf = Hypergraph ⟪ f ⟫
    open Restrict (Fin Hf.nV) Hf.vlab
      using (idᵛ; _∘ᵛ_; σᵛ; castᵛ; _≈ᵛ_; permuteᵛ; permuteᵛ-subst-dom
            ; ∘-castᵛ; subst-codᵛ; σᵛ-≈̂)

    rigidˢ = RF.rigidˢ

    nE≡0 : Hf.nE ≡ 0
    nE≡0 = refl

    collapse = DShapes.nE0-run ⟪ f ⟫ nE≡0
    s≡ : RF.s-finˢ ≡ Hf.dom
    s≡ = proj₁ collapse

    -- the canonical block-swap derivation, on the hSwap blocks.
    Lblk Rblk : List (Fin Hf.nV)
    Lblk = map (_↑ˡ length (flatten B)) (range (length (flatten A)))
    Rblk = map (length (flatten A) ↑ʳ_) (range (length (flatten B)))

    -- `Hf.dom = Lblk ++ Rblk`, `Hf.cod = Rblk ++ Lblk` (definitional).

    -- per-block vertex-label evaluations: `Hf.vlab` IS `hGenSwap-impl`'s
    -- `vlab-c` (`⟪ σ ⟫ = hSwap A B`), so its own `lem-L`/`lem-R` apply.
    open hGenSwap-impl A B using (lem-L; lem-R)

    -- the canonical derivation `dom ↭ cod`.
    bsw : Hf.dom ↭ Hf.cod
    bsw = DShapes.Scr.bswap (Fin Hf.nV) Hf.vlab Lblk Rblk

    -- the algorithm's final permutation equals `bsw` under `permuteˢ`,
    -- by `perm-rigidˢ` into the `Unique` codomain (exactly where the
    -- non-strict proof invokes K-faithfulness).
    perm≈ : RF.permuteˢ (finalPermˢ f)
            ≈ˢ RF.permuteˢ (subst (Perm._↭ Hf.cod) (sym s≡) bsw)
    perm≈ = rigidˢ (⟪⟫-cod-Unique f) (finalPermˢ f)
              (subst (Perm._↭ Hf.cod) (sym s≡) bsw)

  -- the block-swap identity at the hSwap blocks (the residual `bswap-σ`),
  -- V-level: `Hf.dom = Lblk ++ Rblk` and `Hf.cod = Rblk ++ Lblk` hold
  -- definitionally, so the braiding needs no frame cast.
  σ-block-≈ : RF.permuteˢ bsw ≈ᵛ σᵛ Lblk Rblk
  σ-block-≈ = BSC.block-swap-comm (Fin Hf.nV) Hf.vlab Lblk Rblk

  private
    -- the run collapses to `coe` of the stack-equality (nE ≡ 0).
    run≡ : proj₂ RF.runˢ ≡ castᵛ refl (sym s≡) (idᵛ {Hf.dom})
    run≡ = trans (proj₂ collapse) (subst-codᵛ (sym s≡) idᵛ)

    -- `permuteᵛ` of the `s≡`-substituted canonical derivation is a `castᵛ`
    -- of `permuteᵛ bsw`.
    permsub≡ : RF.permuteˢ (subst (Perm._↭ Hf.cod) (sym s≡) bsw)
               ≡ castᵛ (sym s≡) refl (permuteᵛ bsw)
    permsub≡ = permuteᵛ-subst-dom (sym s≡) bsw

  -- the inner term `permuteˢ (finalPermˢ σ) ∘ᵛ proj₂ runˢ` IS the block
  -- braiding: the two `s≡` transports meet at the collapsed run and cancel.
  inner≈ : RF.permuteˢ (finalPermˢ f) ∘ᵛ proj₂ RF.runˢ ≈ᵛ σᵛ Lblk Rblk
  inner≈ =
    ≈-trans (∘-resp (≈-trans perm≈ (≡⇒≈ˢ permsub≡)) (≡⇒≈ˢ run≡))
    (≈-trans (∘-castᵛ refl (sym s≡) refl (permuteᵛ bsw) idᵛ)
      (≈-trans idʳ σ-block-≈))

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
-- the σ-hexˢ reconciliation).  Fed with `rigidˢ` it collapses `finalPermˢ σ`
-- onto `bswap`, giving `decodePˢ (σ {A}{B}) ≈ σˢ (flatten A) (flatten B)`.
--------------------------------------------------------------------------------
