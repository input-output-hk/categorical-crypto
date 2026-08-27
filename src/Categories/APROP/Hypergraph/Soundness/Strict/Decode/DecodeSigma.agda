{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- The σ-SHAPE of the strict decoder `decodePˢ`.
--
--   decodePˢ-σ : decodePˢ (σ {A}{B}) ≈ˢ σˢ (flatten A) (flatten B)
--
-- `⟪ σ {A}{B} ⟫ = hSwap A B` has `nE ≡ 0`, so (exactly as in
-- `DecodeShapes.Atom`) the run collapses to `idˢ` and `decodePˢ σ` reduces to
-- `castˢ (boundary) (permuteˢ (finalPermˢ σ))`.  `finalPermˢ σ` is a derivation
-- `dom(hSwap) ↭ cod(hSwap)` into the `Unique` codomain `cod`; via `perm-rigidˢ`
-- it is identified with the CANONICAL block-swap derivation `bswap Lblk Rblk`,
-- whose `permuteˢ` is the strict block braiding `σˢ` (`bswap-σ` below).
--
-- The two inductive steps `bswap-σ (v ∷ L)` / `permuteˢ-shift-sym v (x∷R)`
-- (the hexagon-reconciliation content) are reduced to the single clearly-typed
-- `≈ˢ` fact `bswap-σ` (`Scr.BswapSig`), threaded as a module parameter and
-- discharged in `Strict/Interchange/BlockSwapComm.agda`.  The
-- strict vertex-level block-swap-commutes keystone.
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
import Categories.APROP.Hypergraph.Soundness.Strict.Perm.PermK sig _≟X_ as PK

open import Data.Fin using (Fin; _↑ˡ_; _↑ʳ_)
open import Data.Fin.Properties using () renaming (_≟_ to _≟F_)
open import Data.List using (List; []; _∷_; _++_; map; length)
open import Data.List.Properties using (++-identityʳ)
open import Data.Product using (proj₁; proj₂)
import Data.List.Relation.Binary.Permutation.Propositional as Perm
open Perm using (_↭_)
import Data.List.Relation.Binary.Permutation.Propositional.Properties as PermProp

--------------------------------------------------------------------------------
-- The canonical block-swap derivation + its `permuteˢ ≈ σˢ` identity (the
-- vertex-level keystone).  Recursion on the LEFT block.

module Scr (V : Set) (vlab : V → X) where
  open PK.Support V vlab public
  open DShapes.Trivial V vlab public
  open Restrict V vlab
    using (idᵛ; _⊗ᵛ_; σᵛ; _≈ᵛ_; permuteᵛ; castᵛ-cast; σ-unitᵛ)

  bswap : (L R : List V) → (L ++ R) ↭ (R ++ L)
  bswap []      R = Perm.↭-reflexive (sym (++-identityʳ R))
  bswap (v ∷ L) R = Perm.trans (Perm.prep v (bswap L R)) (Perm.↭-sym (PermProp.shift v R L))

  -- `permuteᵛ (↭-sym (shift v R L))` is the braiding of `v ∷ []` past the
  -- block `R`, framed by `idᵛ {L}` — stated in the `Restrict` layer, so the
  -- former `mdom`/`mcod` map-distribution endpoints are gone.  BASE proven
  -- here (both sides reduce to `idˢ`); the `(x ∷ R)` step is the `σ-hexˢʳ`
  -- reconciliation `Interchange.BlockSwapComm.shift-symᵛ`.
  permuteˢ-shift-sym-base
    : (v : V) (L : List V)
    → permuteᵛ (Perm.↭-sym (PermProp.shift v [] L))
      ≈ᵛ σᵛ (v ∷ []) [] ⊗ᵛ idᵛ {L}
  permuteˢ-shift-sym-base v L =
    ≈-sym (≈-trans (⊗-resp (σ-unitʳˢ (vlab v ∷ [])) ≈-refl) ⊗-id)

  -- `permuteᵛ (bswap L R) ≈ᵛ σᵛ L R`.  BASE proven; the `(v ∷ L)` step is the
  -- `σ-hexᵛ` reconciliation `Interchange.BlockSwapComm.block-swap-comm`.
  bswap-σ-base : (R : List V) → permuteᵛ (bswap [] R) ≈ᵛ σᵛ [] R
  bswap-σ-base R =
    ≈-trans (refl-trivial (sym (++-identityʳ R)))
      (≈-sym (≈-trans (σ-unitᵛ R)
                      (≡⇒≈ˢ (castᵛ-cast refl (sym (++-identityʳ R)) idᵛ))))

  -- The full block-swap identity (statement) — the strict vertex-level
  -- block-swap-commutes keystone.  `bswap-σ-base` is the [] case.
  BswapSig : Set
  BswapSig = ∀ (L R : List V) → permuteᵛ (bswap L R) ≈ᵛ σᵛ L R

--------------------------------------------------------------------------------
-- The σ-shape, assembled from `bswap-σ` (the single residual) via the
-- `nE ≡ 0` collapse and `perm-rigidˢ`.

module _
  (bswap-σ : ∀ (V : Set) (vlab : V → X) → Scr.BswapSig V vlab)
  where

  ------------------------------------------------------------------------
  -- The σ-shape.

  module Sigma (A B : ObjTerm) where
    private
      f : HomTerm (A ⊗₀ B) (B ⊗₀ A)
      f = σ {A} {B}

      module RF = Run ⟪ f ⟫
      module Hf = Hypergraph ⟪ f ⟫
      open PK.Support (Fin Hf.nV) Hf.vlab
      open Restrict (Fin Hf.nV) Hf.vlab
        using (idᵛ; _∘ᵛ_; σᵛ; castᵛ; _≈ᵛ_; permuteᵛ; ∘-castᵛ; subst-codᵛ; σᵛ-≈̂)

      K : PermK
      K = PK.permˢ-K (Fin Hf.nV) _≟F_ Hf.vlab

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
      bsw = Scr.bswap (Fin Hf.nV) Hf.vlab Lblk Rblk

      -- the algorithm's final permutation equals `bsw` under `permuteˢ`,
      -- by `perm-rigidˢ` into the `Unique` codomain (exactly where the
      -- non-strict proof invokes K-faithfulness).
      perm≈ : RF.permuteˢ (finalPermˢ f)
              ≈ˢ RF.permuteˢ (subst (Perm._↭ Hf.cod) (sym s≡) bsw)
      perm≈ = perm-rigidˢ K (⟪⟫-cod-Unique f) (finalPermˢ f)
                (subst (Perm._↭ Hf.cod) (sym s≡) bsw)

    -- the block-swap identity at the hSwap blocks (the residual `bswap-σ`),
    -- V-level: `Hf.dom = Lblk ++ Rblk` and `Hf.cod = Rblk ++ Lblk` hold
    -- definitionally, so the braiding needs no frame cast.
    σ-block-≈ : RF.permuteˢ bsw ≈ᵛ σᵛ Lblk Rblk
    σ-block-≈ = bswap-σ (Fin Hf.nV) Hf.vlab Lblk Rblk

    private
      -- the run collapses to `coe` of the stack-equality (nE ≡ 0).
      run≡ : proj₂ RF.runˢ ≡ castᵛ refl (sym s≡) (idᵛ {Hf.dom})
      run≡ = trans (proj₂ collapse) (subst-codᵛ (sym s≡) idᵛ)

      -- `permuteᵛ` of the `s≡`-substituted canonical derivation is a `castᵛ`
      -- of `permuteᵛ bsw`.
      permsub≡ : RF.permuteˢ (subst (Perm._↭ Hf.cod) (sym s≡) bsw)
                 ≡ castᵛ (sym s≡) refl (permuteᵛ bsw)
      permsub≡ = permuteˢ-subst-dom (sym s≡) bsw
        where
          permuteˢ-subst-dom
            : ∀ {xs xs' ys : List (Fin Hf.nV)} (e : xs ≡ xs') (p : xs ↭ ys)
            → RF.permuteˢ (subst (Perm._↭ ys) e p)
              ≡ castᵛ e refl (permuteᵛ p)
          permuteˢ-subst-dom refl p = refl

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
-- The σ-shape is reduced to the single residual `bswap-σ` (`Scr.BswapSig`),
-- discharged in `Strict/Interchange/BlockSwapComm.agda` (the `[]` base is
-- `bswap-σ-base` here; the `(v ∷ L)` step is the σ-hexˢ reconciliation).  Fed
-- with `perm-rigidˢ` it collapses `finalPermˢ σ` onto `bswap`, giving
-- `decodePˢ (σ {A}{B}) ≈ σˢ (flatten A) (flatten B)`.
--------------------------------------------------------------------------------
