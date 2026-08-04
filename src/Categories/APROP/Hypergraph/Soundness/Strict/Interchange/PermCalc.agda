{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- The THIN WIRING-GROUPOID calculus (`≈̂`-level `PermCalc`, F11).
--
-- Every "located coherence" proof in the strict interchange/tensor cone
-- (`vin-cohᵛ`/`vout-cohᵛ`, `in-eq`/`out-eq`/`σ-side`/`glue`, `in-reconcile`,
-- `in-combined`, …) has the SAME skeleton: present each side as `permuteˢ` of a
-- `_↭_`-derivation, identify the two derivations by rigidity on their `Unique`
-- codomain, and reconcile the `castˢ` paths by `cast-fuse`/`cast-irrel`/
-- `∘-cast-split`.  The reconciliation is pure noise; only the rigidity step is
-- content.
--
-- Mathematically: permutation morphisms between `Unique` stacks form a THIN
-- groupoid (rigidity), presented by `_↭_`-derivations under `permuteˢ`.  This
-- module gives `permuteˢ` the structure of an `_≈̂_`-homomorphism, so every
-- located proof reduces to congruence bookkeeping over the bridges below —
-- all statements HETEROGENEOUS, so no cast path is ever named.
--
-- The bridges are `≈̂`-restatements of EXISTING lemmas:
--   ⟦absorbˡ⟧/⟦absorbʳ⟧ — a reindexing factor is absorbed (`idˡ`/`idʳ`)
--   ⟦frameˡ⟧    — `SwapCore.permuteˢ-frameˡ`  (+ its V face ⟦frameˡ⟧ᵛ)
--   ⟦frameʳ⟧    — `FreeStrictSMC.Perm′.permuteˢ-frame`
--   ⟦bswap⟧ᵛ    — `BlockSwapComm.swap-block`
--   rigid-≈̂     — `SwapCore.perm-rigidˢ`   (the rigidity discharge)
--------------------------------------------------------------------------------

open import Categories.APROP
open import Relation.Binary using (DecidableEquality)

module Categories.APROP.Hypergraph.Soundness.Strict.Interchange.PermCalc
  (sig : APROPSignature)
  (_≟X_ : DecidableEquality (APROPSignature.X sig))
  where

open APROP sig using (X)

open import Categories.APROP.Hypergraph.Model.Core using (Hypergraph)
open import Categories.APROP.Hypergraph.Model.FromAPROP sig using (FlatGen)

open import Categories.APROP.Hypergraph.Soundness.Strict.Decode.Decoder sig _≟X_
open import Categories.APROP.Hypergraph.Soundness.Strict.Perm.PermSupport sig _≟X_
open import Categories.APROP.Hypergraph.Soundness.Strict.Interchange.SwapCore sig _≟X_

import Categories.APROP.Hypergraph.Soundness.Strict.Interchange.BlockSwapComm sig _≟X_ as BSC
import Categories.APROP.Hypergraph.Soundness.Strict.Decode.DecodeSigma sig _≟X_ as DSS

open import Data.Fin using (Fin)
open import Data.List using (List; map)
open import Data.List.Relation.Unary.Unique.Propositional using (Unique)
import Data.List.Relation.Binary.Permutation.Propositional as Perm
import Data.List.Relation.Binary.Permutation.Propositional.Properties as PermProp
open import Data.List.Properties using (map-++)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

--------------------------------------------------------------------------------

module Kit (H : Hypergraph FlatGen)
           (permˢ-K : Support.PermK (Fin (Hypergraph.nV H)) (Hypergraph.vlab H))
           where
  private module H = Hypergraph H

  open StrictDecoder H

  open Restrict (Fin H.nV) vl
    using (idᵛ; _⊗ᵛ_; σᵛ; _≈ᵛ_; permuteᵛ)

  private
    m : List (Fin H.nV) → List X
    m = map vl

  -- Existing bridges, threaded at this hypergraph's vertex set.
  private
    perm-rigidˢ′ = perm-rigidˢ H permˢ-K
    perm-frameˡ′ = permuteˢ-frameˡ
    swap-block′  = BSC.swap-block (Fin H.nV) H.vlab
  open DSS.Scr (Fin H.nV) H.vlab using (bswap)

  ------------------------------------------------------------------------
  -- ⟦absorbˡ⟧/⟦absorbʳ⟧ : a reindexing FACTOR of a sequential derivation is
  -- absorbed by the identity laws (the reindex is an `idˢ` on that side).
  ------------------------------------------------------------------------
  ⟦absorbˡ⟧
    : ∀ {xs ys zs : List (Fin H.nV)} {p : xs Perm.↭ ys} (eq : ys ≡ zs)
    → permuteˢ (Perm.trans p (Perm.↭-reflexive eq)) ≈̂ permuteˢ p
  ⟦absorbˡ⟧ refl = ≈ˢ⇒≈̂ idˡ

  ⟦absorbʳ⟧
    : ∀ {xs ys zs : List (Fin H.nV)} (eq : xs ≡ ys) {p : ys Perm.↭ zs}
    → permuteˢ (Perm.trans (Perm.↭-reflexive eq) p) ≈̂ permuteˢ p
  ⟦absorbʳ⟧ refl = ≈ˢ⇒≈̂ idʳ

  ------------------------------------------------------------------------
  -- ⟦frameˡ⟧ : a `++⁺ˡ ls` frame becomes a `idˢ ⊗ˢ_` frame.
  ------------------------------------------------------------------------
  ⟦frameˡ⟧
    : ∀ (ls : List (Fin H.nV)) {xs ys : List (Fin H.nV)} (p : xs Perm.↭ ys)
    → permuteˢ (PermProp.++⁺ˡ ls p) ≈̂ idˢ {m ls} ⊗ˢ permuteˢ p
  ⟦frameˡ⟧ ls p = ≈̂-trans (≈̂-sym cast-≈̂) (≈ˢ⇒≈̂ (perm-frameˡ′ ls p))

  -- …and its V-level face, where the frame IS `idᵛ ⊗ᵛ_` (no cast to peel).
  ⟦frameˡ⟧ᵛ
    : ∀ (ls : List (Fin H.nV)) {xs ys : List (Fin H.nV)} (p : xs Perm.↭ ys)
    → permuteᵛ (PermProp.++⁺ˡ ls p) ≈ᵛ idᵛ {ls} ⊗ᵛ permuteᵛ p
  ⟦frameˡ⟧ᵛ ls {xs} {ys} p =
    cast-flip (map-++ vl ls xs) (map-++ vl ls ys) (perm-frameˡ′ ls p)

  ------------------------------------------------------------------------
  -- ⟦frameʳ⟧ : a `++⁺ʳ R` frame becomes a `_⊗ˢ idˢ` frame.
  ------------------------------------------------------------------------
  ⟦frameʳ⟧
    : ∀ (R : List (Fin H.nV)) {xs ys : List (Fin H.nV)} (p : xs Perm.↭ ys)
    → permuteˢ (PermProp.++⁺ʳ R p) ≈̂ permuteˢ p ⊗ˢ idˢ {m R}
  ⟦frameʳ⟧ R p = ≈̂-trans (≈̂-sym cast-≈̂) (≈ˢ⇒≈̂ (permuteˢ-frame R p))

  ------------------------------------------------------------------------
  -- ⟦bswap⟧ᵛ : a `++⁺ʳ Rl`-framed canonical block swap is the strict block
  -- braiding — `BlockSwapComm.swap-block` verbatim at V level.
  ------------------------------------------------------------------------
  ⟦bswap⟧ᵛ
    : ∀ (L R Rl : List (Fin H.nV))
    → permuteᵛ (PermProp.++⁺ʳ Rl (bswap L R)) ≈ᵛ σᵛ L R ⊗ᵛ idᵛ {Rl}
  ⟦bswap⟧ᵛ = swap-block′

  ------------------------------------------------------------------------
  -- rigid-≈̂ : the RIGIDITY discharge — any two derivations into a `Unique`
  -- stack are `permuteˢ`-equal (the wiring groupoid is thin).
  ------------------------------------------------------------------------
  rigid-≈̂
    : ∀ {xs ys : List (Fin H.nV)} → Unique ys
    → (p q : xs Perm.↭ ys) → permuteˢ p ≈̂ permuteˢ q
  rigid-≈̂ u p q = ≈ˢ⇒≈̂ (perm-rigidˢ′ u p q)
