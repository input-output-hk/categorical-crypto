{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- DISCHARGE WORK for the `reconcileˢ` residual of `Strict.DecodeTensorS` — the
-- K-block prepend-asymmetry braid + final-permute resort completing the
-- ⊗-shape.  This is the strict port of the whole-run assembly TAIL of the
-- non-strict `Discharge.Sub.DecodeTensorShape`.
--
-- The TARGET (verified verbatim against `DecodeTensor.Tensor`'s `reconcileˢ`
-- parameter) is, for `f : HomTerm A B`, `g : HomTerm C D`:
--
--   reconcileˢ
--     : Run.permuteˢ ⟪ f ⊗₁ g ⟫ (finalPermˢ (f ⊗₁ g))
--         ∘ˢ proj₂ (Run.runˢ ⟪ f ⊗₁ g ⟫)
--       ≈ˢ castˢ (sym (⟪⟫-domL (f ⊗₁ g))) (sym (⟪⟫-codL (f ⊗₁ g)))
--           (decodePˢ f ⊗ˢ decodePˢ g)
--
-- WHAT IS PROVEN HERE (green, postulate-free, `--safe --without-K`):
--
--   * `final-resortˢ` — the FINAL-PERMUTE RESORT half, FULLY proven.  Via
--     `perm-rigidˢ` (the `Unique` codomain of `⟪ f ⊗₁ g ⟫` coming from
--     linearity) the algorithm's `finalPermˢ (f ⊗₁ g)` is collapsed onto ANY
--     chosen canonical derivation `cand : s-finˢ ↭ C.cod`, so
--         permuteˢ (finalPermˢ (f ⊗₁ g)) ≈ˢ permuteˢ cand.
--     This is the strict, tensor-level analogue of `DecodeSigma`'s `perm≈`
--     and is exactly where the non-strict proof invokes K-faithfulness.
--
--   * `reconcile-from-braid` — the REDUCTION: GIVEN the single K-block braid
--     fact `braidˢ` (one clearly-typed `≈ˢ`, stated below: the C-run inner
--     term, post-resort by a canonical derivation `cand`, equals the clean
--     tensor at the boundary objects), `reconcileˢ` follows by `final-resortˢ`
--     + `∘-resp`.  Hence the whole ⊗-shape rests on the SINGLE residual
--     `braidˢ` — the K-block prepend-asymmetry braid.
--
-- THE `braidˢ` PARAMETER (precisely typed; discharged DOWNSTREAM, not here):
--   `braidˢ`, the K-block braid: the strict statement that the C-run inner
--   term `permuteˢ cand ∘ˢ proj₂ runˢ`, with `cand` the canonical block-braid
--   derivation, equals `castˢ … (decodePˢ f ⊗ˢ decodePˢ g)`.  This is the
--   G-block frame (`G-block-frameˢ`, available) tensored with the K-block run
--   slid back past `G.cod` via `σˢ`/`σ-hexˢʳ`/`strict-braid`, reconciled with
--   the sub-decoder runs through the cross-vertex bridge `permuteˢ-X`.
--   `braidˢ` is supplied downstream by `Strict.Tensor.TensorBraid` (via the
--   K-prepend box-braid `KBlockσ`), so `decodePˢ-⊗-from-braid` here is fed a
--   concrete witness in `TensorKBlockFinal.decodePˢ-⊗-concrete` — making the
--   whole ⊗-shape UNCONDITIONAL (TensorKBlockFinal has ZERO postulates).
--------------------------------------------------------------------------------

open import Categories.APROP
open import Relation.Binary using (DecidableEquality)

module Categories.APROP.Hypergraph.Soundness.Strict.Tensor.TensorReconcile
  (sig : APROPSignature)
  (_≟X_ : DecidableEquality (APROPSignature.X sig))
  where

open APROP sig

open import Categories.APROP.Hypergraph.Model.Core using (Hypergraph; domL; codL)
open import Categories.APROP.Hypergraph.Model.Translation sig using (⟪_⟫; ⟪⟫-domL; ⟪⟫-codL)
open import Categories.APROP.Hypergraph.Soundness.Discharge.Sub.StackUnique
  sig using (Linear⇒cod-Unique)
open import Categories.APROP.Hypergraph.Soundness.Discharge.DecodeAttemptLinearP
  sig using (⟪⟫-LinearP)

open import Categories.APROP.Hypergraph.Soundness.Strict.Decode.Decode sig _≟X_
open import Categories.APROP.Hypergraph.Soundness.Strict.Perm.PermSupport sig _≟X_
import Categories.APROP.Hypergraph.Soundness.Strict.Decode.DecodeTensor sig _≟X_ as DT

open import Data.Fin using (Fin)
open import Data.Fin.Properties using () renaming (_≟_ to _≟F_)
open import Data.List using (List)
open import Data.List.Relation.Unary.Unique.Propositional using (Unique)
open import Data.Product using (_,_; proj₂)
open import Relation.Binary.PropositionalEquality using (sym)
import Data.List.Relation.Binary.Permutation.Propositional as Perm
open Perm using (_↭_)

--------------------------------------------------------------------------------
-- Threaded through the SAME deferred residual `permˢ-K` the whole strict chain
-- consumes (a `Support.PermK`, polymorphic over the vertex set).

module _
  (permˢ-K : ∀ (V : Set) (_≟V_ : DecidableEquality V) (vlab : V → X) → Support.PermK V vlab)
  where

  module Reconcile {A B C D : ObjTerm}
    (f : HomTerm A B) (g : HomTerm C D)
    where
    private
      fg : HomTerm (A ⊗₀ C) (B ⊗₀ D)
      fg = f ⊗₁ g

      module RF = Run ⟪ fg ⟫
      module Hf = Hypergraph ⟪ fg ⟫
      open Support (Fin Hf.nV) Hf.vlab

      K : PermK
      K = permˢ-K (Fin Hf.nV) _≟F_ Hf.vlab

      uniqCod : Unique Hf.cod
      uniqCod = Linear⇒cod-Unique ⟪ fg ⟫ (⟪⟫-LinearP fg)

    ----------------------------------------------------------------------
    -- ## The FINAL-PERMUTE RESORT half (FULLY PROVEN).
    --
    -- The algorithm's `finalPermˢ (f ⊗₁ g)` is a derivation `s-finˢ ↭ C.cod`
    -- into the `Unique` codomain `C.cod`.  By `perm-rigidˢ` it is
    -- `permuteˢ`-equal to ANY other derivation with the same endpoints — in
    -- particular the canonical block-braid derivation `cand` the braid half
    -- will supply.  This is the K-faithfulness consumption point.

    final-resortˢ
      : (cand : RF.s-finˢ ↭ Hf.cod)
      → RF.permuteˢ (finalPermˢ fg) ≈ˢ RF.permuteˢ cand
    final-resortˢ cand = perm-rigidˢ K uniqCod (finalPermˢ fg) cand

    ----------------------------------------------------------------------
    -- ## The REDUCTION: ⊗-shape ⇐ K-block braid.
    --
    -- The K-block braid `braidˢ` is the single clearly-typed `≈ˢ` fact: the
    -- C-run inner term, with the final permute REPLACED by the canonical
    -- derivation `cand`, equals the clean tensor at the boundary objects.
    -- (Cast-FREE: stated at the boundary objects, like `reconcileˢ` itself.)
    --
    -- Given `braidˢ`, `reconcileˢ` follows by rewriting the algorithm's
    -- `permuteˢ (finalPermˢ fg)` to `permuteˢ cand` via `final-resortˢ`.

    reconcile-from-braid
      : (cand : RF.s-finˢ ↭ Hf.cod)
      → (braidˢ
          : RF.permuteˢ cand ∘ˢ proj₂ (Run.runˢ ⟪ fg ⟫)
            ≈ˢ castˢ (sym (⟪⟫-domL fg)) (sym (⟪⟫-codL fg))
                (decodePˢ f ⊗ˢ decodePˢ g))
      → RF.permuteˢ (finalPermˢ fg) ∘ˢ proj₂ (Run.runˢ ⟪ fg ⟫)
        ≈ˢ castˢ (sym (⟪⟫-domL fg)) (sym (⟪⟫-codL fg))
            (decodePˢ f ⊗ˢ decodePˢ g)
    reconcile-from-braid cand braidˢ = ≈-trans (∘-resp (final-resortˢ cand) ≈-refl) braidˢ

    ----------------------------------------------------------------------
    -- VERIFICATION that `reconcile-from-braid` produces EXACTLY the
    -- `reconcileˢ` parameter of `DecodeTensor.Tensor`, and that feeding it
    -- yields the ⊗-shape THEOREM `decodePˢ (f ⊗₁ g) ≈ˢ decodePˢ f ⊗ˢ
    -- decodePˢ g` modulo the single residual `braidˢ` (the K-block braid).

    decodePˢ-⊗-from-braid
      : (cand : RF.s-finˢ ↭ Hf.cod)
      → (braidˢ
          : RF.permuteˢ cand ∘ˢ proj₂ (Run.runˢ ⟪ fg ⟫)
            ≈ˢ castˢ (sym (⟪⟫-domL fg)) (sym (⟪⟫-codL fg))
                (decodePˢ f ⊗ˢ decodePˢ g))
      → decodePˢ fg ≈ˢ decodePˢ f ⊗ˢ decodePˢ g
    decodePˢ-⊗-from-braid cand braidˢ =
      DT.Tensor.decodePˢ-⊗ permˢ-K f g (reconcile-from-braid cand braidˢ)

--------------------------------------------------------------------------------
-- `reconcileˢ` = `final-resortˢ` (proven here, via `perm-rigidˢ` on the
-- `Unique` cod) + the single K-block braid residual `braidˢ`, discharged
-- downstream in `Strict/Tensor/TensorBraid` (concrete witness
-- `TensorKBlockFinal.decodePˢ-⊗-concrete`, zero postulates).  See the header
-- for `braidˢ`'s statement and the CRITICAL-ASYMMETRY content it packages.
--------------------------------------------------------------------------------
