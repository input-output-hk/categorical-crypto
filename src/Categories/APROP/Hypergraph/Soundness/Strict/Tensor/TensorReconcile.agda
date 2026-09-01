{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- The ⊗-SHAPE of the strict decoder `decodePˢ` (strict analogue of the former
-- non-strict `DecodeTensorShape`), reduced to its ONE residual and discharged
-- down to the K-block braid:
--
--   decodePˢ-⊗ : decodePˢ (f ⊗₁ g) ≈ˢ decodePˢ f ⊗ˢ decodePˢ g
--
-- CRITICAL ASYMMETRY (the documented finding — NOT re-discovered here).  The
-- ⊗-shape is NOT two separability frames.  `edge-stepˢ` PREPENDS fired outputs:
--
--   * the RIGHT frame (untouched region = SUFFIX) works — this is the PROVEN
--     `Decoder.term-sepᵛ`.  It factors the G-block run over `C.dom =
--     map injL G.dom ++ map injR K.dom` as `(G-run on map injL G.dom) ⊗ᵛ
--     idᵛ {map injR K.dom}` (the untouched K-input is a suffix).
--   * the LEFT frame is FALSE for any firing block: in `hTensor G K`, after
--     G's block fires (leaving `G.cod ++ K.dom`-shaped stack), K's edges act on
--     the K-input suffix and PREPEND K's outputs in FRONT of `G.cod`, producing
--     a BRAIDED form (`SeparableStack`'s obstruction note: no left frame).
--
-- So the clean `decodePˢ f ⊗ˢ decodePˢ g` is recovered ONLY at the whole-decode
-- level, where the final closing permutation `finalPermˢ (f ⊗₁ g)`
-- re-sorts the braided K-outputs back behind `G.cod`.  That is the `braidˢ`
-- residual below; in the strict SMC it collapses to the `σˢ`/`σ-hexˢ` machinery
-- of `Strict/Perm/Braid.agda` + `Strict/Interchange/BlockSwapComm.agda`.
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
--     tensor at the boundary objects), `BraidSigˢ (finalPermˢ fg)` follows by
--     `final-resortˢ` + `∘-resp`.  Hence the whole ⊗-shape rests on the SINGLE
--     residual `braidˢ` — the K-block prepend-asymmetry braid.
--
--   * `decodePˢ-⊗-from-braid` — the ⊗-shape itself, from that by `viaˢ`.
--
-- THE `braidˢ` PARAMETER (precisely typed; discharged DOWNSTREAM, not here):
--   `braidˢ`, the K-block braid: the strict statement that the C-run inner
--   term `permuteˢ cand ∘ˢ proj₂ runˢ`, with `cand` the canonical block-braid
--   derivation, equals `castˢ … (decodePˢ f ⊗ˢ decodePˢ g)`.  This is the
--   G-block frame (`TensorBraid.gframe`, available) tensored with the K-block
--   run slid back past `G.cod` via `σˢ`/`σ-hexˢʳ`/`strict-braid`, reconciled
--   with the sub-decoder runs through `PermRelabel.pvv-≈̂`.
--   `braidˢ` is supplied downstream by `Strict.Tensor.TensorBraid` (via the
--   K-prepend box-braid `KBlockσ`), so `decodePˢ-⊗-from-braid` here is fed a
--   concrete witness in `TensorBraid.decodePˢ-⊗-concrete` — making the
--   whole ⊗-shape UNCONDITIONAL (with ZERO postulates).
--------------------------------------------------------------------------------

open import Categories.APROP
open import Relation.Binary using (DecidableEquality)

module Categories.APROP.Hypergraph.Soundness.Strict.Tensor.TensorReconcile
  (sig : APROPSignature)
  (_≟X_ : DecidableEquality (APROPSignature.X sig))
  where

open APROP sig

open import Categories.APROP.Hypergraph.Model.Core using (Hypergraph)
open import Categories.APROP.Hypergraph.Model.Translation sig using (⟪_⟫; ⟪⟫-domL; ⟪⟫-codL)
open import Categories.APROP.Hypergraph.Soundness.Stack.StackUnique
  sig using (⟪⟫-cod-Unique)

open import Categories.APROP.Hypergraph.Soundness.Strict.Decode.Decode sig _≟X_

open Perm using (_↭_)

--------------------------------------------------------------------------------
-- The strict Kelly residual is taken CONCRETELY from `Perm.PermK` (axiom-free
-- for every vertex set), exactly as the rest of the strict chain takes it.

module Reconcile {A B C D : ObjTerm}
  (f : HomTerm A B) (g : HomTerm C D)
  where
  private
    fg : HomTerm (A ⊗₀ C) (B ⊗₀ D)
    fg = f ⊗₁ g

    module RF = Run ⟪ fg ⟫
    module Hf = Hypergraph ⟪ fg ⟫

  -- THE `braidˢ` RESIDUAL, named: the C-run inner term post-sorted by
  -- `cand` is the clean tensor at the boundary objects.  At
  -- `cand := finalPermˢ fg` this signature IS the ⊗-shape conjugated by
  -- `castˢ (⟪⟫-domL fg) (⟪⟫-codL fg)`.
  BraidSigˢ : RF.s-finˢ ↭ Hf.cod → Set
  BraidSigˢ cand =
    RF.permuteˢ cand ∘ˢ proj₂ (Run.runˢ ⟪ fg ⟫)
      ≈ˢ castˢ (sym (⟪⟫-domL fg)) (sym (⟪⟫-codL fg))
          (decodePˢ f ⊗ˢ decodePˢ g)

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
  final-resortˢ cand = RF.rigidˢ (⟪⟫-cod-Unique fg) (finalPermˢ fg) cand

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
    : (cand : RF.s-finˢ ↭ Hf.cod) → BraidSigˢ cand → BraidSigˢ (finalPermˢ fg)
  reconcile-from-braid cand braidˢ = ≈-trans (∘-resp (final-resortˢ cand) ≈-refl) braidˢ

  ----------------------------------------------------------------------
  -- The ⊗-shape THEOREM, modulo the single residual `braidˢ`.  Boundaries
  -- align definitionally (`flatten` distributes over `⊗₀` as `_++_`), so the
  -- statement is cast-free and `BraidSigˢ (finalPermˢ fg)` is exactly it
  -- conjugated by `castˢ (⟪⟫-domL fg) (⟪⟫-codL fg)`.

  decodePˢ-⊗-from-braid
    : (cand : RF.s-finˢ ↭ Hf.cod) → BraidSigˢ cand
    → decodePˢ fg ≈ˢ decodePˢ f ⊗ˢ decodePˢ g
  decodePˢ-⊗-from-braid cand braidˢ =
    viaˢ (cast-≈̂ {p = ⟪⟫-domL fg} {q = ⟪⟫-codL fg})
         (reconcile-from-braid cand braidˢ)
         (≈̂-sym (cast-≈̂ {p = sym (⟪⟫-domL fg)} {q = sym (⟪⟫-codL fg)}))

--------------------------------------------------------------------------------
-- The ⊗-shape = `final-resortˢ` (proven here, via `perm-rigidˢ` on the
-- `Unique` cod) + the single K-block braid residual `braidˢ`, discharged
-- downstream in `Strict/Tensor/TensorBraid` (concrete witness
-- `TensorBraid.decodePˢ-⊗-concrete`, zero postulates).  See the header
-- for `braidˢ`'s statement and the CRITICAL-ASYMMETRY content it packages.
--------------------------------------------------------------------------------
