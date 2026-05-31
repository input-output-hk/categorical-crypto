{-# OPTIONS --safe --with-K #-}

--------------------------------------------------------------------------------
-- Construction of `decode-rel-≈-decode-impl`, the `decode-rel-≈-decode`
-- field of `DecodeRespIso.CompletenessAssumptions`, by wiring together
-- the constructive infrastructure of `DecoderAgreementSafe.agda` and the
-- per-constructor discharge modules in `Discharge/`.
--
-- ## Strategy
--
-- We construct a value of `DecoderAgreementAssumptions` (the 11-field
-- record from `DecoderAgreementSafe.agda`) and apply
-- `DecoderAgreementSafe.WithAssumptions.decode-rel-≈-decode` to obtain
-- the polymorphic `decode-rel ≈Term decode` agreement.
--
-- The 11 fields are assembled from existing constructive infrastructure
-- (DecodeShape, DecoderAgreementCases, DecoderAgreementRho,
-- DecoderAgreementAtomic) plus a small number of APROP-specific
-- residuals passed as parameters of the inner `FromResiduals` module.
--
-- This file is `--safe`-clean: no postulates.  Trust lives at the call
-- site that instantiates `FromResiduals`.
--------------------------------------------------------------------------------

open import Categories.APROP
open import Categories.APROP.Hypergraph.Solver.Signature using (APROPSignatureDec)

module Categories.APROP.Hypergraph.Completeness.FromAssumptions.DecodeRelDecode
  (sig-dec : APROPSignatureDec) where

open APROPSignatureDec sig-dec using (sig)
open APROP sig

open import Categories.APROP.Hypergraph.Completeness.DecodeAttempt sig
  using (decode)
open import Categories.APROP.Hypergraph.Completeness.DecodeRel sig
  using (decode-rel)
open import Categories.APROP.Hypergraph.Completeness.DecoderAgreementSafe sig
  using ( DecoderAgreementAssumptions
        ; Ty-Agen; Ty-σ; Ty-id; Ty-λ⇒; Ty-λ⇐
        ; Ty-ρ⇒; Ty-ρ⇐; Ty-α⇒; Ty-α⇐
        ; Ty-∘-shape; Ty-⊗-shape
        ; unapply-α⇒; unapply-α⇐
        ; unapply-∘-shape; unapply-⊗-shape
        )
import Categories.APROP.Hypergraph.Completeness.DecoderAgreementSafe as DAS
module DAS-sig = DAS sig
open import Categories.APROP.Hypergraph.Completeness.Discharge.DecodeShape sig
  using (DecodeShapeResiduals; module DecodeShapeResiduals)
import Categories.APROP.Hypergraph.Completeness.Discharge.DecoderAgreementCases as Cases
module Cases-sig = Cases sig
import Categories.APROP.Hypergraph.Completeness.Discharge.DecoderAgreementRho as Rho
module Rho-sig = Rho sig
open Rho-sig using (RhoShapeResidual)
open import Categories.APROP.Hypergraph.Completeness.Discharge.DecoderAgreementAtomic sig-dec
  using (module FromResiduals)
open import Categories.APROP.Hypergraph.Completeness.Discharge.DecodeRoundtripAgenSigma sig
  using (Residuals)

--------------------------------------------------------------------------------
-- ## The constructive wiring, exposed as a top-level `abstract` function.
--
-- `abstract` is critical: without it, downstream elaboration in
-- `Solver/Tests.agda` runs out of memory (>8 GB) due to the
-- module-application chain through `DecoderAgreementSafe.WithAssumptions`
-- and the `FromShape` / `FromResiduals` submodules.

abstract
  decode-rel-≈-decode-impl
    : (decodeShapeResiduals : DecodeShapeResiduals)
      (rhoShapeResidual : RhoShapeResidual)
      (agenSigmaResiduals : Residuals)
      (decode-rel-≈-decode-α⇒-impl
         : ∀ {A B C} → decode-rel (α⇒ {A} {B} {C}) ≈Term decode (α⇒ {A} {B} {C}))
      (decode-rel-≈-decode-α⇐-impl
         : ∀ {A B C} → decode-rel (α⇐ {A} {B} {C}) ≈Term decode (α⇐ {A} {B} {C}))
    → ∀ {A B} (f : HomTerm A B) → decode-rel f ≈Term decode f
  decode-rel-≈-decode-impl
    decodeShapeResiduals rhoShapeResidual agenSigmaResiduals
    decode-rel-≈-decode-α⇒-impl decode-rel-≈-decode-α⇐-impl =
    DAS-sig.WithAssumptions.decode-rel-≈-decode decoderAgreementAssumptions
    where
      module Shape = DecodeShapeResiduals decodeShapeResiduals

      ty-⊗-shape : Ty-⊗-shape
      ty-⊗-shape = unapply-⊗-shape (λ {A} {B} {C} {D} f g → Shape.decode-⊗-shape-inner f g)

      ty-∘-shape : Ty-∘-shape
      ty-∘-shape = unapply-∘-shape (λ {A} {B} {C} g f → Shape.decode-∘-shape-inner g f)

      module CasesShape = Cases-sig.FromShape ty-⊗-shape

      ty-id : Ty-id
      ty-id = CasesShape.ty-id
      ty-λ⇒ : Ty-λ⇒
      ty-λ⇒ = CasesShape.ty-λ⇒
      ty-λ⇐ : Ty-λ⇐
      ty-λ⇐ = CasesShape.ty-λ⇐

      module RhoShape = Rho-sig.FromShape ty-⊗-shape rhoShapeResidual

      ty-ρ⇒ : Ty-ρ⇒
      ty-ρ⇒ = RhoShape.ty-ρ⇒
      ty-ρ⇐ : Ty-ρ⇐
      ty-ρ⇐ = RhoShape.ty-ρ⇐

      module Atomic = FromResiduals agenSigmaResiduals

      ty-Agen : Ty-Agen
      ty-Agen = Atomic.ty-Agen
      ty-σ : Ty-σ
      ty-σ    = Atomic.ty-σ

      ty-α⇒ : Ty-α⇒
      ty-α⇒ = unapply-α⇒ (λ {A} {B} {C} → decode-rel-≈-decode-α⇒-impl {A} {B} {C})

      ty-α⇐ : Ty-α⇐
      ty-α⇐ = unapply-α⇐ (λ {A} {B} {C} → decode-rel-≈-decode-α⇐-impl {A} {B} {C})

      decoderAgreementAssumptions : DecoderAgreementAssumptions
      decoderAgreementAssumptions = record
        { decode-rel-≈-decode-Agen-T = ty-Agen
        ; decode-rel-≈-decode-σ-T    = ty-σ
        ; decode-rel-≈-decode-id-T   = ty-id
        ; decode-rel-≈-decode-λ⇒-T  = ty-λ⇒
        ; decode-rel-≈-decode-λ⇐-T  = ty-λ⇐
        ; decode-rel-≈-decode-ρ⇒-T  = ty-ρ⇒
        ; decode-rel-≈-decode-ρ⇐-T  = ty-ρ⇐
        ; decode-rel-≈-decode-α⇒-T  = ty-α⇒
        ; decode-rel-≈-decode-α⇐-T  = ty-α⇐
        ; decode-∘-shape-T           = ty-∘-shape
        ; decode-⊗-shape-T           = ty-⊗-shape
        }
