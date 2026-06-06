{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- Part (I) of the completeness proof: structural ↔ pruned-algorithmic
-- decoder NORMAL-FORM agreement
--
--     decode-rel-≈-decodeP : ∀ {A B} (f : HomTerm A B)
--                          → decode-rel f ≈Term decodeP f
--
-- consumed in `Discharge.DecodeRelRespIsoWired`.
--
-- ## The reduction
--
-- For EVERY ATOMIC constructor X (Agen, σ, id, λ⇒, λ⇐, ρ⇒, ρ⇐, α⇒, α⇐):
--
--     decodeP X  ≡  decode X     (DEFINITIONALLY, by `refl`)
--
-- because the pruned translation and the unpruned one are identical on
-- every HomTerm constructor EXCEPT `∘` (pruning removes only vertices,
-- never edges; it only changes the `∘` case, `hComposeP` vs `hCompose`).
-- This collapses the pruned residual surface to:
--
--   (U)  the UNPRUNED dispatcher `decode-rel-≈-decode`, assembled here
--        from the SAME shared residual records the unpruned completeness
--        proof and the interchange chain already depend on; AND
--
--   (B)  the pruned-vs-unpruned BRIDGE on the two recursive constructors
--        `decodeP-≈-decode-{∘,⊗}`; every ATOMIC case is `refl`.
--
-- The dispatcher is then:
--
--     decode-rel-≈-decodeP f
--       = decode-rel f  ≈⟨ decode-rel-≈-decode f ⟩  decode f
--                       ≈⟨ sym (decodeP-≈-decode f) ⟩  decodeP f
--
-- The (B) bridges are factored through `decodePShapeResiduals` consuming
-- the two PRUNED shape lemmas (the `decodeP` mirrors of the unpruned
-- `decode-{∘,⊗}-shape-inner`). The pruned ⊗-shape reuses the SAME `hTensor`
-- block machinery as the unpruned proof (tensor is not pruned).
--
-- The transitive live trust surface of part (I) is {K-faithfulness}.
--------------------------------------------------------------------------------

open import Categories.APROP

open import Relation.Binary using (DecidableEquality)

module Categories.APROP.Hypergraph.Completeness.Discharge.DecodeRelDecodeP
  (sig : APROPSignature)
  (_≟X_ : DecidableEquality (APROPSignature.X sig)) where

open APROP sig

open import Categories.APROP.Hypergraph.FromAPROP sig
  using (flatten; domL-hId; codL-hId)
open import Categories.APROP.Hypergraph.Completeness.Unflatten sig
  using (unflatten)
open import Categories.APROP.Hypergraph.Translation sig
  using (⟪⟫-domL; ⟪⟫-codL)
open import Categories.APROP.Hypergraph.Completeness.DecodeRel sig
  using (decode-rel)
open import Categories.APROP.Hypergraph.Completeness.Discharge.DecodeAttemptLinearP sig
  using (decode-attempt-LinearP)

open import Categories.APROP.Hypergraph.Completeness.DecodeAttempt sig
  using (decode; decode-attempt-hId)
open import Categories.APROP.Hypergraph.Completeness.DecoderAgreementSafe sig
  using ( DecoderAgreementAssumptions; module WithAssumptions
        ; Ty-Agen; Ty-σ; Ty-id; Ty-λ⇒; Ty-λ⇐; Ty-ρ⇒; Ty-ρ⇐; Ty-α⇒; Ty-α⇐
        ; Ty-∘-shape; Ty-⊗-shape
        ; unapply-Agen; unapply-σ; unapply-α⇒; unapply-α⇐
        ; unapply-∘-shape; unapply-⊗-shape )
open import Categories.APROP.Hypergraph.Completeness.Discharge.DecodeShape sig
  using (DecodeShapeResiduals; module DecodeShapeResiduals)
-- The shape lemmas (∘-side, ⊗-side), each in a top-level `module _ (objUIP)(Kf)`.
import Categories.APROP.Hypergraph.Completeness.Discharge.Sub.DecodeComposeShape sig as DCS
import Categories.APROP.Hypergraph.Completeness.Discharge.Sub.DecodeTensorShape sig _≟X_ as DTS
-- The PRUNED shape lemmas (∘-side, ⊗-side).
import Categories.APROP.Hypergraph.Completeness.Discharge.Sub.DecodeComposePruned sig as DCP
import Categories.APROP.Hypergraph.Completeness.Discharge.Sub.DecodeTensorPruned sig _≟X_ as DTP
-- The single-edge collapses `decode-{Agen,σ}-collapse`.
import Categories.APROP.Hypergraph.Completeness.Discharge.Sub.DecodeAgenSigmaShape sig _≟X_ as DAS
import Categories.APROP.Hypergraph.Completeness.Discharge.DecoderAgreementCases as Cases
module Cases-sig = Cases sig
import Categories.APROP.Hypergraph.Completeness.Discharge.DecoderAgreementRho as Rho
module Rho-sig = Rho sig
open Rho-sig using (RhoShapeResidual)
open import Categories.APROP.Hypergraph.Completeness.Discharge.DecodeRoundtripAgenSigma sig
  using (Residuals; module Residuals)
open import Categories.APROP.Hypergraph.Completeness.Discharge.Sub.ProcessEdgesTermShape sig
  using (DecodePShapeResiduals; module Assemble)
open import Categories.APROP.Hypergraph.Completeness.Discharge.Sub.HomTermTransport sig
  using (subst₂-cod-trans; subst₂-dom-trans)

open import Categories.PermuteCoherence.Faithfulness asFreeMonoidalData
  using (FaithfulnessResidual)

open import Categories.Category using (Category)
open import Data.Product using (proj₁)
open import Data.List using (List)
open import Data.List.Properties using (++-identityʳ)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; trans; cong; subst₂)

--------------------------------------------------------------------------------
-- The pruned decoder `decodeP`: the boundary `subst₂`-transport of
-- `proj₁ (decode-attempt-LinearP f)`, using the pruned translation's
-- `⟪⟫-{dom,cod}L`.  Replicated here rather than imported so this module
-- avoids the host module's transitive dependency on `FinOrderNoInv`.
--------------------------------------------------------------------------------

decodeP : ∀ {A B} (f : HomTerm A B)
        → HomTerm (unflatten (flatten A)) (unflatten (flatten B))
decodeP {A} {B} f =
  subst₂ HomTerm (cong unflatten (⟪⟫-domL f)) (cong unflatten (⟪⟫-codL f))
         (proj₁ (decode-attempt-LinearP f))

private
  module FM = Category FreeMonoidal

  ≡⇒≈Term : ∀ {A B} {f g : HomTerm A B} → f ≡ g → f ≈Term g
  ≡⇒≈Term refl = ≈-Term-refl

--------------------------------------------------------------------------------
-- ## `rhoShapeResidual`.
--
-- `RhoShapeResidual` packages two `_≡_` characterisations relating
-- `decode (ρ{⇒,⇐} {A})` to `decode (id {A ⊗₀ unit})` modulo the trailing
-- `++-identityʳ`.  These are PURE boundary-`subst₂` ALGEBRA, not
-- process-edges content: `⟪ ρ⇒ {A} ⟫ = hId (A ⊗₀ unit) = ⟪ id {A ⊗₀ unit} ⟫`,
-- so both decoders share the SAME inner term and differ ONLY in the
-- boundary equations.  The identity follows from a generic
-- `subst₂`-over-`trans` split (a `--with-K` UIP-level transport fact).
--------------------------------------------------------------------------------

private
  rho⇒-shape
    : ∀ A → decode (ρ⇒ {A})
         ≡ subst₂ HomTerm refl (cong unflatten (++-identityʳ (flatten A)))
                  (decode (id {A ⊗₀ unit}))
  rho⇒-shape A =
    subst₂-cod-trans (domL-hId (A ⊗₀ unit)) (codL-hId (A ⊗₀ unit))
                     (++-identityʳ (flatten A))
                     (proj₁ (decode-attempt-hId (A ⊗₀ unit)))

  rho⇐-shape
    : ∀ A → decode (ρ⇐ {A})
         ≡ subst₂ HomTerm (cong unflatten (++-identityʳ (flatten A))) refl
                  (decode (id {A ⊗₀ unit}))
  rho⇐-shape A =
    subst₂-dom-trans (domL-hId (A ⊗₀ unit)) (++-identityʳ (flatten A))
                     (codL-hId (A ⊗₀ unit))
                     (proj₁ (decode-attempt-hId (A ⊗₀ unit)))

rhoShapeResidual : RhoShapeResidual
rhoShapeResidual = record
  { decode-ρ⇒-shape = rho⇒-shape
  ; decode-ρ⇐-shape = rho⇐-shape
  }

--------------------------------------------------------------------------------
-- ## (B) The pruned-vs-unpruned BRIDGE, factored through PRUNED shapes.
--
-- The two recursive constructors are the only places `decodeP X` and
-- `decode X` can differ.  Each bridge is factored through a PRUNED shape
-- lemma + the structural recursion + the unpruned shape:
--
--     decodeP (g∘f) ≈⟨ pruned ∘ shape ⟩ decodeP g ∘ decodeP f
--                   ≈⟨ rec g , rec f  ⟩ decode  g ∘ decode  f
--                   ≈⟨ sym (unpruned ∘ shape) ⟩ decode (g∘f)
--
-- (and dually for `⊗`).  The assembler `Assemble.decodeP-≈-decode-∘-from`
-- performs the chain; `decodeP-≈-decode` itself is the recursion `rec`.
--
-- Everything that consumes the shape residuals is parameterised by
-- `(objUIP)(K)`; `DecodeRelRespIsoWired` passes its own `objUIP`/
-- `K-faithfulness` at the consume site.
--------------------------------------------------------------------------------

module Wired
  (objUIP : ∀ {A B : ObjTerm} (p q : A ≡ B) → p ≡ q)
  (K : FaithfulnessResidual)
  where

  decodeShapeResiduals : DecodeShapeResiduals
  decodeShapeResiduals = record
    { decode-∘-shape-inner = DCS.decode-∘-shape-inner objUIP K
    ; decode-⊗-shape-inner = DTS.decode-⊗-shape-inner objUIP K
    }

  -- Consumes the single-edge collapses `decode-{Agen,σ}-collapse`.
  agenSigmaResiduals : Residuals
  agenSigmaResiduals = record
    { decode-Agen-collapse = λ {A} {B} g → DAS.decode-Agen-collapse objUIP K g
    ; decode-σ-collapse    = λ {A} {B} ⦃ s ⦄ → DAS.decode-σ-collapse objUIP K ⦃ s ⦄
    }

  -- The two atomic associator obligations.  `decode-rel (α{⇒,⇐}) =
  -- bridge (α{⇒,⇐})` DEFINITIONALLY, so each is `≈-Term-sym` of the
  -- collapse `DAS.decode-α{⇒,⇐}-collapse`.
  decode-rel-≈-decode-α⇒
    : ∀ {A B C} → decode-rel (α⇒ {A} {B} {C}) ≈Term decode (α⇒ {A} {B} {C})
  decode-rel-≈-decode-α⇒ {A} {B} {C} =
    ≈-Term-sym (DAS.decode-α⇒-collapse objUIP K {A} {B} {C})

  decode-rel-≈-decode-α⇐
    : ∀ {A B C} → decode-rel (α⇐ {A} {B} {C}) ≈Term decode (α⇐ {A} {B} {C})
  decode-rel-≈-decode-α⇐ {A} {B} {C} =
    ≈-Term-sym (DAS.decode-α⇐-collapse objUIP K {A} {B} {C})

  -- Consumes the two PRUNED shape lemmas.
  decodePShapeResiduals : DecodePShapeResiduals
  decodePShapeResiduals = record
    { decodeP-∘-shape = λ {A} {B} {C} g f → DCP.decodeP-∘-shape objUIP K g f
    ; decodeP-⊗-shape = λ {A} {B} {C} {D} f g → DTP.decodeP-⊗-shape objUIP K f g
    }

  -- Assemble the unpruned `DecoderAgreementAssumptions` from the residual
  -- records.
  private
    module Shape = DecodeShapeResiduals decodeShapeResiduals
    module AS    = Residuals agenSigmaResiduals

    ty-⊗-shape : Ty-⊗-shape
    ty-⊗-shape = unapply-⊗-shape (λ {A} {B} {C} {D} f g → Shape.decode-⊗-shape-inner f g)

    ty-∘-shape : Ty-∘-shape
    ty-∘-shape = unapply-∘-shape (λ {A} {B} {C} g f → Shape.decode-∘-shape-inner g f)

    module CasesShape = Cases-sig.FromShape ty-⊗-shape
    module RhoShape   = Rho-sig.FromShape ty-⊗-shape rhoShapeResidual

    ty-Agen : Ty-Agen
    ty-Agen = unapply-Agen (λ {A} {B} g → ≈-Term-sym (AS.decode-Agen-collapse g))

    ty-σ : Ty-σ
    ty-σ = unapply-σ (λ {A} {B} ⦃ s ⦄ → ≈-Term-sym (AS.decode-σ-collapse ⦃ s ⦄))

    ty-α⇒ : Ty-α⇒
    ty-α⇒ = unapply-α⇒ (λ {A} {B} {C} → decode-rel-≈-decode-α⇒ {A} {B} {C})

    ty-α⇐ : Ty-α⇐
    ty-α⇐ = unapply-α⇐ (λ {A} {B} {C} → decode-rel-≈-decode-α⇐ {A} {B} {C})

    unprunedAssumptions : DecoderAgreementAssumptions
    unprunedAssumptions = record
      { decode-rel-≈-decode-Agen-T = ty-Agen
      ; decode-rel-≈-decode-σ-T    = ty-σ
      ; decode-rel-≈-decode-id-T   = CasesShape.ty-id
      ; decode-rel-≈-decode-λ⇒-T  = CasesShape.ty-λ⇒
      ; decode-rel-≈-decode-λ⇐-T  = CasesShape.ty-λ⇐
      ; decode-rel-≈-decode-ρ⇒-T  = RhoShape.ty-ρ⇒
      ; decode-rel-≈-decode-ρ⇐-T  = RhoShape.ty-ρ⇐
      ; decode-rel-≈-decode-α⇒-T  = ty-α⇒
      ; decode-rel-≈-decode-α⇐-T  = ty-α⇐
      ; decode-∘-shape-T           = ty-∘-shape
      ; decode-⊗-shape-T           = ty-⊗-shape
      }

  -- The unpruned dispatcher, derived constructively (induction on `f`) from
  -- the assembled assumptions via `DecoderAgreementSafe.WithAssumptions`.
  decode-rel-≈-decode
    : ∀ {A B} (f : HomTerm A B) → decode-rel f ≈Term decode f
  decode-rel-≈-decode = WithAssumptions.decode-rel-≈-decode unprunedAssumptions

  private
    module Asm = Assemble decode
                   (λ {A} {B} {C} g f → Shape.decode-∘-shape-inner g f)
                   (λ {A} {B} {C} {D} f g → Shape.decode-⊗-shape-inner f g)
                   decodePShapeResiduals

  -- The full pruned-vs-unpruned bridge.  ATOMIC cases: `refl`.  Recursive
  -- cases: the factoring assemblers on the structurally-smaller sub-terms.
  decodeP-≈-decode : ∀ {A B} (f : HomTerm A B) → decodeP f ≈Term decode f
  decodeP-≈-decode (Agen g)  = ≡⇒≈Term refl
  decodeP-≈-decode (σ ⦃ s ⦄) = ≡⇒≈Term refl
  decodeP-≈-decode id        = ≡⇒≈Term refl
  decodeP-≈-decode λ⇒        = ≡⇒≈Term refl
  decodeP-≈-decode λ⇐        = ≡⇒≈Term refl
  decodeP-≈-decode ρ⇒        = ≡⇒≈Term refl
  decodeP-≈-decode ρ⇐        = ≡⇒≈Term refl
  decodeP-≈-decode α⇒        = ≡⇒≈Term refl
  decodeP-≈-decode α⇐        = ≡⇒≈Term refl
  decodeP-≈-decode (g ∘ f)   =
    Asm.decodeP-≈-decode-∘-from g f (decodeP-≈-decode g) (decodeP-≈-decode f)
  decodeP-≈-decode (f ⊗₁ g)  =
    Asm.decodeP-≈-decode-⊗-from f g (decodeP-≈-decode f) (decodeP-≈-decode g)

  decodeP-≈-decode-∘
    : ∀ {A B C} (g : HomTerm B C) (f : HomTerm A B)
    → decodeP (g ∘ f) ≈Term decode (g ∘ f)
  decodeP-≈-decode-∘ g f = decodeP-≈-decode (g ∘ f)

  decodeP-≈-decode-⊗
    : ∀ {A B C D} (f : HomTerm A B) (g : HomTerm C D)
    → decodeP (f ⊗₁ g) ≈Term decode (f ⊗₁ g)
  decodeP-≈-decode-⊗ f g = decodeP-≈-decode (f ⊗₁ g)

  -- The dispatcher (public interface), wired into `DecodeRelRespIsoWired`:
  --     decode-rel f ≈⟨ decode-rel-≈-decode f ⟩ decode f
  --                  ≈⟨ sym (decodeP-≈-decode f) ⟩ decodeP f
  decode-rel-≈-decodeP
    : ∀ {A B} (f : HomTerm A B) → decode-rel f ≈Term decodeP f
  decode-rel-≈-decodeP f =
    ≈-Term-trans (decode-rel-≈-decode f) (≈-Term-sym (decodeP-≈-decode f))

-- Top-level re-export: the dispatcher as a function of the two K-inputs.
decode-rel-≈-decodeP
  : (objUIP : ∀ {A B : ObjTerm} (p q : A ≡ B) → p ≡ q)
    (K : FaithfulnessResidual)
  → ∀ {A B} (f : HomTerm A B) → decode-rel f ≈Term decodeP f
decode-rel-≈-decodeP objUIP K = Wired.decode-rel-≈-decodeP objUIP K
