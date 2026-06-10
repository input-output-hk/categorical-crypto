{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- Structural ↔ pruned-algorithmic decoder agreement: proves
--   decode-rel f ≈Term decodeP f
-- DIRECTLY, without routing through the unpruned `decode` ∘-machinery.
-- Uses ONLY:
--   * the atomic collapses (DAS) `decode X ≈ bridge X`, retyped to
--     `decodeP X` via the definitional equality `decodeP X ≡ decode X` on
--     atomic constructors (pruning only changes `∘`);
--   * the unitor object-induction (`Cases.FromShape`/`Rho.FromShape`),
--     which uses the unpruned ⊗-shape (DTS), which is retained anyway
--     (reused by the pruned tensor `DecodeTensorPruned`);
--   * the pruned shape lemmas DCP / DTP for the recursive `∘` / `⊗` cases.
--
-- It deliberately does NOT import DecodeComposeShape (the unpruned ∘-shape)
-- and does NOT build the unpruned `decode-rel-≈-decode` dispatcher or the
-- `ProcessEdgesTermShape.Assemble` bridge: the direct route makes that
-- whole unpruned middle hop dead (see docs/size-reduction-strategies.md,
-- Lever 2).
--------------------------------------------------------------------------------

open import Categories.APROP

open import Relation.Binary using (DecidableEquality)

module Categories.APROP.Hypergraph.Soundness.Discharge.DecodeRelDecodeP
  (sig : APROPSignature)
  (_≟X_ : DecidableEquality (APROPSignature.X sig)) where

open APROP sig

open import Categories.APROP.Hypergraph.FromAPROP sig
  using (flatten; domL-hId; codL-hId)
open import Categories.APROP.Hypergraph.Soundness.Unflatten sig
  using (unflatten; unflatten-++-≅; _≅_)
open import Categories.APROP.Hypergraph.Translation sig
  using (⟪⟫-domL; ⟪⟫-codL)
open import Categories.APROP.Hypergraph.Soundness.DecodeRel sig
  using (decode-rel)
open import Categories.APROP.Hypergraph.Soundness.Discharge.DecodeAttemptLinearP sig
  using (decode-attempt-LinearP)

open import Categories.APROP.Hypergraph.Soundness.DecodeAttempt sig
  using (decode; bridge; decode-attempt-hId)

open import Categories.APROP.Hypergraph.Soundness.DecoderAgreementSafe sig
  using ( Ty-⊗-shape; unapply-⊗-shape; apply-⊗-shape )

-- The UNPRUNED ⊗-shape (DTS) — STAYS (reused by the pruned tensor DTP);
-- needed here for the unitor object-induction.
import Categories.APROP.Hypergraph.Soundness.Discharge.Sub.DecodeTensorShape sig _≟X_ as DTS
-- The PRUNED shape lemmas (∘-side, ⊗-side).
import Categories.APROP.Hypergraph.Soundness.Discharge.Sub.DecodeComposePruned sig as DCP
import Categories.APROP.Hypergraph.Soundness.Discharge.Sub.DecodeTensorPruned sig _≟X_ as DTP
-- The single-edge collapses `decode-{Agen,σ,α⇒,α⇐}-collapse`.
import Categories.APROP.Hypergraph.Soundness.Discharge.Sub.DecodeAgenSigmaShape sig _≟X_ as DAS
-- The unitor (id/λ⇒/λ⇐) + ρ object-inductions.
import Categories.APROP.Hypergraph.Soundness.Discharge.DecoderAgreementCases as Cases
module Cases-sig = Cases sig
import Categories.APROP.Hypergraph.Soundness.Discharge.DecoderAgreementRho as Rho
module Rho-sig = Rho sig
open Rho-sig using (RhoShapeResidual)
open import Categories.APROP.Hypergraph.Soundness.Discharge.Sub.HomTermTransport sig
  using (subst₂-cod-trans; subst₂-dom-trans)

open import Categories.Category using (Category)
open import Data.Product using (proj₁)
open import Data.List using (List)
open import Data.List.Properties using (++-identityʳ)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; trans; cong; subst₂)

open import Categories.PermuteCoherence.Faithfulness asFreeMonoidalData
  using (FaithfulnessResidual)

--------------------------------------------------------------------------------
-- The pruned decoder `decodeP`.
decodeP : ∀ {A B} (f : HomTerm A B)
        → HomTerm (unflatten (flatten A)) (unflatten (flatten B))
decodeP {A} {B} f =
  subst₂ HomTerm (cong unflatten (⟪⟫-domL f)) (cong unflatten (⟪⟫-codL f))
         (proj₁ (decode-attempt-LinearP f))

private
  module FM = Category FreeMonoidal

--------------------------------------------------------------------------------
-- The `ρ`-shape residual (pure boundary-subst₂ algebra; references `decode`,
-- never unpruned `∘`).
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
-- The DIRECT dispatcher.

module Wired
  (objUIP : ∀ {A B : ObjTerm} (p q : A ≡ B) → p ≡ q)
  (K : FaithfulnessResidual)
  where

  -- The UNPRUNED ⊗-shape, packed into the opaque `Ty-⊗-shape` carrier.
  -- This is the ONLY unpruned shape consumed (for the unitor inductions).
  ty-⊗-shape : Ty-⊗-shape
  ty-⊗-shape =
    unapply-⊗-shape (λ {A} {B} {C} {D} f g → DTS.decode-⊗-shape-inner objUIP K f g)

  -- View of the unpruned ⊗-shape at the natural type.
  decode-⊗-shape
    : ∀ {A B C D} (f : HomTerm A B) (g : HomTerm C D)
    → decode (f ⊗₁ g)
    ≈Term _≅_.to   (unflatten-++-≅ (flatten B) (flatten D))
         ∘ (decode f ⊗₁ decode g)
         ∘ _≅_.from (unflatten-++-≅ (flatten A) (flatten C))
  decode-⊗-shape = apply-⊗-shape ty-⊗-shape

  module CasesShape = Cases-sig.FromShape ty-⊗-shape
  module RhoShape   = Rho-sig.FromShape ty-⊗-shape rhoShapeResidual

  -- Atomic agreements (decode-rel X ≈Term decode X).  decode-rel X = bridge X
  -- definitionally, so each is `≈-Term-sym` of the collapse / the FromShape
  -- view.
  drd-Agen : ∀ {A B} (g : mor A B) → decode-rel (Agen g) ≈Term decode (Agen g)
  drd-Agen g = ≈-Term-sym (DAS.decode-Agen-collapse objUIP K g)

  drd-σ : ∀ {A B} ⦃ s : Symm ≤ Symm ⦄
        → decode-rel (σ {A = A} {B = B} ⦃ s ⦄) ≈Term decode (σ {A = A} {B = B} ⦃ s ⦄)
  drd-σ ⦃ s ⦄ = ≈-Term-sym (DAS.decode-σ-collapse objUIP K ⦃ s ⦄)

  drd-α⇒ : ∀ {A B C} → decode-rel (α⇒ {A} {B} {C}) ≈Term decode (α⇒ {A} {B} {C})
  drd-α⇒ {A} {B} {C} = ≈-Term-sym (DAS.decode-α⇒-collapse objUIP K {A} {B} {C})

  drd-α⇐ : ∀ {A B C} → decode-rel (α⇐ {A} {B} {C}) ≈Term decode (α⇐ {A} {B} {C})
  drd-α⇐ {A} {B} {C} = ≈-Term-sym (DAS.decode-α⇐-collapse objUIP K {A} {B} {C})

  -- The unitor agreements, via the (unpruned) FromShape views.  These views
  -- already produce `decode-rel X ≈Term decode X` (the field type stripped of
  -- the abstract Ty-X carrier is exactly that).
  open import Categories.APROP.Hypergraph.Soundness.DecoderAgreementSafe sig
    using ( apply-id; apply-λ⇒; apply-λ⇐; apply-ρ⇒; apply-ρ⇐ )

  drd-id : ∀ {A} → decode-rel (id {A}) ≈Term decode (id {A})
  drd-id = apply-id CasesShape.ty-id

  drd-λ⇒ : ∀ {A} → decode-rel (λ⇒ {A}) ≈Term decode (λ⇒ {A})
  drd-λ⇒ = apply-λ⇒ CasesShape.ty-λ⇒

  drd-λ⇐ : ∀ {A} → decode-rel (λ⇐ {A}) ≈Term decode (λ⇐ {A})
  drd-λ⇐ = apply-λ⇐ CasesShape.ty-λ⇐

  drd-ρ⇒ : ∀ {A} → decode-rel (ρ⇒ {A}) ≈Term decode (ρ⇒ {A})
  drd-ρ⇒ = apply-ρ⇒ RhoShape.ty-ρ⇒

  drd-ρ⇐ : ∀ {A} → decode-rel (ρ⇐ {A}) ≈Term decode (ρ⇐ {A})
  drd-ρ⇐ = apply-ρ⇐ RhoShape.ty-ρ⇐

  -- Pruned shape lemma views.
  decodeP-∘-shape
    : ∀ {A B C} (g : HomTerm B C) (f : HomTerm A B)
    → decodeP (g ∘ f) ≈Term decodeP g ∘ decodeP f
  decodeP-∘-shape g f = DCP.decodeP-∘-shape objUIP K g f

  decodeP-⊗-shape
    : ∀ {A B C D} (f : HomTerm A B) (g : HomTerm C D)
    → decodeP (f ⊗₁ g)
    ≈Term _≅_.to   (unflatten-++-≅ (flatten B) (flatten D))
         ∘ (decodeP f ⊗₁ decodeP g)
         ∘ _≅_.from (unflatten-++-≅ (flatten A) (flatten C))
  decodeP-⊗-shape f g = DTP.decodeP-⊗-shape objUIP K f g

  -- The DIRECT dispatcher.  Atomic: retype the `decode-rel X ≈ decode X`
  -- agreement to `decodeP X` via the DEFINITIONAL `decodeP X ≡ decode X`
  -- (verified `refl` below for every atomic — so `decode X` and `decodeP X`
  -- are the same term and the agreement typechecks at the `decodeP X` type).
  --
  -- Recursive: use ONLY the pruned shapes + decode-rel's definitional shape.
  decode-rel-≈-decodeP
    : ∀ {A B} (f : HomTerm A B) → decode-rel f ≈Term decodeP f
  decode-rel-≈-decodeP (Agen g)  = drd-Agen g
  decode-rel-≈-decodeP (σ ⦃ s ⦄) = drd-σ ⦃ s ⦄
  decode-rel-≈-decodeP id        = drd-id
  decode-rel-≈-decodeP λ⇒        = drd-λ⇒
  decode-rel-≈-decodeP λ⇐        = drd-λ⇐
  decode-rel-≈-decodeP ρ⇒        = drd-ρ⇒
  decode-rel-≈-decodeP ρ⇐        = drd-ρ⇐
  decode-rel-≈-decodeP α⇒        = drd-α⇒
  decode-rel-≈-decodeP α⇐        = drd-α⇐
  decode-rel-≈-decodeP (g ∘ f)   =
    -- decode-rel (g∘f) = decode-rel g ∘ decode-rel f      (def)
    --   ≈⟨ ∘-resp-≈ (IH g)(IH f) ⟩ decodeP g ∘ decodeP f
    --   ≈⟨ sym (decodeP-∘-shape) ⟩ decodeP (g∘f)
    ≈-Term-trans
      (∘-resp-≈ (decode-rel-≈-decodeP g) (decode-rel-≈-decodeP f))
      (≈-Term-sym (decodeP-∘-shape g f))
  decode-rel-≈-decodeP (_⊗₁_ {A = A} {B = B} {C = C} {D = D} f g) =
    -- decode-rel (f⊗g) = to ∘ (decode-rel f ⊗ decode-rel g) ∘ from   (def)
    --   ≈⟨ frame (IH f)(IH g) ⟩ to ∘ (decodeP f ⊗ decodeP g) ∘ from
    --   ≈⟨ sym (decodeP-⊗-shape) ⟩ decodeP (f⊗g)
    ≈-Term-trans
      (∘-resp-≈ ≈-Term-refl
        (∘-resp-≈ (⊗-resp-≈ (decode-rel-≈-decodeP f) (decode-rel-≈-decodeP g))
                  ≈-Term-refl))
      (≈-Term-sym (decodeP-⊗-shape f g))

--------------------------------------------------------------------------------
-- Top-level re-export.
decode-rel-≈-decodeP
  : (objUIP : ∀ {A B : ObjTerm} (p q : A ≡ B) → p ≡ q)
    (K : FaithfulnessResidual)
  → ∀ {A B} (f : HomTerm A B) → decode-rel f ≈Term decodeP f
decode-rel-≈-decodeP objUIP K = Wired.decode-rel-≈-decodeP objUIP K
