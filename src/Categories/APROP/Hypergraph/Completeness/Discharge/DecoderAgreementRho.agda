{-# OPTIONS --safe --with-K #-}

--------------------------------------------------------------------------------
-- Discharge of `Ty-ρ⇒` and `Ty-ρ⇐` (two `DecoderAgreementAssumptions`
-- fields) from `Ty-⊗-shape` plus a residual record `RhoShapeResidual` of
-- two shape-equations.
--
-- For X ∈ {ρ⇒, ρ⇐}, `decode-rel (X {A}) = bridge (X {A})` definitionally,
-- so `decode-rel X ≈Term decode X` reduces to `bridge X ≈Term decode X`,
-- closed by the 3-step chain
--
--   decode (ρ⇒ {A})
--     ≈⟨ decode-ρ⇒-shape A ⟩          -- residual
--   subst₂ … (decode (id {A ⊗₀ unit}))
--     ≈⟨ subst₂-resp-≈Term … (decode-id-is-id …) ⟩
--   subst₂ … id
--     ≈⟨ ρ⇒-coherence A ⟩
--   bridge (ρ⇒ {A}).
--
-- `decode-id-is-id` is reused from `DecoderAgreementCases.FromShape t⊗`.
--------------------------------------------------------------------------------

open import Categories.APROP

module Categories.APROP.Hypergraph.Completeness.Discharge.DecoderAgreementRho
  (sig : APROPSignature) where

open APROP sig

open import Categories.APROP.Hypergraph.FromAPROP sig
  using (flatten)
open import Categories.APROP.Hypergraph.Completeness.Unflatten sig
  using (unflatten)
open import Categories.APROP.Hypergraph.Completeness.DecodeAttempt sig
  using (decode; bridge)
open import Categories.APROP.Hypergraph.Completeness.DecodeRel sig
  using (decode-rel)
open import Categories.APROP.Hypergraph.Completeness.DecoderAgreementSafe sig
  using ( Ty-⊗-shape
        ; Ty-ρ⇒; Ty-ρ⇐
        ; unapply-ρ⇒; unapply-ρ⇐
        )
open import Categories.APROP.Hypergraph.Completeness.DecodeRoundtripSafe sig
  using ( ≡⇒≈Term
        ; subst₂-resp-≈Term
        ; ρ⇒-coherence
        ; ρ⇐-coherence
        )
import Categories.APROP.Hypergraph.Completeness.Discharge.DecoderAgreementCases as Cases
module Cases-sig = Cases sig

open import Categories.Category using (Category)

open import Data.List.Properties using (++-identityʳ)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; subst₂)

private
  module FM = Category FreeMonoidal

open FM.HomReasoning

--------------------------------------------------------------------------------
-- ## Residual: the two `decode-X-shape` propositional equations.
--
-- Each characterises how `decode (X)` factors through a boundary `subst₂`
-- over `++-identityʳ (flatten A)`, with `decode (id {A ⊗₀ unit})` as the
-- inner term.

record RhoShapeResidual : Set where
  field
    decode-ρ⇒-shape
      : ∀ A → decode (ρ⇒ {A})
           ≡ subst₂ HomTerm refl (cong unflatten (++-identityʳ (flatten A)))
                    (decode (id {A ⊗₀ unit}))
    decode-ρ⇐-shape
      : ∀ A → decode (ρ⇐ {A})
           ≡ subst₂ HomTerm (cong unflatten (++-identityʳ (flatten A))) refl
                    (decode (id {A ⊗₀ unit}))

--------------------------------------------------------------------------------
-- ## `FromShape t⊗ rsr`: derive `Ty-ρ⇒` and `Ty-ρ⇐`.

module FromShape (t⊗ : Ty-⊗-shape) (rsr : RhoShapeResidual) where

  open RhoShapeResidual rsr
  open Cases-sig.FromShape t⊗ using (decode-id-is-id)

  bridge-ρ⇒-≈-decode : ∀ A → bridge (ρ⇒ {A}) ≈Term decode (ρ⇒ {A})
  bridge-ρ⇒-≈-decode A = begin
    bridge (ρ⇒ {A})
      ≈⟨ ρ⇒-coherence A ⟨
    subst₂ HomTerm refl (cong unflatten (++-identityʳ (flatten A))) id
      ≈⟨ subst₂-resp-≈Term refl (++-identityʳ (flatten A))
                            (decode-id-is-id (A ⊗₀ unit)) ⟨
    subst₂ HomTerm refl (cong unflatten (++-identityʳ (flatten A)))
                         (decode (id {A ⊗₀ unit}))
      ≈⟨ ≡⇒≈Term (decode-ρ⇒-shape A) ⟨
    decode (ρ⇒ {A}) ∎

  bridge-ρ⇐-≈-decode : ∀ A → bridge (ρ⇐ {A}) ≈Term decode (ρ⇐ {A})
  bridge-ρ⇐-≈-decode A = begin
    bridge (ρ⇐ {A})
      ≈⟨ ρ⇐-coherence A ⟨
    subst₂ HomTerm (cong unflatten (++-identityʳ (flatten A))) refl id
      ≈⟨ subst₂-resp-≈Term (++-identityʳ (flatten A)) refl
                            (decode-id-is-id (A ⊗₀ unit)) ⟨
    subst₂ HomTerm (cong unflatten (++-identityʳ (flatten A))) refl
                         (decode (id {A ⊗₀ unit}))
      ≈⟨ ≡⇒≈Term (decode-ρ⇐-shape A) ⟨
    decode (ρ⇐ {A}) ∎

  -- The two closed `Ty-X` values.  `decode-rel (X {A}) = bridge (X {A})`
  -- definitionally, so `bridge-X-≈-decode A` has the required type.

  ty-ρ⇒ : Ty-ρ⇒
  ty-ρ⇒ = unapply-ρ⇒ (λ {A} → bridge-ρ⇒-≈-decode A)

  ty-ρ⇐ : Ty-ρ⇐
  ty-ρ⇐ = unapply-ρ⇐ (λ {A} → bridge-ρ⇐-≈-decode A)
