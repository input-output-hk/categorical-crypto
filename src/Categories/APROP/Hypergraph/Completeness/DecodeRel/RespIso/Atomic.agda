{-# OPTIONS #-}

--------------------------------------------------------------------------------
-- Atomic-case dispatcher for `decode-rel-resp-≅ᴴ`.
--
-- An `Atomic` predicate identifies the nine atomic constructors of
-- `HomTerm`: `id, λ⇒, λ⇐, ρ⇒, ρ⇐, α⇒, α⇐, σ, Agen`.  The function
-- `decode-rel-resp-≅ᴴ-atomic` dispatches on the pair of `Atomic`
-- witnesses, routing same-constructor cases to the per-pair lemmas in
-- `RespIso.agda`, cross-pair Agen impossibilities to the absurd
-- helpers, unit-only cross-pairs to `RespIso/UnitCross.agda`, and the
-- Agen-Agen case to `RespIso/AgenAgen.agda`.
--
-- Several non-unit cross-pair cases (id vs σ at non-unit, α⇒/α⇐ vs σ
-- at the A=B=C diagonal) are postulated here, pending Phase 2 of the
-- roadmap (the full ≅ᴴ-respect theorem).  The postulates are local to
-- this module so it's clear which cases remain.
--------------------------------------------------------------------------------

open import Categories.APROP
open import Categories.APROP.Hypergraph.Solver.Signature using (APROPSignatureDec)

module Categories.APROP.Hypergraph.Completeness.DecodeRel.RespIso.Atomic
  (sig-dec : APROPSignatureDec) where

open APROPSignatureDec sig-dec using (sig)
open APROP sig
open import Categories.APROP.Hypergraph.FromAPROP sig using (⟪_⟫)
open import Categories.APROP.Hypergraph.Iso using (_≅ᴴ_)
open import Categories.APROP.Hypergraph.Completeness.DecodeRel sig
  using (decode-rel)

open import Categories.APROP.Hypergraph.Completeness.DecodeRel.RespIso sig
open import Categories.APROP.Hypergraph.Completeness.DecodeRel.RespIso.AgenAgen sig-dec
  using (decode-rel-resp-≅ᴴ-Agen-Agen)
open import Categories.APROP.Hypergraph.Completeness.DecodeRel.RespIso.UnitCross sig
  using ( decode-rel-resp-≅ᴴ-λ⇒-ρ⇒-unit
        ; decode-rel-resp-≅ᴴ-ρ⇒-λ⇒-unit
        ; decode-rel-resp-≅ᴴ-λ⇐-ρ⇐-unit
        ; decode-rel-resp-≅ᴴ-ρ⇐-λ⇐-unit
        ; decode-rel-resp-≅ᴴ-id-σ-unit
        ; decode-rel-resp-≅ᴴ-σ-id-unit
        )
open import Categories.APROP.Hypergraph.Completeness.DecodeRel.RespIso.IdSigma sig
  using ( decode-rel-resp-≅ᴴ-id-σ-general
        ; decode-rel-resp-≅ᴴ-σ-id-general
        )
open import Categories.APROP.Hypergraph.Completeness.DecodeRel.RespIso.AlphaForwardSigma sig
  using ( decode-rel-resp-≅ᴴ-α⇒-σ
        ; decode-rel-resp-≅ᴴ-σ-α⇒
        )
open import Categories.APROP.Hypergraph.Completeness.DecodeRel.RespIso.AlphaBackwardSigma sig
  using ( decode-rel-resp-≅ᴴ-α⇐-σ
        ; decode-rel-resp-≅ᴴ-σ-α⇐
        )

open import Data.Empty using (⊥-elim)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

private
  -- `Symm ≤ Symm` has a unique inhabitant `v≤v`; we use this to
  -- identify two instance arguments in the σ-σ case.
  Symm≤Symm-uniq : (s : Symm ≤ Symm) → s ≡ v≤v
  Symm≤Symm-uniq v≤v = refl

--------------------------------------------------------------------------------
-- The `Atomic` predicate (re-exported from the safe sub-module
-- `RespIso/AtomicData.agda`).

open import Categories.APROP.Hypergraph.Completeness.DecodeRel.RespIso.AtomicData sig public
  using ( Atomic
        ; atomic-Agen; atomic-id
        ; atomic-λ⇒; atomic-λ⇐
        ; atomic-ρ⇒; atomic-ρ⇐
        ; atomic-α⇒; atomic-α⇐
        ; atomic-σ
        )

--------------------------------------------------------------------------------
-- Main dispatcher.  Pattern-matches on the two `Atomic` witnesses,
-- with Agda's coverage checker silently discarding cases whose types
-- fail to unify.  All atomic-vs-atomic cross-pair cases are now
-- discharged by lemmas imported above; no postulates remain in this
-- file.

decode-rel-resp-≅ᴴ-atomic
  : ∀ {A B} {f g : HomTerm A B}
  → Atomic f → Atomic g
  → ⟪ f ⟫ ≅ᴴ ⟪ g ⟫
  → decode-rel f ≈Term decode-rel g

-- ============================================================
-- Same-constructor cases (9): each routes to RespIso.agda.
-- ============================================================
decode-rel-resp-≅ᴴ-atomic (atomic-Agen g₁) (atomic-Agen g₂) iso =
  decode-rel-resp-≅ᴴ-Agen-Agen g₁ g₂ iso
decode-rel-resp-≅ᴴ-atomic atomic-id atomic-id iso =
  decode-rel-resp-≅ᴴ-id-id iso
decode-rel-resp-≅ᴴ-atomic atomic-λ⇒ atomic-λ⇒ iso =
  decode-rel-resp-≅ᴴ-λ⇒-λ⇒ iso
decode-rel-resp-≅ᴴ-atomic atomic-λ⇐ atomic-λ⇐ iso =
  decode-rel-resp-≅ᴴ-λ⇐-λ⇐ iso
decode-rel-resp-≅ᴴ-atomic atomic-ρ⇒ atomic-ρ⇒ iso =
  decode-rel-resp-≅ᴴ-ρ⇒-ρ⇒ iso
decode-rel-resp-≅ᴴ-atomic atomic-ρ⇐ atomic-ρ⇐ iso =
  decode-rel-resp-≅ᴴ-ρ⇐-ρ⇐ iso
decode-rel-resp-≅ᴴ-atomic atomic-α⇒ atomic-α⇒ iso =
  decode-rel-resp-≅ᴴ-α⇒-α⇒ iso
decode-rel-resp-≅ᴴ-atomic atomic-α⇐ atomic-α⇐ iso =
  decode-rel-resp-≅ᴴ-α⇐-α⇐ iso
decode-rel-resp-≅ᴴ-atomic (atomic-σ ⦃ s₁ ⦄) (atomic-σ ⦃ s₂ ⦄) iso
  rewrite Symm≤Symm-uniq s₁ | Symm≤Symm-uniq s₂ =
    decode-rel-resp-≅ᴴ-σ-σ ⦃ v≤v ⦄ iso

-- ============================================================
-- Agen-vs-non-Agen cross-pairs (16): all absurd.
-- ============================================================
decode-rel-resp-≅ᴴ-atomic (atomic-Agen g) atomic-id iso =
  ⊥-elim (decode-rel-resp-≅ᴴ-Agen-id-absurd g iso)
decode-rel-resp-≅ᴴ-atomic atomic-id (atomic-Agen g) iso =
  ⊥-elim (decode-rel-resp-≅ᴴ-id-Agen-absurd g iso)
decode-rel-resp-≅ᴴ-atomic (atomic-Agen g) atomic-λ⇒ iso =
  ⊥-elim (decode-rel-resp-≅ᴴ-Agen-λ⇒-absurd g iso)
decode-rel-resp-≅ᴴ-atomic atomic-λ⇒ (atomic-Agen g) iso =
  ⊥-elim (decode-rel-resp-≅ᴴ-λ⇒-Agen-absurd g iso)
decode-rel-resp-≅ᴴ-atomic (atomic-Agen g) atomic-λ⇐ iso =
  ⊥-elim (decode-rel-resp-≅ᴴ-Agen-λ⇐-absurd g iso)
decode-rel-resp-≅ᴴ-atomic atomic-λ⇐ (atomic-Agen g) iso =
  ⊥-elim (decode-rel-resp-≅ᴴ-λ⇐-Agen-absurd g iso)
decode-rel-resp-≅ᴴ-atomic (atomic-Agen g) atomic-ρ⇒ iso =
  ⊥-elim (decode-rel-resp-≅ᴴ-Agen-ρ⇒-absurd g iso)
decode-rel-resp-≅ᴴ-atomic atomic-ρ⇒ (atomic-Agen g) iso =
  ⊥-elim (decode-rel-resp-≅ᴴ-ρ⇒-Agen-absurd g iso)
decode-rel-resp-≅ᴴ-atomic (atomic-Agen g) atomic-ρ⇐ iso =
  ⊥-elim (decode-rel-resp-≅ᴴ-Agen-ρ⇐-absurd g iso)
decode-rel-resp-≅ᴴ-atomic atomic-ρ⇐ (atomic-Agen g) iso =
  ⊥-elim (decode-rel-resp-≅ᴴ-ρ⇐-Agen-absurd g iso)
decode-rel-resp-≅ᴴ-atomic (atomic-Agen g) atomic-α⇒ iso =
  ⊥-elim (decode-rel-resp-≅ᴴ-Agen-α⇒-absurd g iso)
decode-rel-resp-≅ᴴ-atomic atomic-α⇒ (atomic-Agen g) iso =
  ⊥-elim (decode-rel-resp-≅ᴴ-α⇒-Agen-absurd g iso)
decode-rel-resp-≅ᴴ-atomic (atomic-Agen g) atomic-α⇐ iso =
  ⊥-elim (decode-rel-resp-≅ᴴ-Agen-α⇐-absurd g iso)
decode-rel-resp-≅ᴴ-atomic atomic-α⇐ (atomic-Agen g) iso =
  ⊥-elim (decode-rel-resp-≅ᴴ-α⇐-Agen-absurd g iso)
decode-rel-resp-≅ᴴ-atomic (atomic-Agen g) (atomic-σ ⦃ s ⦄) iso =
  ⊥-elim (decode-rel-resp-≅ᴴ-Agen-σ-absurd ⦃ s ⦄ g iso)
decode-rel-resp-≅ᴴ-atomic (atomic-σ ⦃ s ⦄) (atomic-Agen g) iso =
  ⊥-elim (decode-rel-resp-≅ᴴ-σ-Agen-absurd ⦃ s ⦄ g iso)

-- ============================================================
-- Cross-pair cases that unify only at A = unit.
-- ============================================================
decode-rel-resp-≅ᴴ-atomic atomic-λ⇒ atomic-ρ⇒ iso =
  decode-rel-resp-≅ᴴ-λ⇒-ρ⇒-unit iso
decode-rel-resp-≅ᴴ-atomic atomic-ρ⇒ atomic-λ⇒ iso =
  decode-rel-resp-≅ᴴ-ρ⇒-λ⇒-unit iso
decode-rel-resp-≅ᴴ-atomic atomic-λ⇐ atomic-ρ⇐ iso =
  decode-rel-resp-≅ᴴ-λ⇐-ρ⇐-unit iso
decode-rel-resp-≅ᴴ-atomic atomic-ρ⇐ atomic-λ⇐ iso =
  decode-rel-resp-≅ᴴ-ρ⇐-λ⇐-unit iso

-- ============================================================
-- Cross-pair cases requiring the general (postulated) lemmas.
-- ============================================================
decode-rel-resp-≅ᴴ-atomic atomic-id (atomic-σ ⦃ s ⦄) iso =
  decode-rel-resp-≅ᴴ-id-σ-general ⦃ s ⦄ iso
decode-rel-resp-≅ᴴ-atomic (atomic-σ ⦃ s ⦄) atomic-id iso =
  decode-rel-resp-≅ᴴ-σ-id-general ⦃ s ⦄ iso
decode-rel-resp-≅ᴴ-atomic atomic-α⇒ (atomic-σ ⦃ s ⦄) iso =
  decode-rel-resp-≅ᴴ-α⇒-σ ⦃ s ⦄ iso
decode-rel-resp-≅ᴴ-atomic (atomic-σ ⦃ s ⦄) atomic-α⇒ iso =
  decode-rel-resp-≅ᴴ-σ-α⇒ ⦃ s ⦄ iso
decode-rel-resp-≅ᴴ-atomic atomic-α⇐ (atomic-σ ⦃ s ⦄) iso =
  decode-rel-resp-≅ᴴ-α⇐-σ ⦃ s ⦄ iso
decode-rel-resp-≅ᴴ-atomic (atomic-σ ⦃ s ⦄) atomic-α⇐ iso =
  decode-rel-resp-≅ᴴ-σ-α⇐ ⦃ s ⦄ iso

-- All other cross-pair combinations (e.g., `λ⇒ vs λ⇐`, `α⇒ vs α⇐`,
-- `id vs λ⇒`, …) are type-impossible: their HomTerm sources/targets
-- fail to unify under ObjTerm constructor injectivity.  Agda's
-- coverage checker discards them silently.
