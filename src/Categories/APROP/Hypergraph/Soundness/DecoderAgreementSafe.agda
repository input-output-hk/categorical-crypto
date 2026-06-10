{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- `--safe`-clean derivation of
--     decode-rel-≈-decode : ∀ {A B} (f : HomTerm A B) → decode-rel f ≈Term decode f
-- from a record of 11 NARROWER per-constructor assumptions: 9 per-atomic-
-- constructor `bridge-≈-decode-X` fields + 2 shape distributivity fields
-- (`decode-∘-shape`, `decode-⊗-shape`).  The `WithAssumptions` module
-- derives the polymorphic statement by structural induction on `f`.
--
-- DESIGN: each field type is wrapped in an `abstract` type alias.  Without
-- the wrapper, elaborating each per-constructor field TYPE forces Agda to
-- unfold `decode-rel (X)` / `decode (X)` through `decode-attempt-Linear`
-- and the boundary `subst₂` chain, exhausting >14 GB heap across the 11
-- fields.  `abstract` blocks that unfolding during record elaboration and
-- is `--safe`-compatible (it does not postulate anything).
--------------------------------------------------------------------------------

open import Categories.APROP

module Categories.APROP.Hypergraph.Soundness.DecoderAgreementSafe
  (sig : APROPSignature) where

open APROP sig

open import Categories.APROP.Hypergraph.FromAPROP sig
  using (flatten)
open import Categories.APROP.Hypergraph.Soundness.Unflatten sig
  using (unflatten-++-≅)
-- `decode` here is the PRUNED total decoder `decodeP`: every `Ty-X`
-- carrier and the agreement dispatcher are stated over the pruned decoder.
open import Categories.APROP.Hypergraph.Soundness.Discharge.DecodeAttemptLinearP sig
  using () renaming (decodeP to decode)
open import Categories.APROP.Hypergraph.Soundness.DecodeRel sig
  using (decode-rel)

open import Categories.Category using (Category)
open import Categories.Morphism FreeMonoidal using (_≅_)

private
  module FM = Category FreeMonoidal

open FM.HomReasoning

--------------------------------------------------------------------------------
-- `abstract` type aliases for each per-constructor field (see header).

abstract
    Ty-Agen : Set
    Ty-Agen = ∀ {A B} (g : mor A B) → decode-rel (Agen g) ≈Term decode (Agen g)

    Ty-σ : Set
    Ty-σ = ∀ {A B} ⦃ s : Symm ≤ Symm ⦄
          → decode-rel (σ {A = A} {B = B} ⦃ s ⦄)
            ≈Term decode (σ {A = A} {B = B} ⦃ s ⦄)

    Ty-id : Set
    Ty-id = ∀ {A} → decode-rel (id {A}) ≈Term decode (id {A})

    Ty-λ⇒ : Set
    Ty-λ⇒ = ∀ {A} → decode-rel (λ⇒ {A}) ≈Term decode (λ⇒ {A})

    Ty-λ⇐ : Set
    Ty-λ⇐ = ∀ {A} → decode-rel (λ⇐ {A}) ≈Term decode (λ⇐ {A})

    Ty-ρ⇒ : Set
    Ty-ρ⇒ = ∀ {A} → decode-rel (ρ⇒ {A}) ≈Term decode (ρ⇒ {A})

    Ty-ρ⇐ : Set
    Ty-ρ⇐ = ∀ {A} → decode-rel (ρ⇐ {A}) ≈Term decode (ρ⇐ {A})

    Ty-α⇒ : Set
    Ty-α⇒ = ∀ {A B C} → decode-rel (α⇒ {A} {B} {C}) ≈Term decode (α⇒ {A} {B} {C})

    Ty-α⇐ : Set
    Ty-α⇐ = ∀ {A B C} → decode-rel (α⇐ {A} {B} {C}) ≈Term decode (α⇐ {A} {B} {C})

    Ty-∘-shape : Set
    Ty-∘-shape = ∀ {A B C} (g : HomTerm B C) (f : HomTerm A B)
               → decode (g ∘ f) ≈Term decode g ∘ decode f

    Ty-⊗-shape : Set
    Ty-⊗-shape = ∀ {A B C D} (f : HomTerm A B) (g : HomTerm C D)
               → decode (f ⊗₁ g)
                 ≈Term _≅_.to   (unflatten-++-≅ (flatten B) (flatten D))
                      ∘ (decode f ⊗₁ decode g)
                      ∘ _≅_.from (unflatten-++-≅ (flatten A) (flatten C))

    -- "Apply" functions that unwrap the abstract aliases into the
    -- underlying per-constructor type.
    apply-Agen : Ty-Agen
               → ∀ {A B} (g : mor A B)
               → decode-rel (Agen g) ≈Term decode (Agen g)
    apply-Agen t g = t g

    apply-σ : Ty-σ
            → ∀ {A B} ⦃ s : Symm ≤ Symm ⦄
            → decode-rel (σ {A = A} {B = B} ⦃ s ⦄)
              ≈Term decode (σ {A = A} {B = B} ⦃ s ⦄)
    apply-σ t ⦃ s ⦄ = t ⦃ s ⦄

    apply-id : Ty-id → ∀ {A} → decode-rel (id {A}) ≈Term decode (id {A})
    apply-id t = t

    apply-λ⇒ : Ty-λ⇒ → ∀ {A} → decode-rel (λ⇒ {A}) ≈Term decode (λ⇒ {A})
    apply-λ⇒ t = t

    apply-λ⇐ : Ty-λ⇐ → ∀ {A} → decode-rel (λ⇐ {A}) ≈Term decode (λ⇐ {A})
    apply-λ⇐ t = t

    apply-ρ⇒ : Ty-ρ⇒ → ∀ {A} → decode-rel (ρ⇒ {A}) ≈Term decode (ρ⇒ {A})
    apply-ρ⇒ t = t

    apply-ρ⇐ : Ty-ρ⇐ → ∀ {A} → decode-rel (ρ⇐ {A}) ≈Term decode (ρ⇐ {A})
    apply-ρ⇐ t = t

    apply-α⇒ : Ty-α⇒ → ∀ {A B C}
             → decode-rel (α⇒ {A} {B} {C}) ≈Term decode (α⇒ {A} {B} {C})
    apply-α⇒ t = t

    apply-α⇐ : Ty-α⇐ → ∀ {A B C}
             → decode-rel (α⇐ {A} {B} {C}) ≈Term decode (α⇐ {A} {B} {C})
    apply-α⇐ t = t

    apply-∘-shape : Ty-∘-shape → ∀ {A B C} (g : HomTerm B C) (f : HomTerm A B)
                  → decode (g ∘ f) ≈Term decode g ∘ decode f
    apply-∘-shape t g f = t g f

    apply-⊗-shape : Ty-⊗-shape → ∀ {A B C D} (f : HomTerm A B) (g : HomTerm C D)
                  → decode (f ⊗₁ g)
                    ≈Term _≅_.to   (unflatten-++-≅ (flatten B) (flatten D))
                         ∘ (decode f ⊗₁ decode g)
                         ∘ _≅_.from (unflatten-++-≅ (flatten A) (flatten C))
    apply-⊗-shape t f g = t f g

-- "Unapply" functions that pack a natural-typed proof into the opaque
-- `Ty-X` alias.  Public so consumers can lift a constructively-proved
-- natural form into the opaque `Ty-X` carrier.  Packaged inside the same
-- `abstract` block so the type-equation `Ty-X = body` is visible.

abstract
  unapply-Agen
    : (∀ {A B} (g : mor A B) → decode-rel (Agen g) ≈Term decode (Agen g))
    → Ty-Agen
  unapply-Agen t = t

  unapply-σ
    : (∀ {A B} ⦃ s : Symm ≤ Symm ⦄
       → decode-rel (σ {A = A} {B = B} ⦃ s ⦄)
         ≈Term decode (σ {A = A} {B = B} ⦃ s ⦄))
    → Ty-σ
  unapply-σ t ⦃ s ⦄ = t ⦃ s ⦄

  unapply-id
    : (∀ {A} → decode-rel (id {A}) ≈Term decode (id {A}))
    → Ty-id
  unapply-id t = t

  unapply-λ⇒
    : (∀ {A} → decode-rel (λ⇒ {A}) ≈Term decode (λ⇒ {A}))
    → Ty-λ⇒
  unapply-λ⇒ t = t

  unapply-λ⇐
    : (∀ {A} → decode-rel (λ⇐ {A}) ≈Term decode (λ⇐ {A}))
    → Ty-λ⇐
  unapply-λ⇐ t = t

  unapply-ρ⇒
    : (∀ {A} → decode-rel (ρ⇒ {A}) ≈Term decode (ρ⇒ {A}))
    → Ty-ρ⇒
  unapply-ρ⇒ t = t

  unapply-ρ⇐
    : (∀ {A} → decode-rel (ρ⇐ {A}) ≈Term decode (ρ⇐ {A}))
    → Ty-ρ⇐
  unapply-ρ⇐ t = t

  unapply-α⇒
    : (∀ {A B C} → decode-rel (α⇒ {A} {B} {C}) ≈Term decode (α⇒ {A} {B} {C}))
    → Ty-α⇒
  unapply-α⇒ t = t

  unapply-α⇐
    : (∀ {A B C} → decode-rel (α⇐ {A} {B} {C}) ≈Term decode (α⇐ {A} {B} {C}))
    → Ty-α⇐
  unapply-α⇐ t = t

  unapply-∘-shape
    : (∀ {A B C} (g : HomTerm B C) (f : HomTerm A B)
       → decode (g ∘ f) ≈Term decode g ∘ decode f)
    → Ty-∘-shape
  unapply-∘-shape t = t

  unapply-⊗-shape
    : (∀ {A B C D} (f : HomTerm A B) (g : HomTerm C D)
       → decode (f ⊗₁ g)
         ≈Term _≅_.to   (unflatten-++-≅ (flatten B) (flatten D))
              ∘ (decode f ⊗₁ decode g)
              ∘ _≅_.from (unflatten-++-≅ (flatten A) (flatten C)))
    → Ty-⊗-shape
  unapply-⊗-shape t = t

--------------------------------------------------------------------------------
-- The assumptions record: 11 STRICTLY NARROWER fields, one per atomic
-- constructor + 2 distributivity shapes.

record DecoderAgreementAssumptions : Set where
  field
    decode-rel-≈-decode-Agen-T : Ty-Agen
    decode-rel-≈-decode-σ-T    : Ty-σ
    decode-rel-≈-decode-id-T   : Ty-id
    decode-rel-≈-decode-λ⇒-T  : Ty-λ⇒
    decode-rel-≈-decode-λ⇐-T  : Ty-λ⇐
    decode-rel-≈-decode-ρ⇒-T  : Ty-ρ⇒
    decode-rel-≈-decode-ρ⇐-T  : Ty-ρ⇐
    decode-rel-≈-decode-α⇒-T  : Ty-α⇒
    decode-rel-≈-decode-α⇐-T  : Ty-α⇐
    decode-∘-shape-T           : Ty-∘-shape
    decode-⊗-shape-T           : Ty-⊗-shape

--------------------------------------------------------------------------------
-- Constructive derivation of the polymorphic `decode-rel-≈-decode`
-- from the per-constructor assumptions.  Structural induction on `f`.

module WithAssumptions (a : DecoderAgreementAssumptions) where
  open DecoderAgreementAssumptions a

  -- Apply-views of each field (strip the abstract Ty-X wrapper).

  decode-rel-≈-decode-Agen
    : ∀ {A B} (g : mor A B) → decode-rel (Agen g) ≈Term decode (Agen g)
  decode-rel-≈-decode-Agen = apply-Agen decode-rel-≈-decode-Agen-T

  decode-rel-≈-decode-σ
    : ∀ {A B} ⦃ s : Symm ≤ Symm ⦄
    → decode-rel (σ {A = A} {B = B} ⦃ s ⦄)
      ≈Term decode (σ {A = A} {B = B} ⦃ s ⦄)
  decode-rel-≈-decode-σ ⦃ s ⦄ = apply-σ decode-rel-≈-decode-σ-T ⦃ s ⦄

  decode-rel-≈-decode-id
    : ∀ {A} → decode-rel (id {A}) ≈Term decode (id {A})
  decode-rel-≈-decode-id = apply-id decode-rel-≈-decode-id-T

  decode-rel-≈-decode-λ⇒
    : ∀ {A} → decode-rel (λ⇒ {A}) ≈Term decode (λ⇒ {A})
  decode-rel-≈-decode-λ⇒ = apply-λ⇒ decode-rel-≈-decode-λ⇒-T

  decode-rel-≈-decode-λ⇐
    : ∀ {A} → decode-rel (λ⇐ {A}) ≈Term decode (λ⇐ {A})
  decode-rel-≈-decode-λ⇐ = apply-λ⇐ decode-rel-≈-decode-λ⇐-T

  decode-rel-≈-decode-ρ⇒
    : ∀ {A} → decode-rel (ρ⇒ {A}) ≈Term decode (ρ⇒ {A})
  decode-rel-≈-decode-ρ⇒ = apply-ρ⇒ decode-rel-≈-decode-ρ⇒-T

  decode-rel-≈-decode-ρ⇐
    : ∀ {A} → decode-rel (ρ⇐ {A}) ≈Term decode (ρ⇐ {A})
  decode-rel-≈-decode-ρ⇐ = apply-ρ⇐ decode-rel-≈-decode-ρ⇐-T

  decode-rel-≈-decode-α⇒
    : ∀ {A B C} → decode-rel (α⇒ {A} {B} {C}) ≈Term decode (α⇒ {A} {B} {C})
  decode-rel-≈-decode-α⇒ = apply-α⇒ decode-rel-≈-decode-α⇒-T

  decode-rel-≈-decode-α⇐
    : ∀ {A B C} → decode-rel (α⇐ {A} {B} {C}) ≈Term decode (α⇐ {A} {B} {C})
  decode-rel-≈-decode-α⇐ = apply-α⇐ decode-rel-≈-decode-α⇐-T

  decode-∘-shape
    : ∀ {A B C} (g : HomTerm B C) (f : HomTerm A B)
    → decode (g ∘ f) ≈Term decode g ∘ decode f
  decode-∘-shape = apply-∘-shape decode-∘-shape-T

  decode-⊗-shape
    : ∀ {A B C D} (f : HomTerm A B) (g : HomTerm C D)
    → decode (f ⊗₁ g)
    ≈Term _≅_.to   (unflatten-++-≅ (flatten B) (flatten D))
         ∘ (decode f ⊗₁ decode g)
         ∘ _≅_.from (unflatten-++-≅ (flatten A) (flatten C))
  decode-⊗-shape = apply-⊗-shape decode-⊗-shape-T

  -- The main result: `decode-rel-≈-decode` by structural induction.
  decode-rel-≈-decode
    : ∀ {A B} (f : HomTerm A B) → decode-rel f ≈Term decode f
  decode-rel-≈-decode (Agen g)         = decode-rel-≈-decode-Agen g
  decode-rel-≈-decode (σ ⦃ s ⦄)        = decode-rel-≈-decode-σ ⦃ s ⦄
  decode-rel-≈-decode id               = decode-rel-≈-decode-id
  decode-rel-≈-decode λ⇒               = decode-rel-≈-decode-λ⇒
  decode-rel-≈-decode λ⇐               = decode-rel-≈-decode-λ⇐
  decode-rel-≈-decode ρ⇒               = decode-rel-≈-decode-ρ⇒
  decode-rel-≈-decode ρ⇐               = decode-rel-≈-decode-ρ⇐
  decode-rel-≈-decode α⇒               = decode-rel-≈-decode-α⇒
  decode-rel-≈-decode α⇐               = decode-rel-≈-decode-α⇐
  decode-rel-≈-decode (g ∘ f) =
    ≈-Term-trans (∘-resp-≈ (decode-rel-≈-decode g) (decode-rel-≈-decode f))
                 (≈-Term-sym (decode-∘-shape g f))
  decode-rel-≈-decode (_⊗₁_ {A = A} {B = B} {C = C} {D = D} f g) =
    ≈-Term-trans
      (refl⟩∘⟨ ⊗-resp-≈ (decode-rel-≈-decode f) (decode-rel-≈-decode g) ⟩∘⟨refl)
      (≈-Term-sym (decode-⊗-shape f g))

--------------------------------------------------------------------------------
-- All eleven fields of `DecoderAgreementAssumptions` are STRICTLY NARROWER
-- than the polymorphic `decode-rel-≈-decode`: each characterises a specific
-- algorithmic / coherence property at a fixed atomic constructor (Agen, σ,
-- id, the unitors/associators) or a pure distributivity shape (∘, ⊗), so
-- discharging any one does NOT require soundness of the whole algorithm.
-- Consumers instantiate the record from a non-`--safe` `decode-roundtrip`.
--------------------------------------------------------------------------------
