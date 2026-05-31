{-# OPTIONS --safe --with-K #-}

--------------------------------------------------------------------------------
-- `--safe`-clean derivation of `decode-rel-≈-decode` from per-constructor
-- assumptions.
--
-- This file provides a constructive structural-induction derivation of
--
--     decode-rel-≈-decode
--       : ∀ {A B} (f : HomTerm A B) → decode-rel f ≈Term decode f
--
-- from a record of NARROWER per-constructor assumptions:
--
--   * 9 per-atomic-constructor `bridge-≈-decode-X` fields (Agen, σ, id,
--     λ⇒, λ⇐, ρ⇒, ρ⇐, α⇒, α⇐).
--   * 2 shape distributivity fields (`decode-∘-shape`, `decode-⊗-shape`).
--
-- Pattern matches `CompletenessAssumptions` in `DecodeRespIso.agda`:
-- record-of-assumptions + a `WithAssumptions` module that
-- constructively derives the high-level statement.
--
-- ## How this composes with `DecodeRespIso.CompletenessAssumptions`
--
-- A consumer wanting maximally fine-grained trust can:
--
--   1. Postulate `DecoderAgreementSafe.DecoderAgreementAssumptions`
--      (11 narrower fields).
--   2. Open `WithAssumptions a` to get `decode-rel-≈-decode`
--      (the polymorphic version).
--   3. Combine with the 4 algorithmic-decoder fields to construct
--      `DecodeRespIso.CompletenessAssumptions`.
--
-- Alternatively, a consumer can postulate
-- `DecodeRespIso.CompletenessAssumptions` directly (5 coarser fields),
-- as `Solver/TestsTrust.agda` currently does.
--
-- ## Why per-constructor fields require `abstract` wrappers.
--
-- A naive per-constructor split (each field directly typed as
-- `decode-rel (X) ≈Term decode (X)`) causes Agda's type-checker to
-- exhaust >14 GB heap during the `WithAssumptions` derivation.  Root
-- cause: each per-constructor record-field TYPE forces Agda to
-- elaborate `decode-rel (X)` and `decode (X)`, which recursively
-- expand through `decode-attempt-Linear` / `decode-attempt-h*` and
-- the boundary `subst₂` chain.  Multiplied across 11 fields, the
-- unification workload explodes.
--
-- Wrapping each field type in an `abstract` type alias prevents Agda
-- from unfolding the algorithmic side during record elaboration,
-- keeping memory consumption manageable (compiles in <8 GB).
--
-- This is `--safe`-compatible: `abstract` definitions are allowed in
-- `--safe` mode (they only opaque-ify; they don't postulate anything).
--
-- ## Constructive content.
--
-- The body of `decode-rel-≈-decode` in `WithAssumptions` is a
-- structural induction on `f`:
--
--   * Atomic constructors: directly invoke the corresponding
--     `bridge-≈-decode-X` field.
--   * `∘` and `⊗`: structural recursion with IHs, using the
--     definitional `decode-rel-{∘,⊗}-shape` (refl per `DecodeRel.agda`)
--     and the `decode-{∘,⊗}-shape` fields for the algorithmic side.
--
-- All 11 fields are STRICTLY NARROWER than the original polymorphic
-- `decode-rel-≈-decode` (each is at a fixed atomic constructor or
-- pure distributivity statement).
--------------------------------------------------------------------------------

open import Categories.APROP

module Categories.APROP.Hypergraph.Completeness.DecoderAgreementSafe
  (sig : APROPSignature) where

open APROP sig

open import Categories.APROP.Hypergraph.FromAPROP sig
  using (flatten)
open import Categories.APROP.Hypergraph.Completeness.Unflatten sig
  using (unflatten-++-≅)
open import Categories.APROP.Hypergraph.Completeness.DecodeAttempt sig
  using (decode)
open import Categories.APROP.Hypergraph.Completeness.DecodeRel sig
  using (decode-rel)

open import Categories.Category using (Category)
open import Categories.Morphism FreeMonoidal using (_≅_)

private
  module FM = Category FreeMonoidal

open FM.HomReasoning

--------------------------------------------------------------------------------
-- `abstract` type aliases for each per-constructor field.  Prevents
-- Agda from unfolding `decode-rel (X)` / `decode (X)` during record
-- elaboration, keeping memory consumption manageable.

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

    -- "Apply" functions that unwrap the abstract aliases.  Needed
    -- because consumer pattern-match on `f` and want a concrete term,
    -- not the opaque Type alias.
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
-- `Ty-X` alias.  Public (not in the `private` block) so consumer
-- modules can construct values of the opaque `Ty-X` carrier — from
-- outside `Ty-X` is opaque, so a consumer who has constructively proved
-- the natural form invokes `unapply-X` to lift it into `Ty-X`.
-- Implementation: identity wrapper at the underlying type, packaged
-- inside the same `abstract` block so the type-equation `Ty-X = body`
-- is visible.

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

  -- Apply-views of each field.  The `apply-X` functions strip the
  -- abstract Ty-X wrapper, yielding usable per-constructor lemmas.

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
  -- ∘ case: definitional `decode-rel-∘-shape` (refl) + IHs + `decode-∘-shape`.
  decode-rel-≈-decode (g ∘ f) =
    ≈-Term-trans (∘-resp-≈ (decode-rel-≈-decode g) (decode-rel-≈-decode f))
                 (≈-Term-sym (decode-∘-shape g f))
  -- ⊗ case: definitional `decode-rel-⊗-shape` (refl) + IHs + `decode-⊗-shape`.
  decode-rel-≈-decode (_⊗₁_ {A = A} {B = B} {C = C} {D = D} f g) =
    ≈-Term-trans
      (refl⟩∘⟨ ⊗-resp-≈ (decode-rel-≈-decode f) (decode-rel-≈-decode g) ⟩∘⟨refl)
      (≈-Term-sym (decode-⊗-shape f g))

--------------------------------------------------------------------------------
-- ## Postulate inventory (record fields) and discharge status.
--
-- All ELEVEN fields of `DecoderAgreementAssumptions` are STRICTLY
-- NARROWER than the original polymorphic `decode-rel-≈-decode`.
--
-- 1. SINGLE-EDGE ATOMIC LEVEL (Agen, σ):
--    `decode-rel-≈-decode-Agen-T`, `decode-rel-≈-decode-σ-T`.
--
--    These mirror the still-open `decode-roundtrip-{Agen,σ}` in
--    `DecodeRoundtrip.agda`.  Discharge requires unfolding
--    `decode-attempt-h{Gen,Swap}` against the boundary subst₂ from
--    `⟪⟫-{dom,cod}L`.  The boundary equations are non-trivial
--    `trans` chains, so the `subst₂` does not collapse to `refl`.
--    Estimated ~150 LOC per case.
--
-- 2. ID / ID-COERCION LEVEL (id, λ⇒, λ⇐, ρ⇒, ρ⇐, α⇒, α⇐):
--    `decode-rel-≈-decode-{id,λ⇒,λ⇐,ρ⇒,ρ⇐,α⇒,α⇐}-T`.
--
--    All seven are CONSTRUCTIVELY DISCHARGEABLE from the existing
--    `decode-id-is-id` / `bridge-X-is-id` / `X-coherence` lemmas in
--    `DecodeRoundtrip.agda`, modulo:
--
--      * `decode-⊗-shape` (also a field here, postulated downstream) —
--        needed for the inductive `A ⊗₀ B` case of `decode-id-is-id`.
--      * `decode-{ρ⇒,ρ⇐,α⇒,α⇐}-shape` (postulated in DecodeRoundtrip) —
--        needed for boundary-subst₂ peeling.
--      * `bridge-α⇒-form-⊗-⊗` (postulated) — α-form coherence
--        recursive case.
--      * `c-iso-assoc-from-cons` (postulated) — c-iso pentagon
--        cons case.
--
--    Inlining + discharge estimated ~1000 LOC total.
--
-- 3. DISTRIBUTIVITY LEVEL (∘, ⊗):
--    `decode-∘-shape-T`, `decode-⊗-shape-T`.
--
--    Both mirror the corresponding postulates in `DecodeRoundtrip.agda`.
--    Discharge requires characterising how `decode-attempt-h{Compose,
--    Tensor}` decompose into sub-hypergraph contributions.  Proof
--    outline is sketched in `DecodeRoundtrip.agda`'s Cluster C
--    comments.  Estimated ~300 LOC total.
--
-- All eleven fields are STRUCTURAL — they characterise specific
-- algorithmic / coherence properties, NOT the polymorphic
-- decode-vs-decode-rel agreement.  Discharging any one does NOT
-- require completeness of the whole algorithm.
--
-- ## Surprises and insights.
--
-- 1. `decode-rel f ≈ bridge f` is FULLY CONSTRUCTIVE (proved as
--    `decode-roundtrip-rel` in `DecodeRel.agda`).  The asymmetry is
--    because `decode-rel`'s atomic cases are DEFINED to BE `bridge X`,
--    so the atomic cases reduce to `≈-Term-refl`.
--
-- 2. The bottleneck for the `bridge f ≈ decode f` direction is the
--    boundary `subst₂` of `decode`: the `cong unflatten (⟪⟫-{dom,cod}L f)`
--    coercions don't reduce to `refl` for atomic constructors except
--    `id {unit}` and `id {Var x}`.  Each non-trivial atomic case
--    requires a per-constructor coherence chain.
--
-- 3. SURPRISE: Agda's memory consumption for direct per-constructor
--    record-field types blows up to >14 GB.  Mitigated by wrapping
--    each field type in an `abstract` alias, which prevents
--    record-creation-time expansion of the algorithmic side.
--
-- 4. The `--safe` constraint precludes raw postulates, but the
--    record-of-assumptions pattern (with `abstract` typing) preserves
--    modularity AND breaks the postulate into 11 narrower pieces.
--    Consumers instantiate the record from a non-`--safe`
--    `decode-roundtrip` instance.
--------------------------------------------------------------------------------
