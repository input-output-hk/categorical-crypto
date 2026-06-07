{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- Constructing `DecoderAgreementAssumptions` per-constructor fields.
-- See `DecoderAgreementSafe.agda` for the assumptions record.
--
-- Each field is an abstract type alias `Ty-X`; a value is built from a
-- proof at the natural type (`∀ … → decode-rel X ≈Term decode X`) wrapped
-- via the corresponding `unapply-X` helper.
--
-- `FromShape` (below): given a `Ty-⊗-shape` witness, produces `Ty-id`,
-- `Ty-λ⇒`, `Ty-λ⇐` polymorphically in `A` — the `A ⊗₀ B` case routes
-- through the `⊗`-shape witness; the `Var`/`unit` leaves close directly.
-- The `⊗`-shape witness is thus the load-bearing input.
--------------------------------------------------------------------------------

open import Categories.APROP

module Categories.APROP.Hypergraph.Soundness.Discharge.DecoderAgreementCases
  (sig : APROPSignature) where

open APROP sig

open import Categories.APROP.Hypergraph.Soundness.DecoderAgreementSafe sig
open import Categories.APROP.Hypergraph.Soundness.DecodeAttempt sig
  using (decode; bridge)
open import Categories.APROP.Hypergraph.Soundness.DecodeRel sig
  using (decode-rel)

open import Categories.Category using (Category)

private
  module FM = Category FreeMonoidal

open FM.HomReasoning

-- Common pattern: `decode-rel X = bridge X` definitionally, so each case
-- reduces to `bridge X ≈Term decode X`; the `bridge X` side reduces
-- structurally while the `decode X` side stalls on the `permute-via-vlab`
-- outputs (vlab functions Agda's reducer cannot evaluate).

open import Categories.APROP.Hypergraph.Soundness.Unflatten sig
  using (unflatten; unflatten-flatten-≈; unflatten-++-≅)
open import Categories.APROP.Hypergraph.FromAPROP sig
  using (flatten)
open import Categories.Morphism FreeMonoidal using (_≅_)

open import Categories.APROP.Hypergraph.Soundness.DecodeRoundtripSafe sig
  using ( bridge-id-is-id
        ; bridge-λ⇒-is-id
        ; bridge-λ⇐-is-id
        ; decode-id-is-id-unit
        ; decode-id-is-id-Var
        )

--------------------------------------------------------------------------------
-- `FromShape`: given a `Ty-⊗-shape` assumption, derive the polymorphic
-- `Ty-id`, `Ty-λ⇒`, `Ty-λ⇐` values.  The construction factors through a
-- polymorphic `decode-id-is-id` proven by induction on `A`: the imported
-- `unit`/`Var x` base cases plus `Ty-⊗-shape` for the `A ⊗₀ B` step.

module FromShape (t⊗ : Ty-⊗-shape) where

  private
    _decode-⊗-shape_
      : ∀ {A B C D} (f : HomTerm A B) (g : HomTerm C D)
      → decode (f ⊗₁ g)
        ≈Term _≅_.to   (unflatten-++-≅ (flatten B) (flatten D))
             ∘ (decode f ⊗₁ decode g)
             ∘ _≅_.from (unflatten-++-≅ (flatten A) (flatten C))
    _decode-⊗-shape_ = apply-⊗-shape t⊗

  decode-id-is-id : ∀ A → decode (id {A}) ≈Term id
  decode-id-is-id unit       = decode-id-is-id-unit
  decode-id-is-id (Var x)    = decode-id-is-id-Var x
  decode-id-is-id (A ⊗₀ B)   = begin
    decode (id {A ⊗₀ B})
      ≈⟨ _decode-⊗-shape_ (id {A}) (id {B}) ⟩
    cAB-to ∘ (decode (id {A}) ⊗₁ decode (id {B})) ∘ cAB-from
      ≈⟨ refl⟩∘⟨ ⊗-resp-≈ (decode-id-is-id A) (decode-id-is-id B) ⟩∘⟨refl ⟩
    cAB-to ∘ (id ⊗₁ id) ∘ cAB-from
      ≈⟨ refl⟩∘⟨ id⊗id≈id ⟩∘⟨refl ⟩
    cAB-to ∘ id ∘ cAB-from
      ≈⟨ refl⟩∘⟨ idˡ ⟩
    cAB-to ∘ cAB-from
      ≈⟨ _≅_.isoˡ (unflatten-++-≅ (flatten A) (flatten B)) ⟩
    id ∎
    where
      cAB-to   = _≅_.to   (unflatten-++-≅ (flatten A) (flatten B))
      cAB-from = _≅_.from (unflatten-++-≅ (flatten A) (flatten B))

  -- Each chains `bridge-X-is-id` with `≈-Term-sym (decode-id-is-id A)`
  -- via the definitional `decode-rel X = bridge X`.  For λ⇒/λ⇐,
  -- `⟪ λ⇒ {A} ⟫ = hId A`, so `decode (λ⇒ {A})` has the same form as
  -- `decode (id {A})` and the same proof applies.

  ty-id : Ty-id
  ty-id = unapply-id (λ {A} → ≈-Term-trans
    (bridge-id-is-id A)
    (≈-Term-sym (decode-id-is-id A)))

  ty-λ⇒ : Ty-λ⇒
  ty-λ⇒ = unapply-λ⇒ (λ {A} → ≈-Term-trans
    (bridge-λ⇒-is-id A)
    (≈-Term-sym (decode-id-is-id A)))

  ty-λ⇐ : Ty-λ⇐
  ty-λ⇐ = unapply-λ⇐ (λ {A} → ≈-Term-trans
    (bridge-λ⇐-is-id A)
    (≈-Term-sym (decode-id-is-id A)))

--------------------------------------------------------------------------------
-- `FromShape t⊗` exposes polymorphic `Ty-id`, `Ty-λ⇒`, `Ty-λ⇐`
-- constructed from `Ty-⊗-shape`.  The remaining 8 of 11 Ty-X fields are
-- supplied elsewhere: `Ty-{ρ⇒,ρ⇐,α⇒,α⇐}` via the coherence chains plus
-- the shape postulates; `Ty-{Agen,σ}` via `DecodeRoundtripAgenSigma`;
-- `Ty-{∘,⊗}-shape` via `DecodeShape`.
