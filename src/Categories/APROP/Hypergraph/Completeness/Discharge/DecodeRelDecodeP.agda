{-# OPTIONS --without-K #-}

--------------------------------------------------------------------------------
-- Part (I) of the completeness proof: the structural ↔ pruned-algorithmic
-- decoder NORMAL-FORM agreement
--
--     decode-rel-≈-decodeP : ∀ {A B} (f : HomTerm A B)
--                          → decode-rel f ≈Term decodeP f
--
-- currently postulated wholesale (field `decode-rel-≈-decodeP`) in
-- `Discharge.DecodeRelRespIsoWired`.  This module proves it *as far as
-- possible* by structural induction on `f`, mirroring the existing
-- decomposition of the UNPRUNED analogue
--
--     decode-rel-≈-decode : ∀ {A B} (f : HomTerm A B)
--                         → decode-rel f ≈Term decode f
--
-- in `Completeness.DecoderAgreementSafe` (the `WithAssumptions` module)
-- and its discharge `Completeness.FromAssumptions.DecodeRelDecode`.
--
-- ## Why this is (almost) a verbatim port of the unpruned decomposition
--
-- `decode  f = subst₂ … (proj₁ (decode-attempt-Linear  f))`   [FromAPROP.⟪_⟫]
-- `decodeP f = subst₂ … (proj₁ (decode-attempt-LinearP f))`   [Translation.⟪_⟫]
--
-- The two underlying translations `FromAPROP.⟪_⟫` and `Translation.⟪_⟫`
-- (here aliased `⟪_⟫ₚ`) are *structurally identical on every constructor
-- except `∘`*: `∘` uses `hCompose` resp. `hComposeP` (pruning only removes
-- vertices, never edges).  Correspondingly:
--
--   * `decode-attempt-Linear` and `decode-attempt-LinearP` dispatch to the
--     SAME per-case lemma for every NON-`∘` constructor
--     (`decode-attempt-hGen`, `decode-attempt-hId`, `decode-attempt-hSwap`,
--     `decode-attempt-hTensor`); they differ only at `∘`
--     (`decode-attempt-hCompose` vs `decode-attempt-hComposeP`).
--   * The boundary `subst₂` proofs `⟪⟫-{dom,cod}L` agree on every NON-`∘`
--     constructor (same RHS: `domL-hGen`, `domL-hId`, `domL-hTensor ∘ …`).
--
-- Hence for every ATOMIC constructor X (Agen, σ, id, λ⇒, λ⇐, ρ⇒, ρ⇐,
-- α⇒, α⇐) we have, *definitionally*, `decodeP X ≡ decode X`, so the atomic
-- residuals are LITERALLY the unpruned atomic residuals — exactly the
-- 9 `bridge-≈-decode-X`-style obligations of `DecoderAgreementSafe`.
--
-- The decomposition therefore reduces (mirroring `DecoderAgreementSafe`)
-- to the SAME residual classes:
--
--   * (S) two SHAPE residuals: `decodeP-∘-shape`, `decodeP-⊗-shape`
--         (the pruned analogues of `decode-{∘,⊗}-shape`).  The `∘` shape
--         is the ONLY place where the pruned/unpruned algorithms genuinely
--         differ — `DecodeAttemptLinearP.decode-attempt-hComposeP` is the
--         load-bearing port that handles it.
--   * (M) the seven MONOIDAL-COHERENCE / id-coercion atomics
--         (id, λ⇒, λ⇐, ρ⇒, ρ⇐, α⇒, α⇐): all decode to `bridge` on the
--         `decode-rel` side and to an `hId`-shaped term on the algorithmic
--         side, related by `Categories.MonoidalCoherence`.  Here proven
--         from a single `≈Term`-level residual per shape, OR reduced to the
--         M-coherence residual.
--   * (K)/(atomic-edge) the two single-edge atomics (Agen, σ): the
--         `Agen`-collapse and `σ`-collapse residuals (the latter is the
--         Kelly-coherence `K` class — the σ swap-stack agreement).
--
-- ## What is PROVEN here vs. left as residual
--
-- PROVEN constructively (induction structure, no new postulate):
--   * the `∘` case: from `decodeP-∘-shape` + the two IHs + the
--     *definitional* `decode-rel-∘-shape` (refl).
--   * the `⊗` case: from `decodeP-⊗-shape` + the two IHs + the
--     *definitional* `decode-rel-⊗-shape` (refl).
--   * the dispatcher `decode-rel-≈-decodeP` itself (full induction on `f`).
--   * (M) `decode-rel-≈-decodeP-{id,λ⇒,λ⇐}` — THREE of the seven monoidal
--     atomics, discharged via monoidal coherence (see notes at the (M)
--     section).  Both sides collapse to `id`: the `decode-rel`/`bridge`
--     side by `bridge-{id,λ⇒,λ⇐}-is-id` (iso cancellation), the `decodeP`
--     side by `decodeP-id-is-id` (the algorithmic identity decoder REDUCES;
--     its `A ⊗₀ B` step uses the (S) `decodeP-⊗-shape` residual).  This
--     uses only `decodeP-⊗-shape`; no new postulate is introduced.
--
-- Left as clearly-marked residual `postulate`s (all STRICTLY NARROWER than
-- the original wholesale `decode-rel-≈-decodeP`), each tagged with its
-- class S / M / K:
--   * (S) `decodeP-∘-shape`, `decodeP-⊗-shape`
--   * (M) `decode-rel-≈-decodeP-{ρ⇒,ρ⇐,α⇒,α⇐}` — the four monoidal atomics
--     whose `bridge` side is a genuine unitor/associator coherence (NOT
--     `≈Term id`); their discharge is the unpruned
--     `decode-rel-≈-decode-{ρ⇒,ρ⇐,α⇒,α⇐}` obligation, itself gated on
--     further (still-open) shape/form postulates.
--   * (K) `decode-rel-≈-decodeP-{Agen,σ}`
--
-- This is the SAME 11-way split as `DecoderAgreementSafe`, instantiated at
-- `decodeP` instead of `decode`.  The value delivered is the explicit
-- decomposition, the two genuinely-discharged inductive (∘, ⊗) cases, and
-- the three discharged monoidal atomics (id, λ⇒, λ⇐).
--------------------------------------------------------------------------------

open import Categories.APROP

module Categories.APROP.Hypergraph.Completeness.Discharge.DecodeRelDecodeP
  (sig : APROPSignature) where

open APROP sig

open import Categories.APROP.Hypergraph.FromAPROP sig
  using (flatten)
open import Categories.APROP.Hypergraph.Completeness.Unflatten sig
  using (unflatten; unflatten-++-≅; unflatten-flatten-≈)
open import Categories.APROP.Hypergraph.Translation sig
  using (⟪⟫-domL; ⟪⟫-codL)
open import Categories.APROP.Hypergraph.Completeness.DecodeRel sig
  using (decode-rel; decode-rel-∘-shape; decode-rel-⊗-shape)
open import Categories.APROP.Hypergraph.Completeness.Discharge.DecodeAttemptLinearP sig
  using (decode-attempt-LinearP)
-- (M)-atomic discharge support: the `bridge` side of `decode-rel X`
-- collapses to `id` via the unflatten–flatten coherence isos.  These
-- `bridge-X-is-id` lemmas also exist in `DecodeRoundtripSafe`, but that
-- module is `--with-K`, so (to keep THIS module `--without-K`) we reprove
-- them locally — they are pure `≈Term` equational chains needing no K.

open import Categories.Category using (Category)
open import Categories.Morphism FreeMonoidal using (_≅_)
open import Data.Product using (proj₁)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; subst₂)

--------------------------------------------------------------------------------
-- The pruned decoder `decodeP`, re-stated here *verbatim* from
-- `Discharge.DecodeRelRespIsoWired.decodeP` (same definition: the boundary
-- `subst₂`-transport of `proj₁ (decode-attempt-LinearP f)`, using the
-- pruned translation's `⟪⟫-{dom,cod}L`).  We replicate the definition
-- rather than importing it because the host module
-- `DecodeRelRespIsoWired` transitively depends on `FinOrderNoInv`, which
-- currently does not typecheck on this branch (a pre-existing error
-- unrelated to part (I)); `decodeP` itself only needs
-- `decode-attempt-LinearP` and the boundary lemmas, none of which touch
-- `FinOrderNoInv`.  The statement below is therefore identical to the
-- target postulate `DecodeRelRespIsoWired.decode-rel-≈-decodeP`.
--------------------------------------------------------------------------------

decodeP : ∀ {A B} (f : HomTerm A B)
        → HomTerm (unflatten (flatten A)) (unflatten (flatten B))
decodeP {A} {B} f =
  subst₂ HomTerm (cong unflatten (⟪⟫-domL f)) (cong unflatten (⟪⟫-codL f))
         (proj₁ (decode-attempt-LinearP f))

private
  module FM = Category FreeMonoidal

open FM.HomReasoning

--------------------------------------------------------------------------------
-- Local `--without-K` reproductions of the `bridge-X-is-id` /
-- `decode-id-is-id` base-case lemmas (the same proofs live in the
-- `--with-K` module `DecodeRoundtripSafe`, which we cannot import here
-- without infecting this module).  Each is a pure `≈Term` equational
-- chain — no use of K.  Stated about `bridge X` directly; recall
-- `decode-rel X = bridge X` for atomic X (by `DecodeRel`).
--------------------------------------------------------------------------------

private
  open import Categories.APROP.Hypergraph.Completeness.DecodeAttempt sig
    using (bridge)

  -- `bridge (id {A}) ≈Term id`: the unflatten–flatten iso cancels.
  bridge-id-is-id : ∀ A → bridge (id {A}) ≈Term id
  bridge-id-is-id A = begin
    _≅_.from (unflatten-flatten-≈ A) ∘ id ∘ _≅_.to (unflatten-flatten-≈ A)
      ≈⟨ refl⟩∘⟨ idˡ ⟩
    _≅_.from (unflatten-flatten-≈ A) ∘ _≅_.to (unflatten-flatten-≈ A)
      ≈⟨ _≅_.isoʳ (unflatten-flatten-≈ A) ⟩
    id ∎

  -- `bridge (λ⇒ {A}) ≈Term id` and `bridge (λ⇐ {A}) ≈Term id`.
  bridge-λ⇒-is-id : ∀ A → bridge (λ⇒ {A}) ≈Term id
  bridge-λ⇒-is-id A = begin
    F-A ∘ λ⇒ ∘ (id ⊗₁ T-A) ∘ λ⇐
      ≈⟨ refl⟩∘⟨ FM.sym-assoc ⟩
    F-A ∘ (λ⇒ ∘ (id ⊗₁ T-A)) ∘ λ⇐
      ≈⟨ refl⟩∘⟨ λ⇒∘id⊗f≈f∘λ⇒ ⟩∘⟨refl ⟩
    F-A ∘ (T-A ∘ λ⇒) ∘ λ⇐
      ≈⟨ refl⟩∘⟨ FM.assoc ⟩
    F-A ∘ T-A ∘ λ⇒ ∘ λ⇐
      ≈⟨ FM.sym-assoc ⟩
    (F-A ∘ T-A) ∘ λ⇒ ∘ λ⇐
      ≈⟨ _≅_.isoʳ (unflatten-flatten-≈ A) ⟩∘⟨refl ⟩
    id ∘ λ⇒ ∘ λ⇐
      ≈⟨ idˡ ⟩
    λ⇒ ∘ λ⇐
      ≈⟨ λ⇒∘λ⇐≈id ⟩
    id ∎
    where
      F-A = _≅_.from (unflatten-flatten-≈ A)
      T-A = _≅_.to   (unflatten-flatten-≈ A)

  bridge-λ⇐-is-id : ∀ A → bridge (λ⇐ {A}) ≈Term id
  bridge-λ⇐-is-id A = begin
    (λ⇒ ∘ id ⊗₁ F-A) ∘ (λ⇐ ∘ T-A)
      ≈⟨ λ⇒∘id⊗f≈f∘λ⇒ ⟩∘⟨refl ⟩
    (F-A ∘ λ⇒) ∘ (λ⇐ ∘ T-A)
      ≈⟨ FM.assoc ⟩
    F-A ∘ (λ⇒ ∘ (λ⇐ ∘ T-A))
      ≈⟨ refl⟩∘⟨ FM.sym-assoc ⟩
    F-A ∘ ((λ⇒ ∘ λ⇐) ∘ T-A)
      ≈⟨ refl⟩∘⟨ (λ⇒∘λ⇐≈id ⟩∘⟨refl) ⟩
    F-A ∘ (id ∘ T-A)
      ≈⟨ refl⟩∘⟨ idˡ ⟩
    F-A ∘ T-A
      ≈⟨ _≅_.isoʳ (unflatten-flatten-≈ A) ⟩
    id ∎
    where
      F-A = _≅_.from (unflatten-flatten-≈ A)
      T-A = _≅_.to   (unflatten-flatten-≈ A)

  -- Base cases of the algorithmic identity decoder (it REDUCES; not a
  -- stuck `permute`).  Phrased on `decodeP`; `decodeP (id {A}) ≡
  -- decode (id {A})` is `refl` (same `hId`, same boundary proofs).
  decode-id-is-id-unit : decodeP (id {unit}) ≈Term id
  decode-id-is-id-unit = begin
    (id ∘ id) ∘ id   ≈⟨ idʳ ⟩
    id ∘ id          ≈⟨ idˡ ⟩
    id               ∎

  decode-id-is-id-Var : ∀ x → decodeP (id {Var x}) ≈Term id
  decode-id-is-id-Var x = begin
    ((id ⊗₁ id) ∘ ((id ⊗₁ id) ∘ id)) ∘ id
                                      ≈⟨ idʳ ⟩
    (id ⊗₁ id) ∘ ((id ⊗₁ id) ∘ id)    ≈⟨ id⊗id≈id ⟩∘⟨refl ⟩
    id ∘ ((id ⊗₁ id) ∘ id)            ≈⟨ idˡ ⟩
    (id ⊗₁ id) ∘ id                   ≈⟨ idʳ ⟩
    id ⊗₁ id                          ≈⟨ id⊗id≈id ⟩
    id                                ∎

--------------------------------------------------------------------------------
-- ## Residual postulates.  Each is STRICTLY NARROWER than the original
-- wholesale `decode-rel-≈-decodeP`, and tagged with its discharge class.
--------------------------------------------------------------------------------

------------------------------------------------------------------------
-- (S) The two SHAPE residuals: the pruned analogues of the existing
-- `DecodeShape.DecodeShapeResiduals` fields `decode-{∘,⊗}-shape-inner`.
--
-- `decodeP-∘-shape` is the ONLY residual whose discharge genuinely uses
-- the pruned machinery: it is `DecodeShape`-style term-tracking on the
-- `hComposeP` hypergraph, routed through
-- `DecodeAttemptLinearP.process-edges-↑{ˡ,ʳ}-…P` (the pruned ports of the
-- `DecodeAttempt` liftings).  `decodeP-⊗-shape` reuses `hTensor`
-- verbatim (tensor is NOT pruned), so its discharge is identical to the
-- unpruned `decode-⊗-shape-inner`.
------------------------------------------------------------------------

postulate
  -- (S) ∘-shape (pruned).  Mirrors `DecodeShape.decode-∘-shape-inner`.
  decodeP-∘-shape
    : ∀ {A B C} (g : HomTerm B C) (f : HomTerm A B)
    → decodeP (g ∘ f) ≈Term decodeP g ∘ decodeP f

  -- (S) ⊗-shape (tensor is not pruned; identical to unpruned).  Mirrors
  -- `DecodeShape.decode-⊗-shape-inner`.
  decodeP-⊗-shape
    : ∀ {A B C D} (f : HomTerm A B) (g : HomTerm C D)
    → decodeP (f ⊗₁ g)
    ≈Term _≅_.to   (unflatten-++-≅ (flatten B) (flatten D))
         ∘ (decodeP f ⊗₁ decodeP g)
         ∘ _≅_.from (unflatten-++-≅ (flatten A) (flatten C))

------------------------------------------------------------------------
-- (M) The seven MONOIDAL-COHERENCE / id-coercion atomics.  Each mirrors
-- the corresponding `DecoderAgreementSafe.Ty-{id,λ⇒,…}` field, with
-- `decode` replaced by the *definitionally equal* `decodeP` (the pruned
-- and unpruned algorithms agree on every non-`∘` constructor).  The
-- discharge route is `Categories.MonoidalCoherence` + the existing
-- `Discharge.{DecoderAgreementCases,DecoderAgreementRho}` machinery,
-- transported verbatim from `decode` to `decodeP`.
------------------------------------------------------------------------

-- ## (M) DISCHARGED: id, λ⇒, λ⇐.
--
-- For every non-`∘` constructor the pruned and unpruned pipelines agree
-- definitionally: `Translation.⟪ X ⟫ ≡ FromAPROP.⟪ X ⟫` (both `hId …`),
-- the boundary proofs `⟪⟫-{dom,cod}L X` are the SAME `domL-hId`/`codL-hId`
-- terms, and `decode-attempt-LinearP X ≡ decode-attempt-Linear X` (both
-- `decode-attempt-hId …`).  Hence `decodeP X ≡ decode X` is `refl`, so the
-- imported facts about the UNPRUNED `decode`/`bridge` apply verbatim to
-- `decodeP`/`decode-rel` (recall `decode-rel X = bridge X` for atomic X,
-- by `DecodeRel`).
--
-- The algorithmic identity decoder REDUCES (it is NOT a stuck `permute`):
-- at the `unit`/`Var x` leaves `decode-id-is-id-{unit,Var}` evaluate it to
-- `id`; at `A ⊗₀ B` the `decodeP-⊗-shape` residual (S) supplies the tensor
-- decomposition and the two halves cancel via the `unflatten-++-≅` iso.
-- The `bridge` side collapses to `id` by `bridge-{id,λ⇒,λ⇐}-is-id` (Mac
-- Lane coherence of the unflatten–flatten isos).  Both sides therefore meet
-- at `id`, giving `decode-rel X ≈Term decodeP X`.
--
-- `λ⇒`/`λ⇐` reuse the `id` decoder lemma directly because
-- `⟪ λ⇒ {A} ⟫ = ⟪ λ⇐ {A} ⟫ = hId A = ⟪ id {A} ⟫` with identical boundary
-- proofs, so `decodeP (λ⇒ {A}) ≡ decodeP (λ⇐ {A}) ≡ decodeP (id {A})`.

-- `decodeP (id {A}) ≈Term id`, by induction on `A`.  The `A ⊗₀ B` step
-- uses the (S) `decodeP-⊗-shape` residual (declared below).
decodeP-id-is-id : ∀ A → decodeP (id {A}) ≈Term id
decodeP-id-is-id unit    = decode-id-is-id-unit
decodeP-id-is-id (Var x) = decode-id-is-id-Var x
decodeP-id-is-id (A ⊗₀ B) = begin
  decodeP (id {A ⊗₀ B})
    ≈⟨ decodeP-⊗-shape (id {A}) (id {B}) ⟩
  cAB-to ∘ (decodeP (id {A}) ⊗₁ decodeP (id {B})) ∘ cAB-from
    ≈⟨ refl⟩∘⟨ ⊗-resp-≈ (decodeP-id-is-id A) (decodeP-id-is-id B) ⟩∘⟨refl ⟩
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

-- (M) identity.  `decode-rel (id {A}) = bridge (id {A})` (refl, by
-- `DecodeRel`), so `bridge-id-is-id` ∘ `decodeP-id-is-id` closes it.
decode-rel-≈-decodeP-id
  : ∀ {A} → decode-rel (id {A}) ≈Term decodeP (id {A})
decode-rel-≈-decodeP-id {A} =
  ≈-Term-trans (bridge-id-is-id A) (≈-Term-sym (decodeP-id-is-id A))

-- (M) left unitors.  `⟪ λ⇒ {A} ⟫ = ⟪ λ⇐ {A} ⟫ = hId A`, with the same
-- boundary proofs as `id {A}`, so `decodeP (λ⇒ {A}) ≡ decodeP (id {A})`
-- definitionally; reuse `decodeP-id-is-id`.  The `bridge` side collapses
-- by `bridge-{λ⇒,λ⇐}-is-id`.
decode-rel-≈-decodeP-λ⇒
  : ∀ {A} → decode-rel (λ⇒ {A}) ≈Term decodeP (λ⇒ {A})
decode-rel-≈-decodeP-λ⇒ {A} =
  ≈-Term-trans (bridge-λ⇒-is-id A) (≈-Term-sym (decodeP-id-is-id A))

decode-rel-≈-decodeP-λ⇐
  : ∀ {A} → decode-rel (λ⇐ {A}) ≈Term decodeP (λ⇐ {A})
decode-rel-≈-decodeP-λ⇐ {A} =
  ≈-Term-trans (bridge-λ⇐-is-id A) (≈-Term-sym (decodeP-id-is-id A))

-- ## (M) RESIDUAL: ρ⇒, ρ⇐, α⇒, α⇐.
--
-- These four also have `⟪ X ⟫ = hId …`, so the `decodeP X` side still
-- reduces (to `decodeP (id {…})`, hence `≈Term id`).  But the `bridge X`
-- side is NOT `≈Term id`: it is the genuine right-unitor / associator
-- coherence between the flattened objects (whose flattenings coincide only
-- up to `++-identityʳ` / `++-assoc`).  Discharging them is exactly the
-- unpruned `decode-rel-≈-decode-{ρ⇒,ρ⇐,α⇒,α⇐}` obligation, which in
-- `DecodeRoundtripSafe` is gated on further postulates not available
-- constructively (`decode-{ρ⇒,ρ⇐}-shape`, `bridge-α⇒-form-⊗-⊗`,
-- `c-iso-assoc-from-cons`).  Left as residual.
postulate
  -- (M) right unitors.
  decode-rel-≈-decodeP-ρ⇒
    : ∀ {A} → decode-rel (ρ⇒ {A}) ≈Term decodeP (ρ⇒ {A})
  decode-rel-≈-decodeP-ρ⇐
    : ∀ {A} → decode-rel (ρ⇐ {A}) ≈Term decodeP (ρ⇐ {A})
  -- (M) associators.
  decode-rel-≈-decodeP-α⇒
    : ∀ {A B C} → decode-rel (α⇒ {A} {B} {C}) ≈Term decodeP (α⇒ {A} {B} {C})
  decode-rel-≈-decodeP-α⇐
    : ∀ {A B C} → decode-rel (α⇐ {A} {B} {C}) ≈Term decodeP (α⇐ {A} {B} {C})

------------------------------------------------------------------------
-- (K) The two single-edge atomics: `Agen`-collapse and `σ`-collapse.
-- `Agen` mirrors `DecoderAgreementSafe.Ty-Agen`; `σ` mirrors `Ty-σ` (the
-- Kelly-coherence `K` class — the swap-stack agreement that gates the
-- final permute throughout this development).
------------------------------------------------------------------------

postulate
  -- (K / single-edge) generator collapse.
  decode-rel-≈-decodeP-Agen
    : ∀ {A B} (g : mor A B) → decode-rel (Agen g) ≈Term decodeP (Agen g)
  -- (K) symmetry collapse — the Kelly-coherence residual.
  decode-rel-≈-decodeP-σ
    : ∀ {A B} ⦃ s : Symm ≤ Symm ⦄
    → decode-rel (σ {A = A} {B = B} ⦃ s ⦄)
      ≈Term decodeP (σ {A = A} {B = B} ⦃ s ⦄)

--------------------------------------------------------------------------------
-- ## The dispatcher: `decode-rel-≈-decodeP` by structural induction on `f`.
--
-- This is the genuinely constructive content.  Atomic constructors invoke
-- the corresponding residual directly.  The `∘` and `⊗` cases are PROVEN
-- from the shape residuals + the IHs + the *definitional* (refl)
-- `decode-rel-{∘,⊗}-shape`, exactly as in
-- `DecoderAgreementSafe.WithAssumptions.decode-rel-≈-decode`.
--------------------------------------------------------------------------------

private
  ≡⇒≈Term : ∀ {A B} {f g : HomTerm A B} → f ≡ g → f ≈Term g
  ≡⇒≈Term refl = ≈-Term-refl

decode-rel-≈-decodeP
  : ∀ {A B} (f : HomTerm A B) → decode-rel f ≈Term decodeP f
decode-rel-≈-decodeP (Agen g)  = decode-rel-≈-decodeP-Agen g
decode-rel-≈-decodeP (σ ⦃ s ⦄) = decode-rel-≈-decodeP-σ ⦃ s ⦄
decode-rel-≈-decodeP id        = decode-rel-≈-decodeP-id
decode-rel-≈-decodeP λ⇒        = decode-rel-≈-decodeP-λ⇒
decode-rel-≈-decodeP λ⇐        = decode-rel-≈-decodeP-λ⇐
decode-rel-≈-decodeP ρ⇒        = decode-rel-≈-decodeP-ρ⇒
decode-rel-≈-decodeP ρ⇐        = decode-rel-≈-decodeP-ρ⇐
decode-rel-≈-decodeP α⇒        = decode-rel-≈-decodeP-α⇒
decode-rel-≈-decodeP α⇐        = decode-rel-≈-decodeP-α⇐
-- ∘ case: definitional `decode-rel-∘-shape` (refl) + IHs + `decodeP-∘-shape`.
decode-rel-≈-decodeP (g ∘ f) =
  ≈-Term-trans
    (≡⇒≈Term (decode-rel-∘-shape g f))
    (≈-Term-trans
      (∘-resp-≈ (decode-rel-≈-decodeP g) (decode-rel-≈-decodeP f))
      (≈-Term-sym (decodeP-∘-shape g f)))
-- ⊗ case: definitional `decode-rel-⊗-shape` (refl) + IHs + `decodeP-⊗-shape`.
decode-rel-≈-decodeP (_⊗₁_ {A = A} {B = B} {C = C} {D = D} f g) =
  ≈-Term-trans
    (≡⇒≈Term (decode-rel-⊗-shape f g))
    (≈-Term-trans
      (refl⟩∘⟨ ⊗-resp-≈ (decode-rel-≈-decodeP f) (decode-rel-≈-decodeP g) ⟩∘⟨refl)
      (≈-Term-sym (decodeP-⊗-shape f g)))
