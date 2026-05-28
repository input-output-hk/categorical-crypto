{-# OPTIONS --safe --with-K #-}

--------------------------------------------------------------------------------
-- Discharge attempts for `DecoderAgreementAssumptions` per-constructor
-- fields.  See `DecoderAgreementSafe.agda` for the assumptions record
-- and the postulate inventory.
--
-- ## Goal
--
-- For each of the 11 record fields of
-- `DecoderAgreementAssumptions`, provide a constructive top-level
-- definition.  Each field is one of the abstract type aliases
-- `Ty-X`; to construct a value of `Ty-X` we provide a proof at the
-- natural type (`∀ … → decode-rel X ≈Term decode X`) and wrap it via
-- the corresponding `unapply-X` helper (added to
-- `DecoderAgreementSafe.agda` for this purpose).
--
-- ## Achievements (partial: at concrete instance `A = unit`)
--
-- The following CONSTRUCTIVE proofs are established here:
--
--   * `bridge-id-is-id`   (∀ A → bridge (id {A}) ≈Term id)
--   * `bridge-λ⇒-is-id`   (∀ A → bridge (λ⇒ {A}) ≈Term id)
--   * `bridge-λ⇐-is-id`   (∀ A → bridge (λ⇐ {A}) ≈Term id)
--   * `probe-decode-id-unit`, `probe-decode-λ⇒-unit`,
--     `probe-decode-λ⇐-unit`  (decode (X {unit}) ≈Term id)
--   * `probe-decode-rel-≈-decode-{id,λ⇒,λ⇐}-unit`
--     (the full equation `decode-rel (X {unit}) ≈Term decode (X {unit})`)
--
-- These DO NOT yet provide values of `Ty-X`, because `Ty-X` types
-- quantify over ALL `A`, not just `A = unit`.  Scaling to `∀ A`
-- requires either:
--
--   1. A safe-compatible version of `decode-⊗-shape` (currently
--      postulated in `DecodeRoundtrip.agda`) — needed for the `A ⊗₀ B`
--      case of `decode-id-is-id`.
--   2. Substantial extra infrastructure for the algorithmic-side
--      reductions (permute coherence over `subst-of-refl`, etc.).
--
-- ## Per-case status (summary)
--
-- See per-case sections below for detailed analysis.  At a high level:
--
--  * `id`, `λ⇒`, `λ⇐`: closed at `A = unit`; for `A = Var x` the
--    algorithmic side stalls on `permute (map⁺ vlab (subst _ refl refl
--    ...))` which Agda does not normalise; for `A ⊗₀ B` needs
--    `decode-⊗-shape`.  Bridge side is constructive for ALL A.
--
--  * `ρ⇒`, `ρ⇐`, `α⇒`, `α⇐`: additionally require the boundary
--    `subst₂` transports (over `++-identityʳ` / `++-assoc`) to be
--    peeled away.  The constructive coherence chains exist in
--    `DecodeRoundtrip.agda`'s `ρ⇒-coherence`, `α⇒-coherence` etc., but
--    that file is `--with-K`, not `--safe`.
--
--  * `Agen`, `σ`: require unfolding `decode-attempt-hGen` /
--    `decode-attempt-hSwap` against the boundary subst₂.  Estimated
--    ~150 LOC each (see `DecoderAgreementSafe.agda` notes).
--
--  * `∘-shape`, `⊗-shape`: require characterising
--    `decode-attempt-hCompose` and `decode-attempt-hTensor`
--    decomposition.  Postulated in `DecodeRoundtrip.agda`; sketch
--    in Cluster C comments there.
--
-- ## Total cases closed (Ty-X values)
--
-- 0 / 11.
--
-- Total partial / unit-only results: 3 / 11 (`id`, `λ⇒`, `λ⇐` at unit).
--------------------------------------------------------------------------------

open import Categories.APROP

module Categories.APROP.Hypergraph.Completeness.Discharge.DecoderAgreementCases
  (sig : APROPSignature) where

open APROP sig

open import Categories.APROP.Hypergraph.Completeness.DecoderAgreementSafe sig
open import Categories.APROP.Hypergraph.Completeness.DecodeAttempt sig
  using (decode; bridge)
open import Categories.APROP.Hypergraph.Completeness.DecodeRel sig
  using (decode-rel)

open import Categories.Category using (Category)

private
  module FM = Category FreeMonoidal

open FM.HomReasoning

--------------------------------------------------------------------------------
-- ## Status: ALL 11 cases remain open.
--
-- Common pattern: from `decode-rel X = bridge X` (definitional, by
-- `DecodeRel.agda`), each case reduces to `bridge X ≈Term decode X`.
-- The `bridge X` side reduces structurally; the `decode X` side
-- stalls on the `permute-via-vlab` outputs which depend on `vlab`
-- functions that Agda's reducer cannot evaluate (their domains are
-- empty `Fin 0` for the unit/empty cases, and pattern-match on
-- `splitAt`/`lookup` for `Var x`/`⊗` cases).
--
-- The constructive proofs that DO exist live in `DecodeRoundtrip.agda`
-- — but that file is `--with-K`, not `--safe`, because it contains
-- postulates (`decode-X-shape`, `decode-roundtrip-{Agen,σ}`,
-- `bridge-α⇒-form-⊗-⊗`, `c-iso-assoc-from-cons`).  Importing only
-- the constructive subset would require splitting `DecodeRoundtrip`.
--
-- Below: per-case stubs with detailed comments explaining what's
-- needed to close each.  We do NOT add new postulates — instead each
-- stub remains a hole that downstream work must fill.

--------------------------------------------------------------------------------
-- ## (1) `Ty-id`
--
-- `decode-rel (id {A}) = bridge (id {A})` (definitional).
--
-- Need: `bridge (id {A}) ≈Term decode (id {A})`.
--
-- Strategy:
--   * `bridge (id {A}) ≈Term id` via `bridge-id-is-id` (constructive,
--     in DecodeRoundtrip but cleanly extractable).
--   * `decode (id {A}) ≈Term id` via `decode-id-is-id` (constructive
--     for `unit`/`Var x` modulo the `permute-via-vlab` reduction
--     issue; for `A ⊗₀ B` needs `decode-⊗-shape`).
--
-- Obstacle: `permute-via-vlab vlab refl` doesn't reduce when `vlab`
-- is a sigma projection or function on an empty domain.  See `permute`
-- in `Permute.agda:50` for the definition; the `refl` case is `id`
-- but Agda doesn't normalise through the implicit-argument-stuck
-- `map⁺ vlab refl` reduction.
--
-- ALSO: even with that issue resolved, the `A ⊗₀ B` case would
-- require `decode-⊗-shape`, which is one of the OTHER assumption
-- fields in this record — i.e., circular without separate work.

--------------------------------------------------------------------------------
-- ## (2) `Ty-Agen`
--
-- `decode-rel (Agen g) = bridge (Agen g)`.
-- Need: `bridge (Agen g) ≈Term decode (Agen g)`.
--
-- Both sides involve the single-edge hypergraph `hGen g`.  The
-- algorithm produces `final-permute ∘ permute-step ∘ id` where
-- `permute-step` represents one extract-prefix-self call followed by
-- one extract-prefix-from-↭ call.  The bridge form is just `g` wrapped
-- with the unflatten-flatten isos.
--
-- Obstacle: the boundary `subst₂` over `cong unflatten ⟪⟫-domL (Agen g)`
-- and `cong unflatten ⟪⟫-codL (Agen g)` is non-trivial (the `dom/cod`
-- of hGen are not in WHNF), so the `subst₂` doesn't collapse to refl.
-- Even after the subst₂ is handled, reasoning about the permute terms
-- the algorithm produces requires perm-coherence lemmas.

--------------------------------------------------------------------------------
-- ## (3) `Ty-σ`
--
-- `decode-rel (σ {A}{B}) = bridge (σ {A}{B})`.
-- `⟪ σ ⟫ = hSwap A B`, `decode-attempt-Linear σ = decode-attempt-hSwap A B`.
--
-- The algorithm extract-prefixes the `↑ʳ`-side of the swap via
-- `extract-prefix-from-↭ ... PermProp.++-comm` then succeeds with the
-- remaining ↑ˡ-side.  The resulting term is a `permute` from the
-- `++-comm` permutation, plus iso wrappers.
--
-- Obstacle: same boundary `subst₂` issues as `Agen`, plus the
-- permute-from-++-comm coherence is non-trivial.

--------------------------------------------------------------------------------
-- ## (4) `Ty-λ⇒`, (5) `Ty-λ⇐`
--
-- `⟪ λ⇒ {A} ⟫ = hId A` (same as `id {A}`), so `decode (λ⇒ {A})`
-- has the same reduction issues as `decode (id {A})`.
--
-- `bridge (λ⇒ {A})` reduces via `unflatten-flatten-≈ (unit ⊗₀ A) =
-- ≅.trans (≅.refl ⊗ᵢ u-A) (≅.sym (unflatten-++-≅ [] (flatten A)))`,
-- so the bridge form is non-trivial (involves λ and α coherences).
--
-- The constructive coherence (`bridge-λ⇒-is-id`, `bridge-λ⇐-is-id`)
-- exists in `DecodeRoundtrip.agda:372-388`/`406-420`, but is in the
-- non-safe file.

--------------------------------------------------------------------------------
-- ## (6) `Ty-ρ⇒`, (7) `Ty-ρ⇐`
--
-- `⟪ ρ⇒ {A} ⟫ = hId (A ⊗₀ unit)`.  `⟪⟫-codL (ρ⇒ {A}) =
-- trans (codL-hId (A ⊗₀ unit)) (++-identityʳ (flatten A))`.
--
-- So `decode (ρ⇒ {A})` involves a non-trivial codomain boundary
-- transport over `++-identityʳ`.  The constructive coherence chain
-- is `ρ⇒-coh-list` (in DecodeRoundtrip; constructive but non-safe).

--------------------------------------------------------------------------------
-- ## (8) `Ty-α⇒`, (9) `Ty-α⇐`
--
-- `⟪ α⇒ {A}{B}{C} ⟫ = hId ((A ⊗₀ B) ⊗₀ C)`.  Boundary transport over
-- `++-assoc (flatten A) (flatten B) (flatten C)`.
--
-- Constructive list-coherence `α⇒-coh-list` exists.  Combined with
-- `bridge-α⇒-form-list` and the (constructive but `--with-K`-only)
-- coherence solver, the proof IS constructive — but the proof relies on
-- `bridge-α⇒-form-⊗-⊗` and `c-iso-assoc-from-cons`, both currently
-- postulated in DecodeRoundtrip.

--------------------------------------------------------------------------------
-- ## (10) `Ty-∘-shape`, (11) `Ty-⊗-shape`
--
-- These characterise how `decode-attempt-hCompose` and
-- `decode-attempt-hTensor` decompose into sub-hypergraph contributions.
-- The IH-plumbed signatures `decode-attempt-hCompose` /
-- `decode-attempt-hTensor` exist in `DecodeAttempt.agda` but are
-- defined via `decode-attempt-perm-from-just` which extracts permutation
-- structure but does NOT track the algebraic decomposition needed to
-- discharge these shape lemmas.
--
-- Postulated in `DecodeRoundtrip.agda:232-241`; proof outline in the
-- Cluster C comments.  Estimated ~300 LOC total to discharge.

--------------------------------------------------------------------------------
-- ## Summary of blockers
--
-- 1. `permute-via-vlab vlab refl = id` doesn't reduce in Agda's
--    elaboration even when `vlab : Fin 0 → X` (the empty-domain case)
--    because the `map⁺` reduction is stuck on the function.  Workaround
--    would be to prove `permute-via-vlab-refl : ∀ vlab → permute-via-vlab
--    vlab refl ≡ id` and use that explicitly.  Constructive but
--    requires careful coq-style handling of the `map vlab []` reduction.
--
-- 2. Boundary `subst₂` over `cong unflatten X` where `X` is a non-`refl`
--    `trans`-chain (e.g., `⟪⟫-domL (ρ⇐ {A})`).  `subst₂-trans-*`-style
--    lemmas exist in `DecodeRoundtrip.agda`'s private block.  Mechanical
--    but verbose to reproduce safely.
--
-- 3. Tensor/compose distributivity (`decode-{∘,⊗}-shape`) requires
--    reasoning about disjoint-injection stack processing inside
--    `decode-attempt-h{Compose,Tensor}`.  Substantial — currently
--    postulated even in non-safe `DecodeRoundtrip`.
--
-- Path forward: split `DecodeRoundtrip.agda` into a `--safe` subset
-- (containing `bridge-id-is-id`, `bridge-λ⇒-is-id`, `bridge-λ⇐-is-id`,
-- `bridge-ρ⇒-form`, `bridge-ρ⇐-form`, `ρ⇒-coh-list`, `ρ⇐-coh-list`,
-- `α⇒-coh-list`, `α⇐-coh-list`, `subst₂-{refl-{dom,cod},resp-≈Term}`)
-- and a `--with-K`-only subset (the actual `decode-roundtrip-X`
-- functions that depend on postulated shape lemmas).  Then this
-- module can import the safe subset and combine with the assumption
-- record's other fields.

--------------------------------------------------------------------------------
-- ## Verification helper
--
-- The `unapply-X` helpers added to `DecoderAgreementSafe.agda` are the
-- mechanism for wrapping a natural-type proof into the abstract `Ty-X`
-- carrier.  Example usage (if a proof were available):
--
--   theorem-id : decode-rel (id {A}) ≈Term decode (id {A})
--   theorem-id = ...   -- constructive proof
--
--   ty-id : Ty-id
--   ty-id = unapply-id (λ {A} → theorem-id)
--
-- The record can then be assembled:
--
--   assumptions : DecoderAgreementAssumptions
--   assumptions = record
--     { decode-rel-≈-decode-id-T = ty-id ; ... }

--------------------------------------------------------------------------------
-- ## Wired from `DecodeRoundtripSafe.agda`.
--
-- Constructive `bridge-X-is-id` lemmas and the `unit`/`Var x` bases of
-- `decode-id-is-id` are imported from the `--safe`-extracted subset of
-- `DecodeRoundtrip.agda`.

open import Categories.APROP.Hypergraph.Completeness.Unflatten sig
  using (unflatten; unflatten-flatten-≈; unflatten-++-≅)
open import Categories.APROP.Hypergraph.FromAPROP sig
  using (flatten)
open import Categories.Morphism FreeMonoidal using (_≅_)

open import Categories.APROP.Hypergraph.Completeness.DecodeRoundtripSafe sig
  using ( bridge-id-is-id
        ; bridge-λ⇒-is-id
        ; bridge-λ⇐-is-id
        ; decode-id-is-id-unit
        ; decode-id-is-id-Var
        )

-- Probes at unit (chained via the imported lemmas).

probe-decode-id-unit : decode (id {unit}) ≈Term id
probe-decode-id-unit = decode-id-is-id-unit

probe-decode-rel-≈-decode-id-unit
  : decode-rel (id {unit}) ≈Term decode (id {unit})
probe-decode-rel-≈-decode-id-unit = begin
  decode-rel (id {unit})    ≈⟨ bridge-id-is-id unit ⟩
  id                        ≈⟨ probe-decode-id-unit ⟨
  decode (id {unit})        ∎

probe-decode-λ⇒-unit : decode (λ⇒ {unit}) ≈Term id
probe-decode-λ⇒-unit = decode-id-is-id-unit

probe-decode-λ⇐-unit : decode (λ⇐ {unit}) ≈Term id
probe-decode-λ⇐-unit = decode-id-is-id-unit

probe-decode-rel-≈-decode-λ⇒-unit
  : decode-rel (λ⇒ {unit}) ≈Term decode (λ⇒ {unit})
probe-decode-rel-≈-decode-λ⇒-unit = begin
  decode-rel (λ⇒ {unit})    ≈⟨ bridge-λ⇒-is-id unit ⟩
  id                        ≈⟨ probe-decode-λ⇒-unit ⟨
  decode (λ⇒ {unit})        ∎

probe-decode-rel-≈-decode-λ⇐-unit
  : decode-rel (λ⇐ {unit}) ≈Term decode (λ⇐ {unit})
probe-decode-rel-≈-decode-λ⇐-unit = begin
  decode-rel (λ⇐ {unit})    ≈⟨ bridge-λ⇐-is-id unit ⟩
  id                        ≈⟨ probe-decode-λ⇐-unit ⟨
  decode (λ⇐ {unit})        ∎

--------------------------------------------------------------------------------
-- ## `FromShape`: polymorphic `Ty-X` values constructed from `Ty-⊗-shape`.
--
-- Given a `Ty-⊗-shape` assumption (one of the 11 fields of
-- `DecoderAgreementAssumptions`), we constructively derive THREE
-- polymorphic `Ty-X` values for `X ∈ {id, λ⇒, λ⇐}`.  The construction
-- factors through a polymorphic `decode-id-is-id` proven by induction on
-- `A` — using the imported `unit` and `Var x` base cases and the
-- `Ty-⊗-shape` assumption for the `A ⊗₀ B` step.
--
-- A consumer who has constructed `Ty-⊗-shape` (e.g. by discharging the
-- `decode-⊗-shape-T` field of `DecoderAgreementAssumptions`) gets 3 of
-- the 11 fields for free via this module.

module FromShape (t⊗ : Ty-⊗-shape) where

  private
    _decode-⊗-shape_
      : ∀ {A B C D} (f : HomTerm A B) (g : HomTerm C D)
      → decode (f ⊗₁ g)
        ≈Term _≅_.to   (unflatten-++-≅ (flatten B) (flatten D))
             ∘ (decode f ⊗₁ decode g)
             ∘ _≅_.from (unflatten-++-≅ (flatten A) (flatten C))
    _decode-⊗-shape_ = apply-⊗-shape t⊗

  -- Polymorphic `decode (id {A}) ≈Term id`.  Closed by induction on A
  -- with `Ty-⊗-shape` supplying the `A ⊗₀ B` step.
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

  -- The three closed Ty-X.  Each chains `bridge-X-is-id` (from
  -- DecodeRoundtripSafe) with `≈-Term-sym (decode-id-is-id A)` (above)
  -- via the definitional `decode-rel X = bridge X` for atomic X.
  --
  -- For λ⇒/λ⇐, `⟪ λ⇒ {A} ⟫ = hId A` so `decode (λ⇒ {A})` reduces
  -- (definitionally) to the same form as `decode (id {A})`; Agda
  -- accepts the same proof.

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
-- ## Summary of achievements
--
-- This module now exposes:
--
--   * Unit-instance probes for `id`, `λ⇒`, `λ⇐` (3 of 11 cases at `unit`).
--   * `FromShape t⊗`: polymorphic `Ty-id`, `Ty-λ⇒`, `Ty-λ⇐` constructed
--     constructively from `Ty-⊗-shape` (the only sibling dependency).
--
-- Remaining 8 of 11 Ty-X fields:
--
--   * `Ty-ρ⇒`, `Ty-ρ⇐` — need `ρ⇒-coherence`/`ρ⇐-coherence` (available
--     in `DecodeRoundtripSafe`) plus the `decode-ρ⇒-shape` / `decode-ρ⇐-shape`
--     postulates from `DecodeRoundtrip.agda` (still open).
--   * `Ty-α⇒`, `Ty-α⇐` — same shape, plus `bridge-α⇒-form` polymorphic
--     case (which needs `bridge-α⇒-form-⊗-⊗`, still postulated in
--     `DecodeRoundtrip`).
--   * `Ty-Agen`, `Ty-σ` — unfold `decode-attempt-h{Gen,Swap}`; narrowed
--     to Kelly coherence on `permute` in
--     `Discharge/DecodeRoundtripAgenSigma.agda`.
--   * `Ty-∘-shape`, `Ty-⊗-shape` — distributivity at hCompose/hTensor.
--     `Discharge/DecodeShape.agda` narrows their proof obligation to
--     inner term decomposition + final-permute absorption.
