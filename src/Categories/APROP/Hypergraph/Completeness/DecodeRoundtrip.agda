{-# OPTIONS #-}

--------------------------------------------------------------------------------
-- Phase 3.5f Step 5 — `decode-roundtrip` by induction on the term.
--
-- Given the constructive definition of `decode` (= `proj₁` of
-- `decode-attempt-Linear`, which is itself constructive by induction
-- on the term), we prove
--
--   decode-roundtrip : ∀ f → decode f ≈Term bridge f
--
-- by structural induction on `f`.
--
-- *Layer 1 of Step 5-A — Foundations*:
--   * `bridge-∘`: `bridge` distributes over composition (modulo iso
--     cancellation).  Constructive.
--   * `bridge-⊗`: `bridge` distributes over tensor (modulo the
--     ~unflatten-++-≅~ coherence wrapping).  Constructive.
--   * `bridge-⊗-decompose`: helper splitting `bridge f ⊗₁ bridge g`
--     via ⊗-∘-dist.
--
-- *Cluster C — compositional axioms* are now constructive modulo
-- two smaller postulates (`decode-∘-shape`, `decode-⊗-shape`) that
-- characterise how `decode-attempt-h{Compose,Tensor}` decompose into
-- sub-hypergraph contributions:
--   * `decode-roundtrip-∘ g f IH-g IH-f`: chain
--     decode-∘-shape → IHs → sym bridge-∘.
--   * `decode-roundtrip-⊗₁ f g IH-f IH-g`: chain
--     decode-⊗-shape → IHs (under the coherence wrapper) → sym bridge-⊗.
--
-- *Cluster A — hId-based axioms* and *Cluster B — atomic axioms* are
-- still postulated.  The plan in TODO.org Step 5-A breaks them down
-- into per-constructor `bridge-X-is-id` chains and a shared
-- `decode-id-is-id` lemma (Layer 2).
--
--------------------------------------------------------------------------------
-- POSTULATE INVENTORY (as of Phase 4 work)
--
-- Cluster A/B/C structural postulates (decode-attempt characterisation):
--   * decode-∘-shape, decode-⊗-shape : Layer 6 (line ~183-193)
--   * decode-roundtrip-Agen           : per-generator atomic case
--   * decode-roundtrip-σ              : symmetry case (postulated)
--   * decode-attempt-hSwap shape lemmas (in DecodeAttempt.agda)
--
-- Bridge-form postulates for α (residual after Phase 1-4):
--   * bridge-α⇒-form-⊗-⊗ (line ~1351): Phase 4 inductive case
--     (A₁ = A₁₁⊗A₁₂).  See detailed strategy comment at the postulate.
--   * c-iso-assoc-from-cons (line ~1129, in private block): cons case
--     of the c-iso pentagon.  Required by Phase 4 main proof.
--
-- All ρ⇒/ρ⇐ bridge-form postulates: PROVED.
-- All λ⇒/λ⇐ bridge-form postulates: PROVED (via decode-id-is-id).
-- bridge-α⇒-form base cases (unit, Var x): PROVED.
-- bridge-α⇒-form-⊗ {unit,Var,⊗-⊗}: 2 of 3 proved (unit, Var).
-- bridge-α⇐-form: PROVED (derived from bridge-α⇒-form via α⇒-α⇐-iso).
--
-- Phase 4 helper infrastructure (all proved in this file):
--   * α⇐-α⇒-iso (line ~838): reverse direction of α-form-list iso.
--   * α⇒-λ⇐-collapse (line ~852): Mac Lane corollary
--     α⇒_{unit,X,Y} ∘ (λ⇐ ⊗ id) ≈ λ⇐_{X⊗Y}.
--   * pentagon-rewrite (line ~867): solves pentagon for α⇒_{X⊗Y,Z,W}.
--   * id-⊗-subst-bridge (line ~879): id ⊗ subst-id ≈ subst-id at
--     wrapped predicate (for c-iso pentagon's cons case).
--   * id-⊗-respects-∘ (line ~885): id ⊗ (g ∘ f) ≈ (id ⊗ g) ∘ (id ⊗ f).
--   * α⇐-comm-top (line ~896): top-level α⇐-naturality.
--   * c-iso-assoc-from base case (line ~1167, in private block):
--     base case of c-iso pentagon proved.
--
-- See the strategy comments at bridge-α⇒-form-⊗-⊗ (line ~1280) and
-- c-iso-assoc-from-cons (line ~1109) for detailed proof outlines and
-- explanations of why these postulates remain (Mac Lane coherence
-- shortcut blocked by --without-K, chain proofs estimated at 30-150
-- chain steps each).
--------------------------------------------------------------------------------

open import Categories.APROP
open import Categories.Category.Monoidal using (Monoidal)

module Categories.APROP.Hypergraph.Completeness.DecodeRoundtrip (sig : APROPSignature) where

open APROP sig
open import Categories.APROP.Hypergraph.FromAPROP sig
  using (flatten; ⟪_⟫; hId; domL-hId; codL-hId)
open import Categories.APROP.Hypergraph.Completeness.Unflatten sig
  using (unflatten; unflatten-flatten-≈; unflatten-++-≅)
open import Categories.APROP.Hypergraph.Completeness.DecodeAttempt sig
  using (decode; bridge; decode-attempt-Linear; decode-attempt-hId)

-- DE-INDEXED REFACTOR: `decode-attempt-subst₂` and
-- `decode-attempt-subst₂-proj₁` no longer exist (the boundary
-- transports they handled don't arise in the de-indexed version).
-- The `decode-{ρ⇒,ρ⇐,α⇒,α⇐}-shape` lemmas below are now PROVEN
-- postulate-free (clone of `rhoShapeResidual` from
-- `Discharge/DecodeRelDecodeP.agda`): the role formerly played by
-- `decode-attempt-subst₂-proj₁` is now played by the boundary subst at
-- the top of `decode` itself, peeled by `subst₂-{cod,dom}-trans`.

open import Categories.Category using (Category)
open import Categories.Morphism FreeMonoidal using (_≅_)
open import Categories.Category.Monoidal.Properties Monoidal-FreeMonoidal
  using (module Kelly's)
open Kelly's using (coherence₂; coherence-inv₂; coherence₃; coherence-inv₃)
open Monoidal Monoidal-FreeMonoidal using (unitorʳ; associator)
open import Categories.Category.Monoidal.Utilities Monoidal-FreeMonoidal
  using (triangle-inv)
open import Data.List using (List; []; _∷_; _++_)
open import Data.List.Properties using (++-identityʳ; ++-assoc)
open import Data.Product using (_,_; proj₁)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; sym; subst; subst₂)
  renaming (trans to ≡-trans)
open import Relation.Binary.PropositionalEquality.Properties using (subst-∘)

private
  module FM = Category FreeMonoidal

open FM.HomReasoning

--------------------------------------------------------------------------------
-- Foundation lemmas (Layer 1 of the Step 5-A plan).  These are the
-- shared infrastructure used by the per-constructor proofs below.

-- L8: `bridge` distributes over composition (modulo iso cancellation).
-- Together with the IH `decode g ≈ bridge g` / `decode f ≈ bridge f`,
-- this lets `decode-roundtrip-∘` reduce to a structural lemma about
-- how `decode-attempt-hCompose` produces its output.
--
-- Concretely: the inner ~≅.to u-B ∘ ≅.from u-B~ pair cancels via
-- `_≅_.isoˡ`, leaving the outer iso wrapping intact.

bridge-∘
  : ∀ {A B C} (g : HomTerm B C) (f : HomTerm A B)
  → bridge (g ∘ f) ≈Term bridge g ∘ bridge f
bridge-∘ {A} {B} {C} g f = ≈-Term-sym chain
  where
    F-C = _≅_.from (unflatten-flatten-≈ C)
    F-B = _≅_.from (unflatten-flatten-≈ B)
    T-B = _≅_.to   (unflatten-flatten-≈ B)
    T-A = _≅_.to   (unflatten-flatten-≈ A)

    chain : bridge g ∘ bridge f ≈Term bridge (g ∘ f)
    chain = begin
      (F-C ∘ g ∘ T-B) ∘ (F-B ∘ f ∘ T-A)
        ≈⟨ FM.assoc ⟩
      F-C ∘ (g ∘ T-B) ∘ (F-B ∘ f ∘ T-A)
        ≈⟨ refl⟩∘⟨ FM.assoc ⟩
      F-C ∘ g ∘ T-B ∘ F-B ∘ f ∘ T-A
        ≈⟨ refl⟩∘⟨ refl⟩∘⟨ FM.sym-assoc ⟩
      F-C ∘ g ∘ (T-B ∘ F-B) ∘ f ∘ T-A
        ≈⟨ refl⟩∘⟨ refl⟩∘⟨ _≅_.isoˡ (unflatten-flatten-≈ B) ⟩∘⟨refl ⟩
      F-C ∘ g ∘ id ∘ f ∘ T-A
        ≈⟨ refl⟩∘⟨ refl⟩∘⟨ FM.identityˡ ⟩
      F-C ∘ g ∘ f ∘ T-A
        ≈⟨ refl⟩∘⟨ FM.sym-assoc ⟩
      F-C ∘ (g ∘ f) ∘ T-A
        ∎

-- Helper for L9: distribute ⊗ over the (≅.from ∘ _ ∘ ≅.to)
-- composition that defines `bridge`.
bridge-⊗-decompose
  : ∀ {A B C D} (f : HomTerm A B) (g : HomTerm C D)
  → bridge f ⊗₁ bridge g
  ≈Term ( _≅_.from (unflatten-flatten-≈ B) ⊗₁ _≅_.from (unflatten-flatten-≈ D))
       ∘ ((f ⊗₁ g) ∘ ( _≅_.to (unflatten-flatten-≈ A) ⊗₁ _≅_.to (unflatten-flatten-≈ C)))
bridge-⊗-decompose {A} {B} {C} {D} f g = begin
  (F-B ∘ f ∘ T-A) ⊗₁ (F-D ∘ g ∘ T-C)
    ≈⟨ ⊗-∘-dist ⟩
  F-B ⊗₁ F-D ∘ ((f ∘ T-A) ⊗₁ (g ∘ T-C))
    ≈⟨ refl⟩∘⟨ ⊗-∘-dist ⟩
  F-B ⊗₁ F-D ∘ ((f ⊗₁ g) ∘ (T-A ⊗₁ T-C))
    ∎
  where
    F-B = _≅_.from (unflatten-flatten-≈ B)
    F-D = _≅_.from (unflatten-flatten-≈ D)
    T-A = _≅_.to   (unflatten-flatten-≈ A)
    T-C = _≅_.to   (unflatten-flatten-≈ C)

-- L9: `bridge` distributes over tensor (modulo the ~unflatten-++-≅~
-- coherence iso connecting `unflatten (xs ++ ys)` to
-- `unflatten xs ⊗₀ unflatten ys`).  Combined with the IH and an
-- L7-shape lemma about `decode-attempt-hTensor`, this closes
-- `decode-roundtrip-⊗₁`.
--
-- The chain unfolds `bridge (f ⊗₁ g)` (which involves
-- `unflatten-flatten-≈ (B ⊗₀ D) = ≅.trans (u-B ⊗ᵢ u-D) (≅.sym
-- coh-B-D)`) into the tensor product of the bridges, plus the
-- `coh-B-D.to` and `coh-A-C.from` wrappings.
bridge-⊗
  : ∀ {A B C D} (f : HomTerm A B) (g : HomTerm C D)
  → bridge (f ⊗₁ g)
  ≈Term _≅_.to   (unflatten-++-≅ (flatten B) (flatten D))
       ∘ (bridge f ⊗₁ bridge g)
       ∘ _≅_.from (unflatten-++-≅ (flatten A) (flatten C))
bridge-⊗ {A} {B} {C} {D} f g = begin
  -- bridge (f ⊗₁ g) reduces (definitionally) to:
  (cBD-to ∘ F-B ⊗₁ F-D) ∘ (f ⊗₁ g) ∘ ((T-A ⊗₁ T-C) ∘ cAC-from)
    ≈⟨ FM.assoc ⟩
  cBD-to ∘ (F-B ⊗₁ F-D) ∘ ((f ⊗₁ g) ∘ ((T-A ⊗₁ T-C) ∘ cAC-from))
    ≈⟨ refl⟩∘⟨ refl⟩∘⟨ FM.sym-assoc ⟩
  cBD-to ∘ (F-B ⊗₁ F-D) ∘ ((f ⊗₁ g) ∘ (T-A ⊗₁ T-C)) ∘ cAC-from
    ≈⟨ refl⟩∘⟨ FM.sym-assoc ⟩
  cBD-to ∘ ((F-B ⊗₁ F-D) ∘ ((f ⊗₁ g) ∘ (T-A ⊗₁ T-C))) ∘ cAC-from
    ≈⟨ refl⟩∘⟨ ≈-Term-sym (bridge-⊗-decompose f g) ⟩∘⟨refl ⟩
  cBD-to ∘ (bridge f ⊗₁ bridge g) ∘ cAC-from
    ∎
  where
    F-B    = _≅_.from (unflatten-flatten-≈ B)
    F-D    = _≅_.from (unflatten-flatten-≈ D)
    T-A    = _≅_.to   (unflatten-flatten-≈ A)
    T-C    = _≅_.to   (unflatten-flatten-≈ C)
    cBD-to = _≅_.to   (unflatten-++-≅ (flatten B) (flatten D))
    cAC-from = _≅_.from (unflatten-++-≅ (flatten A) (flatten C))

--------------------------------------------------------------------------------
-- Per-constructor roundtrip lemmas.  Some are still postulated; the
-- "easy" ones are proved by direct categorical reasoning that follows
-- from the structure of `decode-attempt-h*`.
--
-- The composite cases `decode-roundtrip-∘` and `decode-roundtrip-⊗₁`
-- as well as the atomic cases involving non-trivial coherence
-- (`Agen`, `σ`, `ρ⇒`/`ρ⇐`/`α⇒`/`α⇐`) are still postulated — their
-- proofs require unfolding `decode-attempt-hCompose` /
-- `decode-attempt-hTensor` / `decode-attempt-hSwap` /
-- `decode-attempt-subst₂` and chasing the resulting categorical chain.
-- *Cluster C structure postulates* (L6 / L7 from the Step 5-A plan).
-- These characterise how `decode-attempt-hCompose` and
-- `decode-attempt-hTensor` decompose into sub-hypergraph contributions.
-- Combined with `bridge-∘` / `bridge-⊗` and the inductive hypotheses,
-- they make the corresponding `decode-roundtrip-{∘,⊗₁}` axioms below
-- fully constructive.
postulate
  decode-∘-shape
    : ∀ {A B C} (g : HomTerm B C) (f : HomTerm A B)
    → decode (g ∘ f) ≈Term decode g ∘ decode f

  decode-⊗-shape
    : ∀ {A B C D} (f : HomTerm A B) (g : HomTerm C D)
    → decode (f ⊗₁ g)
    ≈Term _≅_.to   (unflatten-++-≅ (flatten B) (flatten D))
         ∘ (decode f ⊗₁ decode g)
         ∘ _≅_.from (unflatten-++-≅ (flatten A) (flatten C))

postulate
  decode-roundtrip-Agen
    : ∀ {A B} (g : mor A B) → decode (Agen g) ≈Term bridge (Agen g)

  decode-roundtrip-σ
    : ∀ {A B} ⦃ s : Symm ≤ Symm ⦄
    → decode (σ {A = A} {B = B} ⦃ s ⦄) ≈Term bridge (σ {A = A} {B = B} ⦃ s ⦄)

-- `decode-roundtrip-∘` is now constructive: chain `decode-∘-shape`
-- (peels apart `decode (g ∘ f)`), the IHs, and `bridge-∘` (in
-- reverse) to land at `bridge (g ∘ f)`.

decode-roundtrip-∘
  : ∀ {A B C} (g : HomTerm B C) (f : HomTerm A B)
  → decode g ≈Term bridge g
  → decode f ≈Term bridge f
  → decode (g ∘ f) ≈Term bridge (g ∘ f)
decode-roundtrip-∘ {A} {B} {C} g f IH-g IH-f = begin
  decode (g ∘ f)         ≈⟨ decode-∘-shape g f ⟩
  decode g ∘ decode f    ≈⟨ ∘-resp-≈ IH-g IH-f ⟩
  bridge g ∘ bridge f    ≈⟨ bridge-∘ g f ⟨
  bridge (g ∘ f)         ∎

-- `decode-roundtrip-⊗₁` is now constructive: chain
-- `decode-⊗-shape` (peels apart `decode (f ⊗₁ g)` keeping its
-- coherence wrappers), the IHs (under the wrapper), and `bridge-⊗`
-- (in reverse) to land at `bridge (f ⊗₁ g)`.

decode-roundtrip-⊗₁
  : ∀ {A B C D} (f : HomTerm A B) (g : HomTerm C D)
  → decode f ≈Term bridge f
  → decode g ≈Term bridge g
  → decode (f ⊗₁ g) ≈Term bridge (f ⊗₁ g)
decode-roundtrip-⊗₁ {A} {B} {C} {D} f g IH-f IH-g = begin
  decode (f ⊗₁ g)
    ≈⟨ decode-⊗-shape f g ⟩
  cBD-to ∘ (decode f ⊗₁ decode g) ∘ cAC-from
    ≈⟨ refl⟩∘⟨ ⊗-resp-≈ IH-f IH-g ⟩∘⟨refl ⟩
  cBD-to ∘ (bridge f ⊗₁ bridge g) ∘ cAC-from
    ≈⟨ bridge-⊗ f g ⟨
  bridge (f ⊗₁ g)
    ∎
  where
    cBD-to   = _≅_.to   (unflatten-++-≅ (flatten B) (flatten D))
    cAC-from = _≅_.from (unflatten-++-≅ (flatten A) (flatten C))

--------------------------------------------------------------------------------
-- Layer 2 of the Step 5-A plan: `decode-id-is-id`.
--
-- Both `decode (id {A})` and `bridge (id {A})` reduce to `id` (in the
-- appropriate type).  This is the shared logic for *all* Cluster A
-- axioms (`id`, `λ⇒`, `λ⇐`, `ρ⇒`, `ρ⇐`, `α⇒`, `α⇐`): each will reuse
-- `decode-id-is-id` for the decode side and a constructor-specific
-- `bridge-X-is-id` chain for the bridge side.

-- `decode (id {A}) ≈Term id` by induction on `A`.
--   * `unit`: `decode (id {unit})` reduces to `(id ∘ id) ∘ id` ≈ id
--     by `idʳ` + `idˡ`.
--   * `Var x`: `decode (id {Var x})` reduces to
--     `((id ⊗₁ id) ∘ ((id ⊗₁ id) ∘ id)) ∘ id` ≈ id by `idʳ` +
--     `id⊗id≈id` + `idˡ` + `idʳ` + `id⊗id≈id`.
--   * `A ⊗₀ B`: definitionally equal to `decode (id {A} ⊗₁ id {B})`;
--     use `decode-⊗-shape` + IH on A and B + `id⊗id≈id` + iso law on
--     `unflatten-++-≅`.

decode-id-is-id : ∀ A → decode (id {A}) ≈Term id
decode-id-is-id unit = begin
  (id ∘ id) ∘ id   ≈⟨ idʳ ⟩
  id ∘ id          ≈⟨ idˡ ⟩
  id               ∎
decode-id-is-id (Var x) = begin
  ((id ⊗₁ id) ∘ ((id ⊗₁ id) ∘ id)) ∘ id
                                    ≈⟨ idʳ ⟩
  (id ⊗₁ id) ∘ ((id ⊗₁ id) ∘ id)    ≈⟨ id⊗id≈id ⟩∘⟨refl ⟩
  id ∘ ((id ⊗₁ id) ∘ id)            ≈⟨ idˡ ⟩
  (id ⊗₁ id) ∘ id                   ≈⟨ idʳ ⟩
  id ⊗₁ id                          ≈⟨ id⊗id≈id ⟩
  id                                ∎
decode-id-is-id (A ⊗₀ B) = begin
  decode (id {A ⊗₀ B})
    ≈⟨ decode-⊗-shape (id {A}) (id {B}) ⟩
  cAB-to ∘ (decode (id {A}) ⊗₁ decode (id {B})) ∘ cAB-from
    ≈⟨ refl⟩∘⟨ ⊗-resp-≈ (decode-id-is-id A) (decode-id-is-id B) ⟩∘⟨refl ⟩
  cAB-to ∘ (id ⊗₁ id) ∘ cAB-from
    ≈⟨ refl⟩∘⟨ id⊗id≈id ⟩∘⟨refl ⟩
  cAB-to ∘ id ∘ cAB-from
    ≈⟨ refl⟩∘⟨ idˡ ⟩
  cAB-to ∘ cAB-from
    ≈⟨ _≅_.isoˡ (unflatten-++-≅ (flatten A) (flatten B)) ⟩
  id
    ∎
  where
    cAB-to   = _≅_.to   (unflatten-++-≅ (flatten A) (flatten B))
    cAB-from = _≅_.from (unflatten-++-≅ (flatten A) (flatten B))

--------------------------------------------------------------------------------
-- `bridge (id {A}) ≈Term id`: the iso `unflatten-flatten-≈ A` cancels.

bridge-id-is-id : ∀ A → bridge (id {A}) ≈Term id
bridge-id-is-id A = begin
  _≅_.from (unflatten-flatten-≈ A) ∘ id ∘ _≅_.to (unflatten-flatten-≈ A)
    ≈⟨ refl⟩∘⟨ idˡ ⟩
  _≅_.from (unflatten-flatten-≈ A) ∘ _≅_.to (unflatten-flatten-≈ A)
    ≈⟨ _≅_.isoʳ (unflatten-flatten-≈ A) ⟩
  id ∎

--------------------------------------------------------------------------------
-- Wire Cluster A's `id` axiom: combine `decode-id-is-id` + sym
-- `bridge-id-is-id`.

decode-roundtrip-id
  : ∀ {A} → decode (id {A}) ≈Term bridge (id {A})
decode-roundtrip-id {A} = begin
  decode (id {A})  ≈⟨ decode-id-is-id A ⟩
  id               ≈⟨ bridge-id-is-id A ⟨
  bridge (id {A})  ∎

--------------------------------------------------------------------------------
-- λ⇒ / λ⇐.  `⟪ λ⇒ {A} ⟫ = hId A` (definitionally), so
-- `decode (λ⇒ {A}) = decode (id {A})`; we reuse `decode-id-is-id`.
-- The bridge side reduces to `id` via λ-naturality + λ⇒∘λ⇐≈id +
-- iso laws on `unflatten-flatten-≈ A`.
--
-- bridge (λ⇒ {A}) reduces (definitionally, via the unfolding of
-- `unflatten-flatten-≈ (unit ⊗₀ A) = ≅.trans (≅.refl ⊗ᵢ u-A)
-- (≅.sym (unflatten-++-≅ [] (flatten A)))`) to:
--   ≅.from u-A ∘ λ⇒ ∘ (id ⊗₁ ≅.to u-A) ∘ λ⇐
-- The chain below transforms this into `id`.

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

decode-roundtrip-λ⇒
  : ∀ {A} → decode (λ⇒ {A}) ≈Term bridge (λ⇒ {A})
decode-roundtrip-λ⇒ {A} = begin
  decode (λ⇒ {A})  ≈⟨ decode-id-is-id A ⟩
  id               ≈⟨ bridge-λ⇒-is-id A ⟨
  bridge (λ⇒ {A})  ∎

-- bridge (λ⇐ {A}) reduces (via ≅.from u-(unit ⊗₀ A) = λ⇒ ∘ (id ⊗₁ F-A)) to:
--   (λ⇒ ∘ (id ⊗₁ F-A)) ∘ (λ⇐ ∘ T-A)   [outer composition is the
--                                       ≅.from-then-rest split, NOT
--                                       fully right-associated]
-- Chase to id.

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

decode-roundtrip-λ⇐
  : ∀ {A} → decode (λ⇐ {A}) ≈Term bridge (λ⇐ {A})
decode-roundtrip-λ⇐ {A} = begin
  decode (λ⇐ {A})  ≈⟨ decode-id-is-id A ⟩
  id               ≈⟨ bridge-λ⇐-is-id A ⟨
  bridge (λ⇐ {A})  ∎

--------------------------------------------------------------------------------
-- *Layer 4 — `subst₂` shape lemmas (Issue 1 partial fix).*
-- With the generalised `decode-attempt-subst₂` (now exposing the
-- transport explicitly via `subst₂ HomTerm`), `decode (ρ⇒ {A})` etc.
-- are no longer opaque — they reduce to a `subst₂`-of-id form.

-- The four `decode-{ρ⇒,ρ⇐,α⇒,α⇐}-shape` lemmas are now PROVEN
-- (postulate-free).  They are PURE boundary-`subst₂` ALGEBRA, NOT
-- process-edges content:
--   `⟪ ρ⇒ {A} ⟫ = hId (A ⊗₀ unit) = ⟪ id {A ⊗₀ unit} ⟫`, and
--   `⟪ α⇒ {A}{B}{C} ⟫ = hId ((A ⊗₀ B) ⊗₀ C) = ⟪ id {(A ⊗₀ B) ⊗₀ C} ⟫`,
-- so `decode-attempt-Linear (ρ⇒/α⇒)` and `decode-attempt-Linear (id …)`
-- are DEFINITIONALLY the SAME `decode-attempt-hId …`.  The two decoders
-- therefore share the SAME inner term `proj₁ (… decode-attempt-hId …)`
-- and differ ONLY in the boundary equations supplied to `decode`'s
-- `subst₂`.  Per `FromAPROP`:
--   ⟪⟫-codL (ρ⇒ {A})       = ≡-trans (codL-hId (A ⊗₀ unit))     (++-identityʳ …)
--   ⟪⟫-domL (ρ⇐ {A})       = ≡-trans (domL-hId (A ⊗₀ unit))     (++-identityʳ …)
--   ⟪⟫-codL (α⇒ {A}{B}{C})  = ≡-trans (codL-hId ((A⊗B)⊗C))       (++-assoc …)
--   ⟪⟫-domL (α⇐ {A}{B}{C})  = ≡-trans (domL-hId ((A⊗B)⊗C))       (++-assoc …)
-- (the OTHER boundary is `codL-hId/domL-hId` alone — same as for `id`),
-- and the generic `subst₂`-over-`trans` split below (`--with-K`, by
-- `refl`-pattern, hence TRUE for ALL instances) peels exactly the
-- trailing `++-identityʳ`/`++-assoc`.  Clone of `rhoShapeResidual`
-- (`Discharge/DecodeRelDecodeP.agda`).

private
  -- Generic: a `subst₂` whose cod equation factors as `≡-trans q r`
  -- splits as the outer `r`-transport of the inner `q`-transport.
  -- (`--with-K`; TRUE for every `p`, `q`, `r`, `x`.)
  subst₂-cod-trans
    : ∀ {as as' bs bs' bs'' : List X}
        (p : as ≡ as') (q : bs ≡ bs') (r : bs' ≡ bs'')
        (x : HomTerm (unflatten as) (unflatten bs))
    → subst₂ HomTerm (cong unflatten p) (cong unflatten (≡-trans q r)) x
      ≡ subst₂ HomTerm refl (cong unflatten r)
               (subst₂ HomTerm (cong unflatten p) (cong unflatten q) x)
  subst₂-cod-trans refl refl refl x = refl

  -- Symmetric: a `subst₂` whose dom equation factors as `≡-trans q r`.
  subst₂-dom-trans
    : ∀ {as as' as'' bs bs' : List X}
        (q : as ≡ as') (r : as' ≡ as'') (p : bs ≡ bs')
        (x : HomTerm (unflatten as) (unflatten bs))
    → subst₂ HomTerm (cong unflatten (≡-trans q r)) (cong unflatten p) x
      ≡ subst₂ HomTerm (cong unflatten r) refl
               (subst₂ HomTerm (cong unflatten q) (cong unflatten p) x)
  subst₂-dom-trans refl refl refl x = refl

decode-ρ⇒-shape
  : ∀ A → decode (ρ⇒ {A})
       ≡ subst₂ HomTerm refl (cong unflatten (++-identityʳ (flatten A)))
                (decode (id {A ⊗₀ unit}))
decode-ρ⇒-shape A =
  subst₂-cod-trans (domL-hId (A ⊗₀ unit)) (codL-hId (A ⊗₀ unit))
                   (++-identityʳ (flatten A))
                   (proj₁ (decode-attempt-hId (A ⊗₀ unit)))

decode-ρ⇐-shape
  : ∀ A → decode (ρ⇐ {A})
       ≡ subst₂ HomTerm (cong unflatten (++-identityʳ (flatten A))) refl
                (decode (id {A ⊗₀ unit}))
decode-ρ⇐-shape A =
  subst₂-dom-trans (domL-hId (A ⊗₀ unit)) (++-identityʳ (flatten A))
                   (codL-hId (A ⊗₀ unit))
                   (proj₁ (decode-attempt-hId (A ⊗₀ unit)))

decode-α⇒-shape
  : ∀ A B C → decode (α⇒ {A} {B} {C})
           ≡ subst₂ HomTerm refl
                    (cong unflatten (++-assoc (flatten A) (flatten B) (flatten C)))
                    (decode (id {(A ⊗₀ B) ⊗₀ C}))
decode-α⇒-shape A B C =
  subst₂-cod-trans (domL-hId ((A ⊗₀ B) ⊗₀ C)) (codL-hId ((A ⊗₀ B) ⊗₀ C))
                   (++-assoc (flatten A) (flatten B) (flatten C))
                   (proj₁ (decode-attempt-hId ((A ⊗₀ B) ⊗₀ C)))

decode-α⇐-shape
  : ∀ A B C → decode (α⇐ {A} {B} {C})
           ≡ subst₂ HomTerm
                    (cong unflatten (++-assoc (flatten A) (flatten B) (flatten C)))
                    refl
                    (decode (id {(A ⊗₀ B) ⊗₀ C}))
decode-α⇐-shape A B C =
  subst₂-dom-trans (domL-hId ((A ⊗₀ B) ⊗₀ C))
                   (++-assoc (flatten A) (flatten B) (flatten C))
                   (codL-hId ((A ⊗₀ B) ⊗₀ C))
                   (proj₁ (decode-attempt-hId ((A ⊗₀ B) ⊗₀ C)))

--------------------------------------------------------------------------------
-- Helpers for chaining `_≡_` and `≈Term` and for transporting `≈Term`
-- equations across `subst₂`.

≡⇒≈Term : ∀ {A B} {f g : HomTerm A B} → f ≡ g → f ≈Term g
≡⇒≈Term refl = ≈-Term-refl

subst₂-resp-≈Term
  : ∀ {As Bs As' Bs' : List X} (eq-As : As ≡ As') (eq-Bs : Bs ≡ Bs')
      {f g : HomTerm (unflatten As) (unflatten Bs)}
  → f ≈Term g
  → subst₂ HomTerm (cong unflatten eq-As) (cong unflatten eq-Bs) f
    ≈Term subst₂ HomTerm (cong unflatten eq-As) (cong unflatten eq-Bs) g
subst₂-resp-≈Term refl refl f≈g = f≈g

--------------------------------------------------------------------------------
-- Issue 2: discharging the ρ/α coherence postulates by Kelly's theorems.
-- With the `subst₂ HomTerm` shape exposed for `decode (X)`, and
-- `decode-id-is-id` providing the inner reduction to `id`, the
-- remaining gap is a coherence-theorem statement: the transported `id`
-- (a "free" coherence iso) equals the explicit `bridge (X)` chain
-- (a "specific" coherence iso) modulo `≈Term`.  We prove these using
-- Kelly's coherence theorems from
-- `Categories.Category.Monoidal.Properties.Kelly's` (`coherence₂`,
-- `coherence-inv₂`, `coherence₃`, `coherence-inv₃`) plus structural
-- induction on the underlying flattened list.

--------------------------------------------------------------------
-- Helper lemmas about `subst` of `id` along `cong unflatten`-shaped
-- equations.  These are the workhorses for moving the transports
-- past the recursive `unflatten`-structure.

private
  -- Bridge: `subst₂ HomTerm refl (cong unflatten q) id ≡ subst (λ z →
  -- HomTerm (unflatten As) (unflatten z)) q id`.  Goes from the
  -- postulate's `subst₂` form (with `cong unflatten`) to the
  -- `subst`-of-codomain form used in induction.
  subst₂-refl-cod
    : ∀ {As As' : List X} (eq : As ≡ As')
    → subst₂ HomTerm refl (cong unflatten eq) (id {unflatten As})
    ≡ subst (λ z → HomTerm (unflatten As) (unflatten z)) eq id
  subst₂-refl-cod refl = refl

  -- Symmetric: source-side transport.
  subst₂-refl-dom
    : ∀ {As As' : List X} (eq : As ≡ As')
    → subst₂ HomTerm (cong unflatten eq) refl (id {unflatten As})
    ≡ subst (λ z → HomTerm (unflatten z) (unflatten As)) eq id
  subst₂-refl-dom refl = refl

  -- Push `subst (cod := unflatten z)` past `Var y ⊗₀_`.  For `eq =
  -- refl`, the LHS reduces to `id` and the RHS to `id ⊗₁ id`; the
  -- equation is by `id⊗id≈id`.
  subst-cod-cons
    : ∀ (y : X) {as as' : List X} (eq : as ≡ as')
    → subst (λ z → HomTerm (Var y ⊗₀ unflatten as) (Var y ⊗₀ unflatten z)) eq id
    ≈Term id {Var y} ⊗₁ subst (λ z → HomTerm (unflatten as) (unflatten z)) eq id
  subst-cod-cons y refl = ≈-Term-sym id⊗id≈id

  subst-dom-cons
    : ∀ (y : X) {as as' : List X} (eq : as ≡ as')
    → subst (λ z → HomTerm (Var y ⊗₀ unflatten z) (Var y ⊗₀ unflatten as)) eq id
    ≈Term id {Var y} ⊗₁ subst (λ z → HomTerm (unflatten z) (unflatten as)) eq id
  subst-dom-cons y refl = ≈-Term-sym id⊗id≈id

--------------------------------------------------------------------
-- Bridge simplification for ρ⇒.  After unfolding `bridge` and using
-- ρ⇒-naturality + the `unflatten-flatten-≈ A` iso law, the bridge
-- reduces to `ρ⇒ {unflatten (flatten A)} ∘ ≅.from (unflatten-++-≅
-- (flatten A) [])`.

bridge-ρ⇒-form
  : ∀ A → bridge (ρ⇒ {A})
       ≈Term ρ⇒ {unflatten (flatten A)}
              ∘ _≅_.from (unflatten-++-≅ (flatten A) [])
bridge-ρ⇒-form A = begin
  F-A ∘ ρ⇒ ∘ (T-A ⊗₁ id) ∘ cAA-from
    ≈⟨ refl⟩∘⟨ FM.sym-assoc ⟩
  F-A ∘ (ρ⇒ ∘ (T-A ⊗₁ id)) ∘ cAA-from
    ≈⟨ refl⟩∘⟨ ρ⇒∘f⊗id≈f∘ρ⇒ ⟩∘⟨refl ⟩
  F-A ∘ (T-A ∘ ρ⇒) ∘ cAA-from
    ≈⟨ refl⟩∘⟨ FM.assoc ⟩
  F-A ∘ T-A ∘ ρ⇒ ∘ cAA-from
    ≈⟨ FM.sym-assoc ⟩
  (F-A ∘ T-A) ∘ ρ⇒ ∘ cAA-from
    ≈⟨ _≅_.isoʳ (unflatten-flatten-≈ A) ⟩∘⟨refl ⟩
  id ∘ ρ⇒ ∘ cAA-from
    ≈⟨ idˡ ⟩
  ρ⇒ ∘ cAA-from ∎
  where
    F-A = _≅_.from (unflatten-flatten-≈ A)
    T-A = _≅_.to   (unflatten-flatten-≈ A)
    cAA-from = _≅_.from (unflatten-++-≅ (flatten A) [])

--------------------------------------------------------------------
-- ρ⇐-naturality, derived from ρ⇒-naturality via the iso law.
-- (FreeMonoidal exposes only `ρ⇒∘f⊗id≈f∘ρ⇒`; the ⇐ side comes from
-- pre/post-composing with ρ⇒ ∘ ρ⇐ ≈ id and the like.)

ρ⇐-naturality
  : ∀ {A B} (f : HomTerm A B)
  → ρ⇐ {B} ∘ f ≈Term f ⊗₁ id ∘ ρ⇐ {A}
ρ⇐-naturality f = begin
  ρ⇐ ∘ f
    ≈⟨ ≈-Term-sym idʳ ⟩
  (ρ⇐ ∘ f) ∘ id
    ≈⟨ refl⟩∘⟨ ≈-Term-sym ρ⇒∘ρ⇐≈id ⟩
  (ρ⇐ ∘ f) ∘ ρ⇒ ∘ ρ⇐
    ≈⟨ FM.sym-assoc ⟩
  ((ρ⇐ ∘ f) ∘ ρ⇒) ∘ ρ⇐
    ≈⟨ FM.assoc ⟩∘⟨refl ⟩
  (ρ⇐ ∘ f ∘ ρ⇒) ∘ ρ⇐
    ≈⟨ (refl⟩∘⟨ ≈-Term-sym ρ⇒∘f⊗id≈f∘ρ⇒) ⟩∘⟨refl ⟩
  (ρ⇐ ∘ ρ⇒ ∘ f ⊗₁ id) ∘ ρ⇐
    ≈⟨ FM.sym-assoc ⟩∘⟨refl ⟩
  ((ρ⇐ ∘ ρ⇒) ∘ f ⊗₁ id) ∘ ρ⇐
    ≈⟨ (ρ⇐∘ρ⇒≈id ⟩∘⟨refl) ⟩∘⟨refl ⟩
  (id ∘ f ⊗₁ id) ∘ ρ⇐
    ≈⟨ idˡ ⟩∘⟨refl ⟩
  f ⊗₁ id ∘ ρ⇐ ∎

--------------------------------------------------------------------
-- Bridge simplification for ρ⇐ (symmetric to ρ⇒).
-- bridge (ρ⇐ {A}) ≈Term ≅.to (unflatten-++-≅ (flatten A) []) ∘ ρ⇐.

bridge-ρ⇐-form
  : ∀ A → bridge (ρ⇐ {A})
       ≈Term _≅_.to (unflatten-++-≅ (flatten A) [])
              ∘ ρ⇐ {unflatten (flatten A)}
bridge-ρ⇐-form A = begin
  (cAA-to ∘ F-A ⊗₁ id) ∘ ρ⇐ ∘ T-A
    ≈⟨ FM.assoc ⟩
  cAA-to ∘ (F-A ⊗₁ id) ∘ (ρ⇐ ∘ T-A)
    ≈⟨ refl⟩∘⟨ refl⟩∘⟨ ρ⇐-naturality T-A ⟩
  cAA-to ∘ (F-A ⊗₁ id) ∘ (T-A ⊗₁ id ∘ ρ⇐)
    ≈⟨ refl⟩∘⟨ FM.sym-assoc ⟩
  cAA-to ∘ ((F-A ⊗₁ id) ∘ T-A ⊗₁ id) ∘ ρ⇐
    ≈⟨ refl⟩∘⟨ ≈-Term-sym ⊗-∘-dist ⟩∘⟨refl ⟩
  cAA-to ∘ (F-A ∘ T-A) ⊗₁ (id ∘ id) ∘ ρ⇐
    ≈⟨ refl⟩∘⟨ ⊗-resp-≈ (_≅_.isoʳ (unflatten-flatten-≈ A)) idˡ ⟩∘⟨refl ⟩
  cAA-to ∘ id ⊗₁ id ∘ ρ⇐
    ≈⟨ refl⟩∘⟨ id⊗id≈id ⟩∘⟨refl ⟩
  cAA-to ∘ id ∘ ρ⇐
    ≈⟨ refl⟩∘⟨ idˡ ⟩
  cAA-to ∘ ρ⇐ ∎
  where
    F-A    = _≅_.from (unflatten-flatten-≈ A)
    T-A    = _≅_.to   (unflatten-flatten-≈ A)
    cAA-to = _≅_.to   (unflatten-++-≅ (flatten A) [])

--------------------------------------------------------------------
-- List-coherence for ρ⇒.  Proves that the transport equals the
-- simplified bridge form, by induction on the underlying list.

ρ⇒-coh-list
  : ∀ (xs : List X)
  → subst (λ z → HomTerm (unflatten (xs ++ [])) (unflatten z))
          (++-identityʳ xs) id
    ≈Term ρ⇒ {unflatten xs} ∘ _≅_.from (unflatten-++-≅ xs [])
ρ⇒-coh-list []       = begin
  id           ≈⟨ ≈-Term-sym λ⇒∘λ⇐≈id ⟩
  λ⇒ ∘ λ⇐      ≈⟨ coherence₃ ⟩∘⟨refl ⟩
  ρ⇒ ∘ λ⇐      ∎
ρ⇒-coh-list (y ∷ ys) = begin
  subst (λ z → HomTerm (Var y ⊗₀ unflatten (ys ++ [])) (unflatten z))
        (cong (y ∷_) (++-identityʳ ys)) id
    ≈⟨ ≡⇒≈Term (sym (subst-∘ {P = λ z → HomTerm (Var y ⊗₀ unflatten (ys ++ [])) (unflatten z)}
                              {f = y ∷_}
                              (++-identityʳ ys))) ⟩
  subst (λ z → HomTerm (Var y ⊗₀ unflatten (ys ++ []))
                        (Var y ⊗₀ unflatten z))
        (++-identityʳ ys) id
    ≈⟨ subst-cod-cons y (++-identityʳ ys) ⟩
  id ⊗₁ subst (λ z → HomTerm (unflatten (ys ++ [])) (unflatten z))
              (++-identityʳ ys) id
    ≈⟨ ⊗-resp-≈ ≈-Term-refl (ρ⇒-coh-list ys) ⟩
  id ⊗₁ (ρ⇒ ∘ inner-from)
    ≈⟨ ⊗-resp-≈ (≈-Term-sym idˡ) ≈-Term-refl ⟩
  (id ∘ id) ⊗₁ (ρ⇒ ∘ inner-from)
    ≈⟨ ⊗-∘-dist ⟩
  id ⊗₁ ρ⇒ ∘ id ⊗₁ inner-from
    ≈⟨ ≈-Term-sym idʳ ⟩∘⟨refl ⟩
  (id ⊗₁ ρ⇒ ∘ id) ∘ id ⊗₁ inner-from
    ≈⟨ (refl⟩∘⟨ ≈-Term-sym α⇒∘α⇐≈id) ⟩∘⟨refl ⟩
  (id ⊗₁ ρ⇒ ∘ α⇒ ∘ α⇐) ∘ id ⊗₁ inner-from
    ≈⟨ FM.sym-assoc ⟩∘⟨refl ⟩
  ((id ⊗₁ ρ⇒ ∘ α⇒) ∘ α⇐) ∘ id ⊗₁ inner-from
    ≈⟨ coherence₂ ⟩∘⟨refl ⟩∘⟨refl ⟩
  (ρ⇒ ∘ α⇐) ∘ id ⊗₁ inner-from
    ≈⟨ FM.assoc ⟩
  ρ⇒ ∘ α⇐ ∘ id ⊗₁ inner-from ∎
  where
    inner-from = _≅_.from (unflatten-++-≅ ys [])

--------------------------------------------------------------------
-- ρ⇒-coherence: combine `ρ⇒-coh-list (flatten A)` with
-- `bridge-ρ⇒-form A` via `subst₂-refl-cod` + `subst-∘`.

ρ⇒-coherence
  : ∀ A → subst₂ HomTerm refl (cong unflatten (++-identityʳ (flatten A))) id
       ≈Term bridge (ρ⇒ {A})
ρ⇒-coherence A = begin
  subst₂ HomTerm refl (cong unflatten (++-identityʳ (flatten A))) id
    ≈⟨ ≡⇒≈Term (subst₂-refl-cod (++-identityʳ (flatten A))) ⟩
  subst (λ z → HomTerm (unflatten (flatten A ++ [])) (unflatten z))
        (++-identityʳ (flatten A)) id
    ≈⟨ ρ⇒-coh-list (flatten A) ⟩
  ρ⇒ ∘ _≅_.from (unflatten-++-≅ (flatten A) [])
    ≈⟨ ≈-Term-sym (bridge-ρ⇒-form A) ⟩
  bridge (ρ⇒ {A}) ∎

--------------------------------------------------------------------
-- List-coherence for ρ⇐.

ρ⇐-coh-list
  : ∀ (xs : List X)
  → subst (λ z → HomTerm (unflatten z) (unflatten (xs ++ [])))
          (++-identityʳ xs) id
    ≈Term _≅_.to (unflatten-++-≅ xs []) ∘ ρ⇐ {unflatten xs}
ρ⇐-coh-list []       = begin
  id           ≈⟨ ≈-Term-sym ρ⇒∘ρ⇐≈id ⟩
  ρ⇒ ∘ ρ⇐      ≈⟨ ≈-Term-sym coherence₃ ⟩∘⟨refl ⟩
  λ⇒ ∘ ρ⇐      ∎
ρ⇐-coh-list (y ∷ ys) = begin
  subst (λ z → HomTerm (unflatten z) (Var y ⊗₀ unflatten (ys ++ [])))
        (cong (y ∷_) (++-identityʳ ys)) id
    ≈⟨ ≡⇒≈Term (sym (subst-∘ {P = λ z → HomTerm (unflatten z) (Var y ⊗₀ unflatten (ys ++ []))}
                              {f = y ∷_}
                              (++-identityʳ ys))) ⟩
  subst (λ z → HomTerm (Var y ⊗₀ unflatten z)
                        (Var y ⊗₀ unflatten (ys ++ [])))
        (++-identityʳ ys) id
    ≈⟨ subst-dom-cons y (++-identityʳ ys) ⟩
  id ⊗₁ subst (λ z → HomTerm (unflatten z) (unflatten (ys ++ [])))
              (++-identityʳ ys) id
    ≈⟨ ⊗-resp-≈ ≈-Term-refl (ρ⇐-coh-list ys) ⟩
  id ⊗₁ (inner-to ∘ ρ⇐)
    ≈⟨ ⊗-resp-≈ (≈-Term-sym idˡ) ≈-Term-refl ⟩
  (id ∘ id) ⊗₁ (inner-to ∘ ρ⇐)
    ≈⟨ ⊗-∘-dist ⟩
  id ⊗₁ inner-to ∘ id ⊗₁ ρ⇐
    ≈⟨ refl⟩∘⟨ id⊗ρ⇐-as-α⇒∘ρ⇐ ⟩
  id ⊗₁ inner-to ∘ α⇒ ∘ ρ⇐
    ≈⟨ FM.sym-assoc ⟩
  (id ⊗₁ inner-to ∘ α⇒) ∘ ρ⇐ ∎
  where
    inner-to = _≅_.to (unflatten-++-≅ ys [])

    -- `id ⊗₁ ρ⇐ {unflatten ys} ≈Term α⇒ ∘ ρ⇐ {Var y ⊗₀ unflatten ys}`.
    -- Derived from `coherence-inv₂ : α⇐ ∘ id ⊗₁ ρ⇐ ≈ ρ⇐` by post-composing
    -- with α⇒ and using α⇒ ∘ α⇐ ≈ id.
    id⊗ρ⇐-as-α⇒∘ρ⇐
      : id {Var y} ⊗₁ ρ⇐ {unflatten ys}
        ≈Term α⇒ {Var y} {unflatten ys} {unit} ∘ ρ⇐ {Var y ⊗₀ unflatten ys}
    id⊗ρ⇐-as-α⇒∘ρ⇐ = begin
      id ⊗₁ ρ⇐
        ≈⟨ ≈-Term-sym idˡ ⟩
      id ∘ id ⊗₁ ρ⇐
        ≈⟨ ≈-Term-sym α⇒∘α⇐≈id ⟩∘⟨refl ⟩
      (α⇒ ∘ α⇐) ∘ id ⊗₁ ρ⇐
        ≈⟨ FM.assoc ⟩
      α⇒ ∘ α⇐ ∘ id ⊗₁ ρ⇐
        ≈⟨ refl⟩∘⟨ coherence-inv₂ ⟩
      α⇒ ∘ ρ⇐ ∎

--------------------------------------------------------------------
-- ρ⇐-coherence: combine `ρ⇐-coh-list (flatten A)` with
-- `bridge-ρ⇐-form A` via `subst₂-refl-dom`.

ρ⇐-coherence
  : ∀ A → subst₂ HomTerm (cong unflatten (++-identityʳ (flatten A))) refl id
       ≈Term bridge (ρ⇐ {A})
ρ⇐-coherence A = begin
  subst₂ HomTerm (cong unflatten (++-identityʳ (flatten A))) refl id
    ≈⟨ ≡⇒≈Term (subst₂-refl-dom (++-identityʳ (flatten A))) ⟩
  subst (λ z → HomTerm (unflatten z) (unflatten (flatten A ++ [])))
        (++-identityʳ (flatten A)) id
    ≈⟨ ρ⇐-coh-list (flatten A) ⟩
  _≅_.to (unflatten-++-≅ (flatten A) []) ∘ ρ⇐
    ≈⟨ ≈-Term-sym (bridge-ρ⇐-form A) ⟩
  bridge (ρ⇐ {A}) ∎

--------------------------------------------------------------------
-- α⇒-coherence and α⇐-coherence by direct manual derivation.
--
-- Strategy: define `α⇒-form-list xsA xsB xsC` as the simple recursive
-- "id-tower" form (which is the canonical id-transport along the
-- propositional `++-assoc` equation).  The list-induction on the
-- LHS becomes trivial (analogous to ρ).  The bridge form
-- `bridge (α⇒ {A}{B}{C}) ≈Term α⇒-form-list (flatten A) (flatten B)
-- (flatten C)` is proved by induction on the *tree structure* of `A`
-- (not on the flat list).  The base cases (A = unit, A = Var x) chase
-- through `unflatten-flatten-≈ unit/Var` directly using λ/ρ
-- naturality + Kelly's `coherence₁` + iso laws.  The ⊗ case uses the
-- `bridge-∘-like` decomposition combined with the pentagon identity
-- and α-naturality.

-- The simple id-tower form: `α⇒-form-list xs ys zs` is the canonical
-- iso `unflatten ((xs ++ ys) ++ zs) ⇒ unflatten (xs ++ ys ++ zs)`.
-- Defined recursively on `xs`: at the base (xs = []) both source and
-- target reduce to `unflatten (ys ++ zs)` so `id` works; at the cons
-- step we wrap with `id ⊗₁`.
α⇒-form-list
  : (xs ys zs : List X)
  → HomTerm (unflatten ((xs ++ ys) ++ zs)) (unflatten (xs ++ ys ++ zs))
α⇒-form-list []       ys zs = id
α⇒-form-list (x ∷ xs) ys zs = id {Var x} ⊗₁ α⇒-form-list xs ys zs

-- The α⇐ counterpart: same shape, opposite direction.  Source/target
-- are flipped.
α⇐-form-list
  : (xs ys zs : List X)
  → HomTerm (unflatten (xs ++ ys ++ zs)) (unflatten ((xs ++ ys) ++ zs))
α⇐-form-list []       ys zs = id
α⇐-form-list (x ∷ xs) ys zs = id {Var x} ⊗₁ α⇐-form-list xs ys zs

-- List induction for α⇒: trivial — both LHS and RHS reduce
-- definitionally with `subst-cod-cons` and the recursive definition.
α⇒-coh-list
  : ∀ (xs ys zs : List X)
  → subst (λ z → HomTerm (unflatten ((xs ++ ys) ++ zs)) (unflatten z))
          (++-assoc xs ys zs) id
    ≈Term α⇒-form-list xs ys zs
α⇒-coh-list []       ys zs = ≈-Term-refl
α⇒-coh-list (x ∷ xs) ys zs = begin
  subst (λ z → HomTerm (Var x ⊗₀ unflatten ((xs ++ ys) ++ zs)) (unflatten z))
        (cong (x ∷_) (++-assoc xs ys zs)) id
    ≈⟨ ≡⇒≈Term (sym (subst-∘ {P = λ z → HomTerm (Var x ⊗₀ unflatten ((xs ++ ys) ++ zs)) (unflatten z)}
                              {f = x ∷_}
                              (++-assoc xs ys zs))) ⟩
  subst (λ z → HomTerm (Var x ⊗₀ unflatten ((xs ++ ys) ++ zs))
                        (Var x ⊗₀ unflatten z))
        (++-assoc xs ys zs) id
    ≈⟨ subst-cod-cons x (++-assoc xs ys zs) ⟩
  id {Var x} ⊗₁ subst (λ z → HomTerm (unflatten ((xs ++ ys) ++ zs)) (unflatten z))
                       (++-assoc xs ys zs) id
    ≈⟨ ⊗-resp-≈ ≈-Term-refl (α⇒-coh-list xs ys zs) ⟩
  id ⊗₁ α⇒-form-list xs ys zs ∎

-- Symmetric list induction for α⇐.
α⇐-coh-list
  : ∀ (xs ys zs : List X)
  → subst (λ z → HomTerm (unflatten z) (unflatten ((xs ++ ys) ++ zs)))
          (++-assoc xs ys zs) id
    ≈Term α⇐-form-list xs ys zs
α⇐-coh-list []       ys zs = ≈-Term-refl
α⇐-coh-list (x ∷ xs) ys zs = begin
  subst (λ z → HomTerm (unflatten z) (Var x ⊗₀ unflatten ((xs ++ ys) ++ zs)))
        (cong (x ∷_) (++-assoc xs ys zs)) id
    ≈⟨ ≡⇒≈Term (sym (subst-∘ {P = λ z → HomTerm (unflatten z) (Var x ⊗₀ unflatten ((xs ++ ys) ++ zs))}
                              {f = x ∷_}
                              (++-assoc xs ys zs))) ⟩
  subst (λ z → HomTerm (Var x ⊗₀ unflatten z)
                        (Var x ⊗₀ unflatten ((xs ++ ys) ++ zs)))
        (++-assoc xs ys zs) id
    ≈⟨ subst-dom-cons x (++-assoc xs ys zs) ⟩
  id {Var x} ⊗₁ subst (λ z → HomTerm (unflatten z) (unflatten ((xs ++ ys) ++ zs)))
                       (++-assoc xs ys zs) id
    ≈⟨ ⊗-resp-≈ ≈-Term-refl (α⇐-coh-list xs ys zs) ⟩
  id ⊗₁ α⇐-form-list xs ys zs ∎

-- Bridge form for α⇒: `bridge (α⇒ {A}{B}{C}) ≈Term α⇒-form-list
-- (flatten A) (flatten B) (flatten C)` by induction on `A`.
--
-- Base case A = unit: bridge (α⇒ {unit}{B}{C}) chases through
-- `unflatten-flatten-≈ unit = ≅.refl` + `unflatten-++-≅ [] ys = ≅.sym
-- unitorˡ`, applies `coherence₁` (λ⇒ ∘ α⇒ ≈ λ⇒ ⊗₁ id) plus λ-naturality
-- and the iso law on `unflatten-++-≅ (flatten B) (flatten C)`, ending
-- at `id`.
--
-- Base case A = Var x: similar but with `unflatten-flatten-≈ (Var x) =
-- ≅.sym unitorʳ`.  The α⇒ at type `(Var x ⊗ B) ⊗ C ⇒ Var x ⊗ (B ⊗ C)`
-- collapses via Kelly's `coherence₂` + ρ-naturality.
--
-- Inductive case A = A1 ⊗ A2: uses `bridge-∘`-style decomposition +
-- pentagon to relate `bridge (α⇒ {A1⊗A2}{B}{C})` to a tower built
-- from the IHs on A1 and A2.

-- We need Kelly's `coherence₁` (and its inverse) for the unit-case
-- chains.
open Kelly's using (coherence₁; coherence-inv₁)

-- Local wrapper for `triangle-inv` to ensure unification with our
-- HomTerm constructors (Agda's `Monoidal.associator.to` doesn't
-- always reduce to `α⇐` directly during unification).
private
  triangle-inv-local
    : ∀ {X Y : ObjTerm}
    → α⇐ {X} {unit} {Y} ∘ id ⊗₁ λ⇐ ≈Term ρ⇐ ⊗₁ id
  triangle-inv-local = triangle-inv

-- α⇒-form-list and α⇐-form-list are mutual inverses (both are
-- "id-towers" between propositionally-equal-via-++-assoc types).
-- This lets us derive the α⇐ side from the α⇒ side via a single
-- categorical argument (using bridge-∘ + α⇒∘α⇐≈id), eliminating the
-- need for separate manual proofs of the α⇐ unit/Var/⊗ cases.

α⇒-α⇐-iso
  : ∀ (xs ys zs : List X)
  → α⇒-form-list xs ys zs ∘ α⇐-form-list xs ys zs ≈Term id
α⇒-α⇐-iso []       ys zs = idˡ
α⇒-α⇐-iso (x ∷ xs) ys zs = begin
  (id {Var x} ⊗₁ α⇒-form-list xs ys zs) ∘ (id {Var x} ⊗₁ α⇐-form-list xs ys zs)
    ≈⟨ ≈-Term-sym ⊗-∘-dist ⟩
  (id ∘ id) ⊗₁ (α⇒-form-list xs ys zs ∘ α⇐-form-list xs ys zs)
    ≈⟨ ⊗-resp-≈ idˡ (α⇒-α⇐-iso xs ys zs) ⟩
  id ⊗₁ id
    ≈⟨ id⊗id≈id ⟩
  id ∎

-- Reverse direction: α⇐-form ∘ α⇒-form ≈ id.  Used by Phase 4 to
-- "invert" the α⇒-form factor introduced by pentagon-LHS application.
α⇐-α⇒-iso
  : ∀ (xs ys zs : List X)
  → α⇐-form-list xs ys zs ∘ α⇒-form-list xs ys zs ≈Term id
α⇐-α⇒-iso []       ys zs = idˡ
α⇐-α⇒-iso (x ∷ xs) ys zs = begin
  (id {Var x} ⊗₁ α⇐-form-list xs ys zs) ∘ (id {Var x} ⊗₁ α⇒-form-list xs ys zs)
    ≈⟨ ≈-Term-sym ⊗-∘-dist ⟩
  (id ∘ id) ⊗₁ (α⇐-form-list xs ys zs ∘ α⇒-form-list xs ys zs)
    ≈⟨ ⊗-resp-≈ idˡ (α⇐-α⇒-iso xs ys zs) ⟩
  id ⊗₁ id
    ≈⟨ id⊗id≈id ⟩
  id ∎

-- Mac Lane coherence corollary: α⇒_{unit, X, Y} ∘ (λ⇐_X ⊗ id_Y) ≈ λ⇐_{X⊗Y}.
-- Used for the base case (xs₁ = []) of `c-iso-assoc-from`.
-- Discharged by `solveM` via `CoherenceSolver.2-objs` (refactor C).
α⇒-λ⇐-collapse
  : ∀ {X Y} → α⇒ {unit} {X} {Y} ∘ (λ⇐ {X} ⊗₁ id {Y}) ≈Term λ⇐ {X ⊗₀ Y}
α⇒-λ⇐-collapse {X} {Y} = lemma
  where open import Categories.APROP.Hypergraph.Completeness.CoherenceSolver sig
        open 2-objs X Y renaming (α⇒-λ⇐-collapse to lemma)

-- Pentagon-rewrite: solves pentagon for `α⇒_{X⊗Y, Z, W}`.  Used by
-- the cons case of `c-iso-assoc-from` to expand the outer α⇒.
-- Discharged by `solveM` via `CoherenceSolver.4-objs` (refactor C).
pentagon-rewrite
  : ∀ {X Y Z W}
  → α⇒ {X ⊗₀ Y} {Z} {W}
  ≈Term α⇐ {X} {Y} {Z ⊗₀ W}
        ∘ id {X} ⊗₁ α⇒ {Y} {Z} {W}
        ∘ α⇒ {X} {Y ⊗₀ Z} {W}
        ∘ α⇒ {X} {Y} {Z} ⊗₁ id {W}
pentagon-rewrite {X} {Y} {Z} {W} = lemma
  where open import Categories.APROP.Hypergraph.Completeness.CoherenceSolver sig
        open 4-objs X Y Z W renaming (pentagon-rewrite to lemma)

-- id-⊗-subst-bridge: relates `id_{Var x} ⊗ (subst-id along e)` to a
-- subst-id at the wrapped predicate.  Used by the cons case to handle
-- the subst term.  Provable by J on `e` (refl case: id⊗id≈id).
id-⊗-subst-bridge
  : ∀ {x : X} {xs₁ ys'} (e : xs₁ ≡ ys')
  → (id {Var x} ⊗₁ subst (λ z → HomTerm (unflatten xs₁) (unflatten z)) e id)
  ≈Term subst (λ z → HomTerm (Var x ⊗₀ unflatten xs₁) (Var x ⊗₀ unflatten z)) e id
id-⊗-subst-bridge refl = id⊗id≈id

-- id-⊗-respects-∘: `id ⊗ (g ∘ f) ≈ (id ⊗ g) ∘ (id ⊗ f)`.  Specialization
-- of `⊗-∘-dist` for the case where the LHS factor is `id`.
id-⊗-respects-∘
  : ∀ {X A B C} (f : HomTerm A B) (g : HomTerm B C)
  → id {X} ⊗₁ (g ∘ f) ≈Term (id {X} ⊗₁ g) ∘ (id {X} ⊗₁ f)
id-⊗-respects-∘ f g = begin
  id ⊗₁ (g ∘ f)
    ≈⟨ ⊗-resp-≈ (≈-Term-sym idˡ) ≈-Term-refl ⟩
  (id ∘ id) ⊗₁ (g ∘ f)
    ≈⟨ ⊗-∘-dist ⟩
  id ⊗₁ g ∘ id ⊗₁ f ∎

-- α⇐-comm: α⇐'s naturality, derived from α-comm + α-iso laws.
-- Moved to top-level so it's accessible by both Phase 3 and the cons
-- case of `c-iso-assoc-from`.
α⇐-comm-top
  : ∀ {X Y Z X' Y' Z' : ObjTerm}
    (f : HomTerm X X') (g : HomTerm Y Y') (h : HomTerm Z Z')
  → α⇐ {X'} {Y'} {Z'} ∘ f ⊗₁ (g ⊗₁ h)
  ≈Term (f ⊗₁ g) ⊗₁ h ∘ α⇐ {X} {Y} {Z}
α⇐-comm-top f g h = begin
  α⇐ ∘ f ⊗₁ (g ⊗₁ h)
    ≈⟨ ≈-Term-sym idʳ ⟩
  (α⇐ ∘ f ⊗₁ (g ⊗₁ h)) ∘ id
    ≈⟨ refl⟩∘⟨ ≈-Term-sym α⇒∘α⇐≈id ⟩
  (α⇐ ∘ f ⊗₁ (g ⊗₁ h)) ∘ (α⇒ ∘ α⇐)
    ≈⟨ FM.assoc ⟩
  α⇐ ∘ f ⊗₁ (g ⊗₁ h) ∘ α⇒ ∘ α⇐
    ≈⟨ refl⟩∘⟨ FM.sym-assoc ⟩
  α⇐ ∘ (f ⊗₁ (g ⊗₁ h) ∘ α⇒) ∘ α⇐
    ≈⟨ refl⟩∘⟨ ≈-Term-sym α-comm ⟩∘⟨refl ⟩
  α⇐ ∘ (α⇒ ∘ (f ⊗₁ g) ⊗₁ h) ∘ α⇐
    ≈⟨ FM.sym-assoc ⟩
  (α⇐ ∘ α⇒ ∘ (f ⊗₁ g) ⊗₁ h) ∘ α⇐
    ≈⟨ FM.sym-assoc ⟩∘⟨refl ⟩
  ((α⇐ ∘ α⇒) ∘ (f ⊗₁ g) ⊗₁ h) ∘ α⇐
    ≈⟨ (α⇐∘α⇒≈id ⟩∘⟨refl) ⟩∘⟨refl ⟩
  (id ∘ (f ⊗₁ g) ⊗₁ h) ∘ α⇐
    ≈⟨ idˡ ⟩∘⟨refl ⟩
  (f ⊗₁ g) ⊗₁ h ∘ α⇐ ∎

-- c-iso pentagon: `c-iso-assoc-from` and its inductive helper
-- `c-iso-assoc-from-cons` are defined inside the private block below
-- (after `λ⇐-naturality`, which is needed for the base case).
-- The base case (xs₁ = []) is constructively proven; the inductive
-- case (xs₁ = x ∷ xs₁') is postulated.

-- `bridge` respects `≈Term`.
private
  bridge-resp-≈Term
    : ∀ {A B} {f g : HomTerm A B}
    → f ≈Term g → bridge f ≈Term bridge g
  bridge-resp-≈Term f≈g = refl⟩∘⟨ f≈g ⟩∘⟨refl

-- Smaller residual postulates for bridge-α⇒-form: the Var x and ⊗
-- cases.  The unit case is proved below by direct chase through
-- `unflatten-flatten-≈ unit = ≅.refl` + `unflatten-++-≅ [] ys = ≅.sym
-- unitorˡ` + Kelly's `coherence₁` (`λ⇒ ∘ α⇒ ≈ λ⇒ ⊗₁ id`) +
-- λ-naturality + `λ⇒∘λ⇐≈id` + `_≅_.isoʳ`.  The Var x case follows the
-- same template but with `unflatten-flatten-≈ (Var x) = ≅.sym
-- unitorʳ` + `unflatten-++-≅ [x] ys = ≅.trans … (≅.sym associator)`
-- and Kelly's `coherence₂` (`id ⊗₁ ρ⇒ ∘ α⇒ ≈ ρ⇒`) + ρ-naturality +
-- `ρ⇒∘ρ⇐≈id` + `_≅_.isoʳ`.  The ⊗ case combines IHs on A₁ and A₂ via
-- the pentagon identity.
--
-- The α⇐ side is derived from the α⇒ side using `α⇒-α⇐-iso` —
-- no separate postulates needed.

-- Helper lemma: `(ρ⇒ ⊗₁ Y) ∘ α⇐ {X}{unit}{Y'} ∘ id ⊗₁ λ⇐ ≈ id ⊗₁ Y`
-- for a morphism Y at appropriate type.  This combines triangle-inv
-- with ⊗-∘-dist + ρ⇒∘ρ⇐ + idʳ.
private
  collapse-ρ⇒-α⇐-λ⇐
    : ∀ {X Y Y' : ObjTerm} (f : HomTerm Y' Y)
    → (ρ⇒ {X} ⊗₁ f) ∘ α⇐ {X}{unit}{Y'} ∘ id ⊗₁ λ⇐ ≈Term id {X} ⊗₁ f
  collapse-ρ⇒-α⇐-λ⇐ f = begin
    (ρ⇒ ⊗₁ f) ∘ α⇐ ∘ id ⊗₁ λ⇐
      ≈⟨ refl⟩∘⟨ triangle-inv ⟩
    (ρ⇒ ⊗₁ f) ∘ ρ⇐ ⊗₁ id
      ≈⟨ ≈-Term-sym ⊗-∘-dist ⟩
    (ρ⇒ ∘ ρ⇐) ⊗₁ (f ∘ id)
      ≈⟨ ⊗-resp-≈ ρ⇒∘ρ⇐≈id idʳ ⟩
    id ⊗₁ f ∎

-- Var x case for bridge-α⇒-form: similar template to unit case but
-- using triangle + triangle-inv to collapse the ρ-related morphisms.
bridge-α⇒-form-Var
  : ∀ x B C → bridge (α⇒ {Var x} {B} {C})
            ≈Term α⇒-form-list (x ∷ []) (flatten B) (flatten C)
bridge-α⇒-form-Var x B C = begin
  bridge (α⇒ {Var x} {B} {C})
    -- bridge unfolds to:
    -- (((id ⊗ λ⇒) ∘ α⇒-unit) ∘ (ρ⇐ ⊗ F-BC)) ∘ (α⇒-VBC ∘ T-((Vx⊗B)⊗C))
    -- A single FM.assoc isn't enough because the LHS is itself a
    -- left-associated 3-element composition.  Two FM.assoc's bring
    -- everything to right-assoc.
    ≈⟨ FM.assoc ⟩
  ((id ⊗₁ λ⇒) ∘ α⇒-unit) ∘ ((ρ⇐ ⊗₁ F-BC) ∘ α⇒-VBC ∘
    (((ρ⇒ ⊗₁ T-B) ∘ α⇐ {Var x}{unit}{unflatten (flatten B)} ∘ id ⊗₁ λ⇐)
       ⊗₁ T-C ∘ α⇐-c2 ∘ id ⊗₁ cBC-from))
    ≈⟨ FM.assoc ⟩
  (id ⊗₁ λ⇒) ∘ α⇒-unit ∘ (ρ⇐ ⊗₁ F-BC) ∘ α⇒-VBC ∘
    (((ρ⇒ ⊗₁ T-B) ∘ α⇐ {Var x}{unit}{unflatten (flatten B)} ∘ id ⊗₁ λ⇐)
       ⊗₁ T-C ∘ α⇐-c2 ∘ id ⊗₁ cBC-from)
    ≈⟨ FM.sym-assoc ⟩
  ((id ⊗₁ λ⇒) ∘ α⇒-unit) ∘ (ρ⇐ ⊗₁ F-BC) ∘ α⇒-VBC ∘
    (((ρ⇒ ⊗₁ T-B) ∘ α⇐ {Var x}{unit}{unflatten (flatten B)} ∘ id ⊗₁ λ⇐)
       ⊗₁ T-C ∘ α⇐-c2 ∘ id ⊗₁ cBC-from)
    ≈⟨ triangle ⟩∘⟨refl ⟩
  (ρ⇒ ⊗₁ id) ∘ (ρ⇐ ⊗₁ F-BC) ∘ α⇒-VBC ∘
    (((ρ⇒ ⊗₁ T-B) ∘ α⇐ {Var x}{unit}{unflatten (flatten B)} ∘ id ⊗₁ λ⇐)
       ⊗₁ T-C ∘ α⇐-c2 ∘ id ⊗₁ cBC-from)
    ≈⟨ FM.sym-assoc ⟩
  ((ρ⇒ ⊗₁ id) ∘ (ρ⇐ ⊗₁ F-BC)) ∘ α⇒-VBC ∘
    (((ρ⇒ ⊗₁ T-B) ∘ α⇐ {Var x}{unit}{unflatten (flatten B)} ∘ id ⊗₁ λ⇐)
       ⊗₁ T-C ∘ α⇐-c2 ∘ id ⊗₁ cBC-from)
    ≈⟨ ≈-Term-sym ⊗-∘-dist ⟩∘⟨refl ⟩
  ((ρ⇒ ∘ ρ⇐) ⊗₁ (id ∘ F-BC)) ∘ α⇒-VBC ∘
    (((ρ⇒ ⊗₁ T-B) ∘ α⇐ {Var x}{unit}{unflatten (flatten B)} ∘ id ⊗₁ λ⇐)
       ⊗₁ T-C ∘ α⇐-c2 ∘ id ⊗₁ cBC-from)
    ≈⟨ ⊗-resp-≈ ρ⇒∘ρ⇐≈id idˡ ⟩∘⟨refl ⟩
  (id ⊗₁ F-BC) ∘ α⇒-VBC ∘
    (((ρ⇒ ⊗₁ T-B) ∘ α⇐ {Var x}{unit}{unflatten (flatten B)} ∘ id ⊗₁ λ⇐)
       ⊗₁ T-C ∘ α⇐-c2 ∘ id ⊗₁ cBC-from)
    -- Now collapse the inner T-B side using collapse-ρ⇒-α⇐-λ⇐.
    ≈⟨ refl⟩∘⟨ refl⟩∘⟨ ⊗-resp-≈ (collapse-ρ⇒-α⇐-λ⇐ T-B) ≈-Term-refl ⟩∘⟨refl ⟩
  (id ⊗₁ F-BC) ∘ α⇒-VBC ∘
    ((id ⊗₁ T-B) ⊗₁ T-C ∘ α⇐-c2 ∘ id ⊗₁ cBC-from)
    -- Apply α-naturality: α⇒-VBC ∘ (id ⊗ T-B) ⊗ T-C ≈ id ⊗ (T-B ⊗ T-C) ∘ α⇒-d.
    ≈⟨ refl⟩∘⟨ FM.sym-assoc ⟩
  (id ⊗₁ F-BC) ∘ (α⇒-VBC ∘ (id ⊗₁ T-B) ⊗₁ T-C) ∘ α⇐-c2 ∘ id ⊗₁ cBC-from
    ≈⟨ refl⟩∘⟨ α-comm ⟩∘⟨refl ⟩
  (id ⊗₁ F-BC) ∘ (id ⊗₁ (T-B ⊗₁ T-C) ∘ α⇒-d) ∘ α⇐-c2 ∘ id ⊗₁ cBC-from
    ≈⟨ refl⟩∘⟨ FM.assoc ⟩
  (id ⊗₁ F-BC) ∘ id ⊗₁ (T-B ⊗₁ T-C) ∘ α⇒-d ∘ α⇐-c2 ∘ id ⊗₁ cBC-from
    -- Combine first two via ⊗-∘-dist (sym).
    ≈⟨ FM.sym-assoc ⟩
  ((id ⊗₁ F-BC) ∘ id ⊗₁ (T-B ⊗₁ T-C)) ∘ α⇒-d ∘ α⇐-c2 ∘ id ⊗₁ cBC-from
    ≈⟨ ≈-Term-sym ⊗-∘-dist ⟩∘⟨refl ⟩
  ((id ∘ id) ⊗₁ (F-BC ∘ T-B ⊗₁ T-C)) ∘ α⇒-d ∘ α⇐-c2 ∘ id ⊗₁ cBC-from
    ≈⟨ ⊗-resp-≈ idˡ collapse-F-BC ⟩∘⟨refl ⟩
  (id ⊗₁ cBC-to) ∘ α⇒-d ∘ α⇐-c2 ∘ id ⊗₁ cBC-from
    -- α⇒-d ∘ α⇐-c2 ≈ id (α⇒∘α⇐≈id).
    ≈⟨ refl⟩∘⟨ FM.sym-assoc ⟩
  (id ⊗₁ cBC-to) ∘ (α⇒-d ∘ α⇐-c2) ∘ id ⊗₁ cBC-from
    ≈⟨ refl⟩∘⟨ α⇒∘α⇐≈id ⟩∘⟨refl ⟩
  (id ⊗₁ cBC-to) ∘ id ∘ id ⊗₁ cBC-from
    ≈⟨ refl⟩∘⟨ idˡ ⟩
  (id ⊗₁ cBC-to) ∘ id ⊗₁ cBC-from
    ≈⟨ ≈-Term-sym ⊗-∘-dist ⟩
  (id ∘ id) ⊗₁ (cBC-to ∘ cBC-from)
    ≈⟨ ⊗-resp-≈ idˡ (_≅_.isoˡ (unflatten-++-≅ (flatten B) (flatten C))) ⟩
  id ⊗₁ id ∎
  where
    F-BC      = _≅_.from (unflatten-flatten-≈ (B ⊗₀ C))
    T-B       = _≅_.to   (unflatten-flatten-≈ B)
    T-C       = _≅_.to   (unflatten-flatten-≈ C)
    cBC-from  = _≅_.from (unflatten-++-≅ (flatten B) (flatten C))
    cBC-to    = _≅_.to   (unflatten-++-≅ (flatten B) (flatten C))
    α⇒-unit   = α⇒ {Var x} {unit} {unflatten (flatten B ++ flatten C)}
    α⇒-VBC    = α⇒ {Var x} {B} {C}
    α⇐-c2     = α⇐ {Var x} {unflatten (flatten B)} {unflatten (flatten C)}
    α⇒-d      = α⇒ {Var x} {unflatten (flatten B)} {unflatten (flatten C)}

    collapse-F-BC : F-BC ∘ T-B ⊗₁ T-C ≈Term cBC-to
    collapse-F-BC = begin
      F-BC ∘ T-B ⊗₁ T-C
        ≈⟨ FM.assoc ⟩
      cBC-to ∘ (F-B ⊗₁ F-C) ∘ T-B ⊗₁ T-C
        ≈⟨ refl⟩∘⟨ ≈-Term-sym ⊗-∘-dist ⟩
      cBC-to ∘ (F-B ∘ T-B) ⊗₁ (F-C ∘ T-C)
        ≈⟨ refl⟩∘⟨ ⊗-resp-≈ (_≅_.isoʳ (unflatten-flatten-≈ B))
                              (_≅_.isoʳ (unflatten-flatten-≈ C)) ⟩
      cBC-to ∘ id ⊗₁ id
        ≈⟨ refl⟩∘⟨ id⊗id≈id ⟩
      cBC-to ∘ id
        ≈⟨ idʳ ⟩
      cBC-to ∎
      where
        F-B = _≅_.from (unflatten-flatten-≈ B)
        F-C = _≅_.from (unflatten-flatten-≈ C)

-- ⊗ case for bridge-α⇒-form, structured as induction on A₁.
-- Three sub-cases (A₁ = unit, Var x, A₁₁ ⊗ A₁₂); each starts as a
-- sub-postulate to be filled in by Phases 2, 3, 4 of the proof plan.
--
-- Phase 2 sub-case (A₁ = unit): `bridge (α⇒ {unit ⊗ A₂}{B}{C})
-- ≈ α⇒-form-list (flatten A₂) (flatten B) (flatten C)`.  The
-- chain uses `λ⇐∘λ⇒` (since `unflatten-flatten-≈ (unit ⊗ X) =
-- ≅.trans (≅.refl ⊗ᵢ u-X) (≅.sym (≅.sym unitorˡ))` introduces λ on
-- both F and T sides) to reduce to bridge-α⇒-form on A₂ (via IH).
--
-- Phase 3 sub-case (A₁ = Var x): `bridge (α⇒ {Var x ⊗ A₂}{B}{C})
-- ≈ α⇒-form-list (x ∷ flatten A₂) (flatten B) (flatten C) =
-- id ⊗ α⇒-form-list (flatten A₂) (flatten B) (flatten C)`.  The
-- chain uses `triangle` + `triangle-inv` (analogous to the Var x
-- proof of `bridge-α⇒-form-Var`) plus IH on A₂ to reach `id ⊗
-- bridge-α⇒-form A₂`.
--
-- Phase 4 sub-case (A₁ = A₁₁ ⊗ A₁₂): the inductive case.  Uses the
-- pentagon identity to express `α⇒ {(A₁₁ ⊗ A₁₂) ⊗ A₂}{B}{C}` via
-- four α⇒'s at simpler types, then applies IHs on A₁₁, A₁₂, A₂.
-- Helper for the unit-prefix collapse:
-- `F-(unit ⊗ X) ∘ λ⇐ ≈ F-X` and `λ⇒ ∘ T-(unit ⊗ X) ≈ T-X`.
-- These follow from `unflatten-flatten-≈ (unit ⊗ X) = ≅.trans
-- (≅.refl ⊗ᵢ u-X) (≅.sym (≅.sym unitorˡ))`, which puts λ⇒ outermost
-- on F and λ⇐ outermost on T.
private
  -- λ⇐-naturality (derived from λ⇒-naturality + iso laws).
  λ⇐-naturality
    : ∀ {A B} (f : HomTerm A B) → λ⇐ {B} ∘ f ≈Term id ⊗₁ f ∘ λ⇐ {A}
  λ⇐-naturality f = begin
    λ⇐ ∘ f
      ≈⟨ ≈-Term-sym idʳ ⟩
    (λ⇐ ∘ f) ∘ id
      ≈⟨ refl⟩∘⟨ ≈-Term-sym λ⇒∘λ⇐≈id ⟩
    (λ⇐ ∘ f) ∘ λ⇒ ∘ λ⇐
      ≈⟨ FM.sym-assoc ⟩
    ((λ⇐ ∘ f) ∘ λ⇒) ∘ λ⇐
      ≈⟨ FM.assoc ⟩∘⟨refl ⟩
    (λ⇐ ∘ f ∘ λ⇒) ∘ λ⇐
      ≈⟨ (refl⟩∘⟨ ≈-Term-sym λ⇒∘id⊗f≈f∘λ⇒) ⟩∘⟨refl ⟩
    (λ⇐ ∘ λ⇒ ∘ id ⊗₁ f) ∘ λ⇐
      ≈⟨ FM.sym-assoc ⟩∘⟨refl ⟩
    ((λ⇐ ∘ λ⇒) ∘ id ⊗₁ f) ∘ λ⇐
      ≈⟨ (λ⇐∘λ⇒≈id ⟩∘⟨refl) ⟩∘⟨refl ⟩
    (id ∘ id ⊗₁ f) ∘ λ⇐
      ≈⟨ idˡ ⟩∘⟨refl ⟩
    id ⊗₁ f ∘ λ⇐ ∎

  -- c-iso pentagon (associativity of unflatten-++-≅).  Proved by list
  -- induction on xs₁: base case constructive, cons case postulated.
  --
  -- Used by Phase 4 to merge c-iso wrappers introduced by `bridge-⊗`
  -- at compound types like A₁₁⊗A₁₂.
  --
  -- Sub-lemmas already proved (top-level, just before this private
  -- block): `pentagon-rewrite` (solves pentagon for α⇒_{X⊗Y, Z, W}),
  -- `id-⊗-subst-bridge` (id ⊗ subst-id ≈ subst-id at compound
  -- predicate), `id-⊗-respects-∘` (id ⊗ (g ∘ f) = (id ⊗ g) ∘ (id ⊗ f)).
  --
  -- Cons case proof outline (postulated; ~30 chain steps):
  --   1. `pentagon-rewrite` to expand α⇒_{Var x ⊗ unflatten xs₁', xs₂, ys}.
  --   2. ⊗-∘-dist + `α⇒∘α⇐≈id` + idˡ to cancel `(α⇒_D ⊗ id) ∘
  --      ((α⇐_1 ∘ (id ⊗ c-1)) ⊗ id) ≈ (id ⊗ c-1) ⊗ id`.
  --   3. `α-comm` to push `α⇒_C` past `((id ⊗ c-1) ⊗ id)`.
  --   4. `α⇒∘α⇐≈id` + `idˡ` to cancel α⇒_E ∘ α⇐_2.
  --   5. `id-⊗-respects-∘` (×2) + `idˡ` to combine `(id ⊗ α⇒_B) ∘
  --      (id ⊗ (c-1 ⊗ id)) ∘ (id ⊗ c-2) ≈ id ⊗ (α⇒_B ∘ (c-1 ⊗ id) ∘ c-2)`.
  --   6. `⊗-resp-≈ ≈-Term-refl (c-iso-assoc-from xs₁' xs₂ ys)` (IH).
  --   7. `id-⊗-respects-∘` (×2) to break `id ⊗ (...)` apart.
  --   8. `α⇐-comm` (currently in Phase 3 private block; would need to
  --      be moved to top-level or inlined).
  --   9. `id⊗id≈id` to simplify `(id ⊗ id) ⊗ c-rest`.
  --  10. Definitional reduction: `α⇐_3 ∘ (id ⊗ c-3) = c-(x ∷ xs₁'),(xs₂++ys)-from`.
  --  11. `id-⊗-subst-bridge` + `≡⇒≈Term (sym (subst-∘ ...))` to
  --      convert `id ⊗ subst-id-xs₁'` to `subst-id-(x ∷ xs₁')`.
  -- Inductive case helper: `c-iso-assoc-from-cons` is what
  -- `c-iso-assoc-from (x ∷ xs₁') xs₂ ys` reduces to.  Constructively
  -- discharged in
  -- `Categories.APROP.Hypergraph.Completeness.Discharge.CIsoAssocFromCons`
  -- via an 11-step pentagon chain.
  open import Categories.APROP.Hypergraph.Completeness.Discharge.CIsoAssocFromCons sig
    using (c-iso-assoc-from-cons)

  c-iso-assoc-from
    : ∀ xs₁ xs₂ ys
    → α⇒ {unflatten xs₁} {unflatten xs₂} {unflatten ys}
      ∘ (_≅_.from (unflatten-++-≅ xs₁ xs₂) ⊗₁ id)
      ∘ _≅_.from (unflatten-++-≅ (xs₁ ++ xs₂) ys)
    ≈Term (id {unflatten xs₁} ⊗₁ _≅_.from (unflatten-++-≅ xs₂ ys))
          ∘ _≅_.from (unflatten-++-≅ xs₁ (xs₂ ++ ys))
          ∘ subst (λ z → HomTerm (unflatten ((xs₁ ++ xs₂) ++ ys)) (unflatten z))
                  (++-assoc xs₁ xs₂ ys) id
  -- Base case: xs₁ = [].  After Agda's reduction:
  --   _≅_.from (unflatten-++-≅ [] ys') reduces to λ⇐_{unflatten ys'}.
  --   ([] ++ xs₂) ++ ys reduces to xs₂ ++ ys.
  --   ++-assoc [] xs₂ ys = refl, so subst _ refl id = id.
  -- The chain uses α⇒-λ⇐-collapse + λ⇐-naturality + idʳ.
  c-iso-assoc-from [] xs₂ ys = begin
    α⇒ ∘ (λ⇐ ⊗₁ id) ∘ _≅_.from (unflatten-++-≅ xs₂ ys)
      ≈⟨ FM.sym-assoc ⟩
    (α⇒ ∘ (λ⇐ ⊗₁ id)) ∘ _≅_.from (unflatten-++-≅ xs₂ ys)
      ≈⟨ α⇒-λ⇐-collapse ⟩∘⟨refl ⟩
    λ⇐ ∘ _≅_.from (unflatten-++-≅ xs₂ ys)
      ≈⟨ λ⇐-naturality (_≅_.from (unflatten-++-≅ xs₂ ys)) ⟩
    id ⊗₁ _≅_.from (unflatten-++-≅ xs₂ ys) ∘ λ⇐
      ≈⟨ refl⟩∘⟨ ≈-Term-sym idʳ ⟩
    (id ⊗₁ _≅_.from (unflatten-++-≅ xs₂ ys)) ∘ λ⇐ ∘ id ∎
  -- Cons case: xs₁ = x ∷ xs₁'.  Constructive proof using:
  --   * `pentagon-rewrite` to expand α⇒_{Var x ⊗ unflatten xs₁', xs₂, ys}.
  --   * ⊗-∘-dist + α⇒∘α⇐≈id to cancel inner pair.
  --   * α-comm + α⇒∘α⇐≈id to cancel another pair.
  --   * `id-⊗-respects-∘` to combine (id ⊗ ...) factors.
  --   * IH `c-iso-assoc-from xs₁' xs₂ ys`.
  --   * `α⇐-comm-top` to push α⇐_A past (id ⊗ (id ⊗ c-rest)).
  --   * `id⊗id≈id` to simplify (id ⊗ id) ⊗ c-rest.
  --   * `id-⊗-subst-bridge` + `≡⇒≈Term (sym (subst-∘ ...))` for the
  --     subst manipulation.
  c-iso-assoc-from (x ∷ xs₁') xs₂ ys = c-iso-assoc-from-cons x xs₁' xs₂ ys

  -- F-(unit ⊗ X) ∘ λ⇐ ≈ F-X.
  F-unit⊗-collapse
    : ∀ X → _≅_.from (unflatten-flatten-≈ (unit ⊗₀ X)) ∘ λ⇐
          ≈Term _≅_.from (unflatten-flatten-≈ X)
  F-unit⊗-collapse X = begin
    -- definitionally: ≅.from u-(unit ⊗ X) = λ⇒ ∘ id ⊗₁ F-X
    (λ⇒ ∘ id ⊗₁ F-X) ∘ λ⇐
      ≈⟨ FM.assoc ⟩
    λ⇒ ∘ id ⊗₁ F-X ∘ λ⇐
      ≈⟨ refl⟩∘⟨ ≈-Term-sym (λ⇐-naturality F-X) ⟩
    λ⇒ ∘ λ⇐ ∘ F-X
      ≈⟨ FM.sym-assoc ⟩
    (λ⇒ ∘ λ⇐) ∘ F-X
      ≈⟨ λ⇒∘λ⇐≈id ⟩∘⟨refl ⟩
    id ∘ F-X
      ≈⟨ idˡ ⟩
    F-X ∎
    where
      F-X = _≅_.from (unflatten-flatten-≈ X)

  -- λ⇒ ∘ T-(unit ⊗ X) ≈ T-X.
  T-unit⊗-collapse
    : ∀ X → λ⇒ ∘ _≅_.to (unflatten-flatten-≈ (unit ⊗₀ X))
          ≈Term _≅_.to (unflatten-flatten-≈ X)
  T-unit⊗-collapse X = begin
    -- definitionally: ≅.to u-(unit ⊗ X) = id ⊗₁ T-X ∘ λ⇐
    λ⇒ ∘ id ⊗₁ T-X ∘ λ⇐
      ≈⟨ FM.sym-assoc ⟩
    (λ⇒ ∘ id ⊗₁ T-X) ∘ λ⇐
      ≈⟨ λ⇒∘id⊗f≈f∘λ⇒ ⟩∘⟨refl ⟩
    (T-X ∘ λ⇒) ∘ λ⇐
      ≈⟨ FM.assoc ⟩
    T-X ∘ λ⇒ ∘ λ⇐
      ≈⟨ refl⟩∘⟨ λ⇒∘λ⇐≈id ⟩
    T-X ∘ id
      ≈⟨ idʳ ⟩
    T-X ∎
    where
      T-X = _≅_.to (unflatten-flatten-≈ X)

  -- F-(Var x ⊗ X) ≈ id {Var x} ⊗ F-X.
  F-Vx⊗-collapse
    : ∀ x X → _≅_.from (unflatten-flatten-≈ (Var x ⊗₀ X))
            ≈Term id {Var x} ⊗₁ _≅_.from (unflatten-flatten-≈ X)
  F-Vx⊗-collapse x X = begin
    -- definitionally: ≅.from u-(Var x ⊗ X) = ((id ⊗ λ⇒) ∘ α⇒) ∘ (ρ⇐ ⊗ F-X)
    ((id ⊗₁ λ⇒) ∘ α⇒) ∘ (ρ⇐ ⊗₁ F-X)
      ≈⟨ triangle ⟩∘⟨refl ⟩
    (ρ⇒ ⊗₁ id) ∘ (ρ⇐ ⊗₁ F-X)
      ≈⟨ ≈-Term-sym ⊗-∘-dist ⟩
    (ρ⇒ ∘ ρ⇐) ⊗₁ (id ∘ F-X)
      ≈⟨ ⊗-resp-≈ ρ⇒∘ρ⇐≈id idˡ ⟩
    id ⊗₁ F-X ∎
    where
      F-X = _≅_.from (unflatten-flatten-≈ X)

  -- T-(Var x ⊗ X) ≈ id {Var x} ⊗ T-X.  Direct application of
  -- `collapse-ρ⇒-α⇐-λ⇐` (which collapses the same shape).
  T-Vx⊗-collapse
    : ∀ x X → _≅_.to (unflatten-flatten-≈ (Var x ⊗₀ X))
            ≈Term id {Var x} ⊗₁ _≅_.to (unflatten-flatten-≈ X)
  T-Vx⊗-collapse x X = collapse-ρ⇒-α⇐-λ⇐ (_≅_.to (unflatten-flatten-≈ X))

  -- Forward declarations: defined after `bridge-α⇒-form` so the bodies
  -- can call it as IH on the structurally-smaller A₂.
  bridge-α⇒-form-⊗-unit
    : ∀ A₂ B C → bridge (α⇒ {unit ⊗₀ A₂} {B} {C})
              ≈Term α⇒-form-list (flatten A₂)
                                  (flatten B) (flatten C)

  bridge-α⇒-form-⊗-Var
    : ∀ x A₂ B C → bridge (α⇒ {Var x ⊗₀ A₂} {B} {C})
                ≈Term α⇒-form-list (x ∷ flatten A₂)
                                    (flatten B) (flatten C)

  -- ============================================================
  -- Phase 4 inductive case: A₁ = A₁₁ ⊗ A₁₂ (compound on first arg)
  -- ============================================================
  --
  -- POSTULATED.  Documentation of state and remaining work below.
  --
  -- ─── Infrastructure in place (all proven, in this file) ─────
  --
  -- * `bridge-⊗` (line ~140): general bridge of tensor product.
  --   The `id ⊗ f` and `f ⊗ id` cases are 1-step corollaries via
  --   `bridge-id-is-id`.
  --
  -- * `bridge-α⇐-form` (forward-declared above): bridge of α⇐
  --   reduces to α⇐-form-list.  Compound-first-arg case is
  --   supported (terminating since A₁₁⊗A₁₂ < (A₁₁⊗A₁₂)⊗A₂
  --   structurally).
  --
  -- * `α⇒-α⇐-iso` and `α⇐-α⇒-iso` (line ~822/838): both
  --   directions of the form-list iso.  Used to invert
  --   α⇒-form-list / α⇐-form-list factors after applying
  --   pentagon-LHS.
  --
  -- * `pentagon-rewrite` (line ~867): solves pentagon for
  --   `α⇒_{X⊗Y, Z, W}`, expressing it as
  --   `α⇐ ∘ (id ⊗ α⇒) ∘ α⇒ ∘ (α⇒ ⊗ id)`.
  --
  -- * `α⇒-λ⇐-collapse` (line ~852): Mac Lane corollary
  --   `α⇒_{unit,X,Y} ∘ (λ⇐ ⊗ id) ≈ λ⇐_{X⊗Y}`.
  --
  -- * `id-⊗-respects-∘` (line ~885): `id ⊗ (g ∘ f) ≈ (id ⊗ g) ∘
  --   (id ⊗ f)`.
  --
  -- * `id-⊗-subst-bridge` (line ~879): `id ⊗ subst-id ≈ subst-id`
  --   at wrapped predicate (for subst-cong handling).  Provable
  --   by J on refl.
  --
  -- * `α⇐-comm-top` (line ~896): α⇐'s naturality at top-level so
  --   accessible from both Phase 3 and Phase 4 proofs.
  --
  -- * `c-iso-assoc-from` (defined in this private block, with
  --   base case proved): the c-iso pentagon — associativity of
  --   `unflatten-++-≅` up to ++-assoc.  Cons case still postulated.
  --
  -- * IHs `bridge-α⇒-form (A₁₁⊗A₁₂) X Y` for various X, Y:
  --   accessible (terminating).
  --
  -- ─── Strategy outline (Option (a): c-iso pentagon-based) ────
  --
  -- 1. Apply pentagon (sym) at types (A₁₁⊗A₁₂, A₂, B, C) to
  --    rewrite α⇒_{(A₁₁⊗A₁₂)⊗A₂, B, C} as
  --      α⇐_{A₁₁⊗A₁₂, A₂, B⊗C} ∘ (id ⊗ α⇒_{A₂,B,C})
  --        ∘ α⇒_{A₁₁⊗A₁₂, A₂⊗B, C} ∘ (α⇒_{A₁₁⊗A₁₂, A₂, B} ⊗ id_C)
  --
  -- 2. Apply `bridge` and `bridge-∘` to get a 4-fold composition
  --    of bridges.
  --
  -- 3. Substitute IHs:
  --    - bridge α⇐_{A₁₁⊗A₁₂, A₂, B⊗C}: bridge-α⇐-form (compound
  --      A) ≈ α⇐-form-list (flatten A₁₁ ++ flatten A₁₂)
  --      (flatten A₂) (flatten B ++ flatten C).
  --    - bridge α⇒_{A₁₁⊗A₁₂, A₂⊗B, C}: IH bridge-α⇒-form-⊗ A₁₁
  --      A₁₂ (A₂⊗B) C.
  --    - bridge α⇒_{A₁₁⊗A₁₂, A₂, B}: IH bridge-α⇒-form-⊗ A₁₁
  --      A₁₂ A₂ B.
  --    - bridge α⇒_{A₂, B, C}: IH bridge-α⇒-form A₂ B C.
  --    - bridge (id ⊗ α⇒) and bridge (α⇒ ⊗ id): use bridge-⊗ +
  --      bridge-id-is-id.
  --
  -- 4. After substitution, c-iso wrappers from `bridge-⊗` appear
  --    at adjacent positions.  Apply `c-iso-assoc-from` (cons case
  --    postulated) to merge them.
  --
  -- 5. Cancel α⇒-form-list ∘ α⇐-form-list pairs via α⇒-α⇐-iso.
  --
  -- 6. Final result: α⇒-form-list ((flatten A₁₁ ++ flatten A₁₂) ++
  --    flatten A₂) (flatten B) (flatten C).
  --
  -- Estimated chain length: 100-150 chain steps.
  --
  -- ─── Why postulated (not proven in this session) ────────────
  --
  -- The chain has many parenthesization invariants and intricate
  -- subst-cong manipulations.  As we observed in Phases 2 and 3
  -- (which each took ~5-10 paren-debugging iterations even for
  -- shorter chains), the Phase 4 main proof realistically needs
  -- a focused multi-hour session of Agda-error iteration.  All
  -- the infrastructure required to make the proof go through is
  -- in place; what remains is the bookkeeping of the chain.
  --
  -- ─── Why no shortcut via Mac Lane coherence ─────────────────
  --
  -- The cleanest formulation would use a "single subst" approach:
  --   bridge α⇒ ≈ subst-id-cast ≈ α⇒-form-list
  -- where the second equation is α⇒-coh-list (already proven by
  -- list induction).  But the FIRST equation (`bridge α⇒ ≈
  -- subst-id-cast` for compound A) is exactly Mac Lane's
  -- coherence theorem at this instance: parallel iso's between
  -- propositionally-equal types in the free monoidal category are
  -- equal.  `Categories.MonoidalCoherence` provides this lemma but
  -- uses K (specifically, the `ι` functor pattern-matches on
  -- `refl` as a morphism in `Discrete`).  Porting it to
  -- --without-K is non-trivial.  Without it, every parallel-iso
  -- equality must be proven case-by-case via chain manipulation.
  --
  -- The c-iso pentagon (`c-iso-assoc-from`) base case proof
  -- already demonstrates one such case: it proves the analogous
  -- claim for the empty list (xs₁ = []), reducing to a known
  -- coherence corollary.  The cons case is the analogous claim
  -- for non-empty lists; it's structurally similar but requires
  -- ~30 chain steps.  Phase 4 main is ~100-150 chain steps.
  postulate
    bridge-α⇒-form-⊗-⊗
      : ∀ A₁₁ A₁₂ A₂ B C
      → bridge (α⇒ {(A₁₁ ⊗₀ A₁₂) ⊗₀ A₂} {B} {C})
      ≈Term α⇒-form-list ((flatten A₁₁ ++ flatten A₁₂) ++ flatten A₂)
                          (flatten B) (flatten C)

bridge-α⇒-form-⊗
  : ∀ A₁ A₂ B C → bridge (α⇒ {A₁ ⊗₀ A₂} {B} {C})
                ≈Term α⇒-form-list (flatten A₁ ++ flatten A₂)
                                    (flatten B) (flatten C)
bridge-α⇒-form-⊗ unit         A₂ B C = bridge-α⇒-form-⊗-unit A₂ B C
bridge-α⇒-form-⊗ (Var x)      A₂ B C = bridge-α⇒-form-⊗-Var x A₂ B C
bridge-α⇒-form-⊗ (A₁₁ ⊗₀ A₁₂) A₂ B C = bridge-α⇒-form-⊗-⊗ A₁₁ A₁₂ A₂ B C

-- Forward-declared so that `bridge-α⇒-form-⊗-⊗` can use it for the
-- α⇐ factor introduced by pentagon decomposition.  Body defined later.
bridge-α⇐-form
  : ∀ A B C → bridge (α⇐ {A} {B} {C})
            ≈Term α⇐-form-list (flatten A) (flatten B) (flatten C)

-- Bridge form for α⇒, by induction on `A`.  The unit base case is
-- discharged constructively below; Var x and ⊗ cases use the residual
-- postulates above.
bridge-α⇒-form
  : ∀ A B C → bridge (α⇒ {A} {B} {C})
            ≈Term α⇒-form-list (flatten A) (flatten B) (flatten C)
bridge-α⇒-form unit B C = begin
  bridge (α⇒ {unit} {B} {C})
    -- bridge unfolds to (λ⇒ ∘ id ⊗ F-BC) ∘ (α⇒ ∘ ((id ⊗ T-B ∘ λ⇐) ⊗ T-C ∘ cBC-from))
    ≈⟨ FM.assoc ⟩
  λ⇒ ∘ id ⊗₁ F-BC ∘ α⇒ ∘ (id ⊗₁ T-B ∘ λ⇐) ⊗₁ T-C ∘ cBC-from
    ≈⟨ FM.sym-assoc ⟩
  (λ⇒ ∘ id ⊗₁ F-BC) ∘ α⇒ ∘ (id ⊗₁ T-B ∘ λ⇐) ⊗₁ T-C ∘ cBC-from
    ≈⟨ λ⇒∘id⊗f≈f∘λ⇒ ⟩∘⟨refl ⟩
  (F-BC ∘ λ⇒) ∘ α⇒ ∘ (id ⊗₁ T-B ∘ λ⇐) ⊗₁ T-C ∘ cBC-from
    ≈⟨ FM.assoc ⟩
  F-BC ∘ λ⇒ ∘ α⇒ ∘ (id ⊗₁ T-B ∘ λ⇐) ⊗₁ T-C ∘ cBC-from
    ≈⟨ refl⟩∘⟨ FM.sym-assoc ⟩
  F-BC ∘ (λ⇒ ∘ α⇒) ∘ (id ⊗₁ T-B ∘ λ⇐) ⊗₁ T-C ∘ cBC-from
    ≈⟨ refl⟩∘⟨ coherence₁ ⟩∘⟨refl ⟩
  F-BC ∘ λ⇒ ⊗₁ id ∘ (id ⊗₁ T-B ∘ λ⇐) ⊗₁ T-C ∘ cBC-from
    ≈⟨ refl⟩∘⟨ FM.sym-assoc ⟩
  F-BC ∘ (λ⇒ ⊗₁ id ∘ (id ⊗₁ T-B ∘ λ⇐) ⊗₁ T-C) ∘ cBC-from
    ≈⟨ refl⟩∘⟨ ≈-Term-sym ⊗-∘-dist ⟩∘⟨refl ⟩
  F-BC ∘ (λ⇒ ∘ id ⊗₁ T-B ∘ λ⇐) ⊗₁ (id ∘ T-C) ∘ cBC-from
    ≈⟨ refl⟩∘⟨ ⊗-resp-≈ collapse-LHS idˡ ⟩∘⟨refl ⟩
  F-BC ∘ T-B ⊗₁ T-C ∘ cBC-from
    -- F-BC ∘ T-B ⊗₁ T-C ∘ cBC-from ≡ F-BC ∘ T-(B⊗C) definitionally,
    -- since T-(B⊗C) = (T-B ⊗₁ T-C) ∘ cBC-from.  Apply isoʳ.
    ≈⟨ _≅_.isoʳ (unflatten-flatten-≈ (B ⊗₀ C)) ⟩
  id ∎
  where
    F-BC = _≅_.from (unflatten-flatten-≈ (B ⊗₀ C))
    T-B  = _≅_.to   (unflatten-flatten-≈ B)
    T-C  = _≅_.to   (unflatten-flatten-≈ C)
    cBC-from = _≅_.from (unflatten-++-≅ (flatten B) (flatten C))

    -- λ⇒ ∘ id ⊗ T-B ∘ λ⇐ ≈ T-B (using λ-naturality + λ⇒∘λ⇐≈id).
    collapse-LHS : λ⇒ ∘ id ⊗₁ T-B ∘ λ⇐ ≈Term T-B
    collapse-LHS = begin
      λ⇒ ∘ id ⊗₁ T-B ∘ λ⇐
        ≈⟨ FM.sym-assoc ⟩
      (λ⇒ ∘ id ⊗₁ T-B) ∘ λ⇐
        ≈⟨ λ⇒∘id⊗f≈f∘λ⇒ ⟩∘⟨refl ⟩
      (T-B ∘ λ⇒) ∘ λ⇐
        ≈⟨ FM.assoc ⟩
      T-B ∘ λ⇒ ∘ λ⇐
        ≈⟨ refl⟩∘⟨ λ⇒∘λ⇐≈id ⟩
      T-B ∘ id
        ≈⟨ idʳ ⟩
      T-B ∎

bridge-α⇒-form (Var x)    B C = bridge-α⇒-form-Var x B C
bridge-α⇒-form (A₁ ⊗₀ A₂) B C = bridge-α⇒-form-⊗   A₁ A₂ B C

-- Phase 2: bridge-α⇒-form-⊗-unit body.  Strategy:
-- 1. Decompose F and T via λ-naturality: F-((unit⊗A₂)⊗(B⊗C)) ≈
--    F-(A₂⊗(B⊗C)) ∘ (λ⇒ ⊗ id), and symmetric on T.
-- 2. Apply α-naturality to commute α⇒_{unit⊗A₂} with (λ⇐ ⊗ id)⊗id.
-- 3. Cancel `(λ⇒ ⊗ id) ∘ (λ⇐ ⊗ (id ⊗ id))` to id via ⊗-∘-dist + λ⇒∘λ⇐.
-- 4. Recognize the result as bridge (α⇒ {A₂}{B}{C}) and apply IH.

private
  -- Decompose F at (unit ⊗ A₂)-prefix: F = F' ∘ (λ⇒ ⊗ id).
  F-decomp-unit
    : ∀ A B C
    → _≅_.from (unflatten-flatten-≈ ((unit ⊗₀ A) ⊗₀ (B ⊗₀ C)))
    ≈Term _≅_.from (unflatten-flatten-≈ (A ⊗₀ (B ⊗₀ C)))
          ∘ (λ⇒ {A} ⊗₁ id {B ⊗₀ C})
  F-decomp-unit A B C = begin
    -- LHS reduces to c-A,BC-to ∘ ((λ⇒ ∘ id ⊗ F-A) ⊗ F-BC)
    c-A,BC-to ∘ ((λ⇒ ∘ id ⊗₁ F-A) ⊗₁ F-BC)
      ≈⟨ refl⟩∘⟨ ⊗-resp-≈ λ⇒∘id⊗f≈f∘λ⇒ ≈-Term-refl ⟩
    c-A,BC-to ∘ ((F-A ∘ λ⇒) ⊗₁ F-BC)
      ≈⟨ refl⟩∘⟨ ⊗-resp-≈ ≈-Term-refl (≈-Term-sym idʳ) ⟩
    c-A,BC-to ∘ ((F-A ∘ λ⇒) ⊗₁ (F-BC ∘ id))
      ≈⟨ refl⟩∘⟨ ⊗-∘-dist ⟩
    c-A,BC-to ∘ (F-A ⊗₁ F-BC) ∘ (λ⇒ ⊗₁ id)
      ≈⟨ FM.sym-assoc ⟩
    (c-A,BC-to ∘ F-A ⊗₁ F-BC) ∘ (λ⇒ ⊗₁ id) ∎
    where
      F-A     = _≅_.from (unflatten-flatten-≈ A)
      F-BC    = _≅_.from (unflatten-flatten-≈ (B ⊗₀ C))
      c-A,BC-to = _≅_.to (unflatten-++-≅ (flatten A) (flatten B ++ flatten C))

  -- Decompose T at (unit ⊗ A₂)-prefix: T = ((λ⇐ ⊗ id) ⊗ id) ∘ T'.
  T-decomp-unit
    : ∀ A B C
    → _≅_.to (unflatten-flatten-≈ (((unit ⊗₀ A) ⊗₀ B) ⊗₀ C))
    ≈Term ((λ⇐ {A} ⊗₁ id {B}) ⊗₁ id {C})
          ∘ _≅_.to (unflatten-flatten-≈ ((A ⊗₀ B) ⊗₀ C))
  T-decomp-unit A B C = begin
    -- LHS reduces to ((((id ⊗ T-A) ∘ λ⇐) ⊗ T-B) ∘ c-A,B-from) ⊗ T-C ∘ c-A,B,C-from
    -- We push the λ⇐ outwards via repeated ⊗-∘-dist + λ⇐-naturality.
    (((id ⊗₁ T-A ∘ λ⇐) ⊗₁ T-B ∘ c-A,B-from) ⊗₁ T-C) ∘ c-AB,C-from
      -- Step 1: id ⊗ T-A ∘ λ⇐ ≈ λ⇐ ∘ T-A
      ≈⟨ ⊗-resp-≈ (⊗-resp-≈ (≈-Term-sym (λ⇐-naturality T-A)) ≈-Term-refl ⟩∘⟨refl) ≈-Term-refl ⟩∘⟨refl ⟩
    (((λ⇐ ∘ T-A) ⊗₁ T-B ∘ c-A,B-from) ⊗₁ T-C) ∘ c-AB,C-from
      -- Step 2: ⊗-∘-dist on (λ⇐ ∘ T-A) ⊗ T-B = (λ⇐ ⊗ id) ∘ (T-A ⊗ T-B)
      ≈⟨ ⊗-resp-≈ (⊗-resp-≈ ≈-Term-refl (≈-Term-sym idˡ) ⟩∘⟨refl) ≈-Term-refl ⟩∘⟨refl ⟩
    (((λ⇐ ∘ T-A) ⊗₁ (id ∘ T-B) ∘ c-A,B-from) ⊗₁ T-C) ∘ c-AB,C-from
      ≈⟨ ⊗-resp-≈ (⊗-∘-dist ⟩∘⟨refl) ≈-Term-refl ⟩∘⟨refl ⟩
    ((((λ⇐ ⊗₁ id) ∘ (T-A ⊗₁ T-B)) ∘ c-A,B-from) ⊗₁ T-C) ∘ c-AB,C-from
      ≈⟨ ⊗-resp-≈ FM.assoc ≈-Term-refl ⟩∘⟨refl ⟩
    (((λ⇐ ⊗₁ id) ∘ (T-A ⊗₁ T-B) ∘ c-A,B-from) ⊗₁ T-C) ∘ c-AB,C-from
      -- Step 3: ⊗-∘-dist on outer ⊗
      ≈⟨ ⊗-resp-≈ ≈-Term-refl (≈-Term-sym idˡ) ⟩∘⟨refl ⟩
    (((λ⇐ ⊗₁ id) ∘ (T-A ⊗₁ T-B) ∘ c-A,B-from) ⊗₁ (id ∘ T-C)) ∘ c-AB,C-from
      ≈⟨ ⊗-∘-dist ⟩∘⟨refl ⟩
    (((λ⇐ ⊗₁ id) ⊗₁ id) ∘ (((T-A ⊗₁ T-B) ∘ c-A,B-from) ⊗₁ T-C)) ∘ c-AB,C-from
      ≈⟨ FM.assoc ⟩
    ((λ⇐ ⊗₁ id) ⊗₁ id) ∘ (((T-A ⊗₁ T-B) ∘ c-A,B-from) ⊗₁ T-C) ∘ c-AB,C-from ∎
    where
      T-A         = _≅_.to (unflatten-flatten-≈ A)
      T-B         = _≅_.to (unflatten-flatten-≈ B)
      T-C         = _≅_.to (unflatten-flatten-≈ C)
      c-A,B-from  = _≅_.from (unflatten-++-≅ (flatten A) (flatten B))
      c-AB,C-from = _≅_.from (unflatten-++-≅ (flatten A ++ flatten B) (flatten C))

  -- λ-cancel: (λ⇒ ⊗ id) ∘ (λ⇐ ⊗ (id ⊗ id)) ≈ id.
  λ-cancel
    : ∀ {X Y Z} → (λ⇒ {X} ⊗₁ id {Y ⊗₀ Z})
                   ∘ (λ⇐ {X} ⊗₁ (id {Y} ⊗₁ id {Z}))
                ≈Term id
  λ-cancel = begin
    (λ⇒ ⊗₁ id) ∘ (λ⇐ ⊗₁ (id ⊗₁ id))
      ≈⟨ ≈-Term-sym ⊗-∘-dist ⟩
    (λ⇒ ∘ λ⇐) ⊗₁ (id ∘ (id ⊗₁ id))
      ≈⟨ ⊗-resp-≈ λ⇒∘λ⇐≈id idˡ ⟩
    id ⊗₁ (id ⊗₁ id)
      ≈⟨ ⊗-resp-≈ ≈-Term-refl id⊗id≈id ⟩
    id ⊗₁ id
      ≈⟨ id⊗id≈id ⟩
    id ∎

bridge-α⇒-form-⊗-unit A₂ B C = begin
  bridge (α⇒ {unit ⊗₀ A₂} {B} {C})
    -- Definitionally: F-((unit⊗A₂)⊗(B⊗C)) ∘ α⇒-uA₂ ∘ T-(((unit⊗A₂)⊗B)⊗C)
    -- Rewrite F via F-decomp-unit, T via T-decomp-unit.
    ≈⟨ F-decomp-unit A₂ B C ⟩∘⟨ refl⟩∘⟨ T-decomp-unit A₂ B C ⟩
  (F-A₂BC ∘ (λ⇒ ⊗₁ id)) ∘ α⇒-uA₂ ∘ (((λ⇐ ⊗₁ id) ⊗₁ id) ∘ T-A₂BC)
    ≈⟨ FM.assoc ⟩
  F-A₂BC ∘ (λ⇒ ⊗₁ id) ∘ α⇒-uA₂ ∘ ((λ⇐ ⊗₁ id) ⊗₁ id) ∘ T-A₂BC
    -- Group (λ⇒ ⊗ id) ∘ α⇒-uA₂ ∘ ((λ⇐ ⊗ id) ⊗ id) and use α-naturality.
    ≈⟨ refl⟩∘⟨ refl⟩∘⟨ FM.sym-assoc ⟩
  F-A₂BC ∘ (λ⇒ ⊗₁ id) ∘ (α⇒-uA₂ ∘ ((λ⇐ ⊗₁ id) ⊗₁ id)) ∘ T-A₂BC
    ≈⟨ refl⟩∘⟨ refl⟩∘⟨ α-comm ⟩∘⟨refl ⟩
  F-A₂BC ∘ (λ⇒ ⊗₁ id) ∘ ((λ⇐ ⊗₁ (id ⊗₁ id)) ∘ α⇒-A₂) ∘ T-A₂BC
    ≈⟨ refl⟩∘⟨ FM.sym-assoc ⟩
  F-A₂BC ∘ ((λ⇒ ⊗₁ id) ∘ (λ⇐ ⊗₁ (id ⊗₁ id)) ∘ α⇒-A₂) ∘ T-A₂BC
    ≈⟨ refl⟩∘⟨ FM.sym-assoc ⟩∘⟨refl ⟩
  F-A₂BC ∘ (((λ⇒ ⊗₁ id) ∘ (λ⇐ ⊗₁ (id ⊗₁ id))) ∘ α⇒-A₂) ∘ T-A₂BC
    ≈⟨ refl⟩∘⟨ λ-cancel ⟩∘⟨refl ⟩∘⟨refl ⟩
  F-A₂BC ∘ (id ∘ α⇒-A₂) ∘ T-A₂BC
    ≈⟨ refl⟩∘⟨ idˡ ⟩∘⟨refl ⟩
  F-A₂BC ∘ α⇒-A₂ ∘ T-A₂BC
    -- This is exactly bridge (α⇒ {A₂}{B}{C}) by definition.
    ≈⟨ bridge-α⇒-form A₂ B C ⟩
  α⇒-form-list (flatten A₂) (flatten B) (flatten C) ∎
  where
    F-A₂BC  = _≅_.from (unflatten-flatten-≈ (A₂ ⊗₀ (B ⊗₀ C)))
    T-A₂BC  = _≅_.to   (unflatten-flatten-≈ ((A₂ ⊗₀ B) ⊗₀ C))
    α⇒-uA₂  = α⇒ {unit ⊗₀ A₂} {B} {C}
    α⇒-A₂   = α⇒ {A₂} {B} {C}

--------------------------------------------------------------------------------
-- Phase 3: bridge-α⇒-form-⊗-Var body (Var x prefix sub-case).
--
-- Strategy:
-- 1. F-decomp-Var: F-((V⊗A)⊗(B⊗C)) ≈ (id ⊗ F-(A⊗(B⊗C))) ∘ α⇒_{V,A,B⊗C}.
-- 2. T-decomp-Var: T-(((V⊗A)⊗B)⊗C) ≈ (α⇐_{V,A,B} ⊗ id) ∘ α⇐_{V,A⊗B,C}
--                                  ∘ (id ⊗ T-((A⊗B)⊗C)).
-- 3. Pentagon collapses α⇒_{V,A,B⊗C} ∘ α⇒_{V⊗A,B,C} into
--    (id ⊗ α⇒_{A,B,C}) ∘ α⇒_{V,A⊗B,C} ∘ (α⇒_{V,A,B} ⊗ id).
-- 4. Cancel (α⇒_{V,A,B} ⊗ id) ∘ (α⇐_{V,A,B} ⊗ id) → id and
--    α⇒_{V,A⊗B,C} ∘ α⇐_{V,A⊗B,C} → id.
-- 5. Combine into id ⊗ (F-(A⊗(B⊗C)) ∘ α⇒_{A,B,C} ∘ T-((A⊗B)⊗C))
--                   = id ⊗ bridge (α⇒ {A}{B}{C}).
-- 6. Apply IH bridge-α⇒-form A B C.

private
  -- α⇐-comm: α⇐'s naturality, derived from α-comm + α-iso laws.
  α⇐-comm
    : ∀ {X Y Z X' Y' Z' : ObjTerm}
      (f : HomTerm X X') (g : HomTerm Y Y') (h : HomTerm Z Z')
    → α⇐ {X'} {Y'} {Z'} ∘ f ⊗₁ (g ⊗₁ h)
    ≈Term (f ⊗₁ g) ⊗₁ h ∘ α⇐ {X} {Y} {Z}
  α⇐-comm f g h = begin
    α⇐ ∘ f ⊗₁ (g ⊗₁ h)
      ≈⟨ ≈-Term-sym idʳ ⟩
    (α⇐ ∘ f ⊗₁ (g ⊗₁ h)) ∘ id
      ≈⟨ refl⟩∘⟨ ≈-Term-sym α⇒∘α⇐≈id ⟩
    (α⇐ ∘ f ⊗₁ (g ⊗₁ h)) ∘ (α⇒ ∘ α⇐)
      ≈⟨ FM.assoc ⟩
    α⇐ ∘ f ⊗₁ (g ⊗₁ h) ∘ α⇒ ∘ α⇐
      ≈⟨ refl⟩∘⟨ FM.sym-assoc ⟩
    α⇐ ∘ (f ⊗₁ (g ⊗₁ h) ∘ α⇒) ∘ α⇐
      ≈⟨ refl⟩∘⟨ ≈-Term-sym α-comm ⟩∘⟨refl ⟩
    α⇐ ∘ (α⇒ ∘ (f ⊗₁ g) ⊗₁ h) ∘ α⇐
      ≈⟨ FM.sym-assoc ⟩
    (α⇐ ∘ α⇒ ∘ (f ⊗₁ g) ⊗₁ h) ∘ α⇐
      ≈⟨ FM.sym-assoc ⟩∘⟨refl ⟩
    ((α⇐ ∘ α⇒) ∘ (f ⊗₁ g) ⊗₁ h) ∘ α⇐
      ≈⟨ (α⇐∘α⇒≈id ⟩∘⟨refl) ⟩∘⟨refl ⟩
    (id ∘ (f ⊗₁ g) ⊗₁ h) ∘ α⇐
      ≈⟨ idˡ ⟩∘⟨refl ⟩
    (f ⊗₁ g) ⊗₁ h ∘ α⇐ ∎

  -- F-decomp-Var: factor the Var x prefix out on the F side.
  F-decomp-Var
    : ∀ x A B C
    → _≅_.from (unflatten-flatten-≈ ((Var x ⊗₀ A) ⊗₀ (B ⊗₀ C)))
    ≈Term (id {Var x} ⊗₁ _≅_.from (unflatten-flatten-≈ (A ⊗₀ (B ⊗₀ C))))
          ∘ α⇒ {Var x} {A} {B ⊗₀ C}
  F-decomp-Var x A B C = begin
    -- Definitionally: ≅.from u-((V⊗A)⊗(B⊗C)) reduces to
    --   ((id ⊗ c-A,BC-to) ∘ α⇒-flat) ∘ (F-V⊗A ⊗ F-BC)
    ((id ⊗₁ c-A,BC-to) ∘ α⇒-flat) ∘ F-V⊗A ⊗₁ F-BC
      ≈⟨ refl⟩∘⟨ ⊗-resp-≈ (F-Vx⊗-collapse x A) ≈-Term-refl ⟩
    ((id ⊗₁ c-A,BC-to) ∘ α⇒-flat) ∘ (id ⊗₁ F-A) ⊗₁ F-BC
      ≈⟨ FM.assoc ⟩
    (id ⊗₁ c-A,BC-to) ∘ α⇒-flat ∘ (id ⊗₁ F-A) ⊗₁ F-BC
      ≈⟨ refl⟩∘⟨ α-comm ⟩
    (id ⊗₁ c-A,BC-to) ∘ id ⊗₁ (F-A ⊗₁ F-BC) ∘ α⇒-struct
      ≈⟨ FM.sym-assoc ⟩
    ((id ⊗₁ c-A,BC-to) ∘ id ⊗₁ (F-A ⊗₁ F-BC)) ∘ α⇒-struct
      ≈⟨ ≈-Term-sym ⊗-∘-dist ⟩∘⟨refl ⟩
    (id ∘ id) ⊗₁ (c-A,BC-to ∘ F-A ⊗₁ F-BC) ∘ α⇒-struct
      ≈⟨ ⊗-resp-≈ idˡ ≈-Term-refl ⟩∘⟨refl ⟩
    id ⊗₁ (c-A,BC-to ∘ F-A ⊗₁ F-BC) ∘ α⇒-struct ∎
    where
      F-A       = _≅_.from (unflatten-flatten-≈ A)
      F-BC      = _≅_.from (unflatten-flatten-≈ (B ⊗₀ C))
      F-V⊗A     = _≅_.from (unflatten-flatten-≈ (Var x ⊗₀ A))
      c-A,BC-to = _≅_.to   (unflatten-++-≅ (flatten A) (flatten B ++ flatten C))
      α⇒-flat   = α⇒ {Var x} {unflatten (flatten A)}
                    {unflatten (flatten B ++ flatten C)}
      α⇒-struct = α⇒ {Var x} {A} {B ⊗₀ C}

  -- T-decomp-Var: factor the Var x prefix out on the T side.
  T-decomp-Var
    : ∀ x A B C
    → _≅_.to (unflatten-flatten-≈ (((Var x ⊗₀ A) ⊗₀ B) ⊗₀ C))
    ≈Term (α⇐ {Var x} {A} {B} ⊗₁ id {C})
          ∘ α⇐ {Var x} {A ⊗₀ B} {C}
          ∘ (id {Var x} ⊗₁ _≅_.to (unflatten-flatten-≈ ((A ⊗₀ B) ⊗₀ C)))
  T-decomp-Var x A B C = begin
    -- Definitionally: ≅.to u-(((V⊗A)⊗B)⊗C) reduces to
    --   ((((ρ⇒ ⊗ T-A) ∘ α⇐-fl0 ∘ id ⊗ λ⇐) ⊗ T-B
    --       ∘ α⇐-fl1 ∘ id ⊗ c-A,B-from) ⊗ T-C)
    --      ∘ α⇐-fl2 ∘ id ⊗ c-A⊗B,C-from
    ((((ρ⇒ ⊗₁ T-A) ∘ α⇐-fl0 ∘ id ⊗₁ λ⇐) ⊗₁ T-B ∘ α⇐-fl1 ∘ id ⊗₁ c-A,B-from)
       ⊗₁ T-C) ∘ α⇐-fl2 ∘ id ⊗₁ c-A⊗B,C-from
      -- Step 1: T-Vx⊗-collapse on inner T-(V⊗A) ≈ id ⊗ T-A.
      ≈⟨ ⊗-resp-≈ (⊗-resp-≈ (T-Vx⊗-collapse x A) ≈-Term-refl
                    ⟩∘⟨refl) ≈-Term-refl ⟩∘⟨refl ⟩
    ((((id ⊗₁ T-A) ⊗₁ T-B ∘ α⇐-fl1 ∘ id ⊗₁ c-A,B-from)
       ⊗₁ T-C) ∘ α⇐-fl2 ∘ id ⊗₁ c-A⊗B,C-from)
      -- Step 2: sym-assoc to expose ((id⊗T-A)⊗T-B) ∘ α⇐-fl1 in left-paren form.
      ≈⟨ ⊗-resp-≈ FM.sym-assoc ≈-Term-refl ⟩∘⟨refl ⟩
    ((((id ⊗₁ T-A) ⊗₁ T-B) ∘ α⇐-fl1) ∘ id ⊗₁ c-A,B-from)
       ⊗₁ T-C ∘ α⇐-fl2 ∘ id ⊗₁ c-A⊗B,C-from
      -- Step 3: α⇐-comm-sym on ((id⊗T-A)⊗T-B) ∘ α⇐-fl1.
      ≈⟨ ⊗-resp-≈ (≈-Term-sym (α⇐-comm id T-A T-B) ⟩∘⟨refl)
                  ≈-Term-refl ⟩∘⟨refl ⟩
    ((α⇐-A,B ∘ id ⊗₁ (T-A ⊗₁ T-B)) ∘ id ⊗₁ c-A,B-from)
       ⊗₁ T-C ∘ α⇐-fl2 ∘ id ⊗₁ c-A⊗B,C-from
      -- Step 4: re-assoc.
      ≈⟨ ⊗-resp-≈ FM.assoc ≈-Term-refl ⟩∘⟨refl ⟩
    (α⇐-A,B ∘ id ⊗₁ (T-A ⊗₁ T-B) ∘ id ⊗₁ c-A,B-from)
       ⊗₁ T-C ∘ α⇐-fl2 ∘ id ⊗₁ c-A⊗B,C-from
      -- Step 5: combine (id ⊗ ...) ∘ (id ⊗ ...) via sym ⊗-∘-dist.
      ≈⟨ ⊗-resp-≈ (refl⟩∘⟨ ≈-Term-sym ⊗-∘-dist) ≈-Term-refl ⟩∘⟨refl ⟩
    (α⇐-A,B ∘ (id ∘ id) ⊗₁ ((T-A ⊗₁ T-B) ∘ c-A,B-from))
       ⊗₁ T-C ∘ α⇐-fl2 ∘ id ⊗₁ c-A⊗B,C-from
      -- Step 6: idˡ on (id ∘ id).
      ≈⟨ ⊗-resp-≈ (refl⟩∘⟨ ⊗-resp-≈ idˡ ≈-Term-refl)
                  ≈-Term-refl ⟩∘⟨refl ⟩
    (α⇐-A,B ∘ id ⊗₁ T-A⊗B) ⊗₁ T-C ∘ α⇐-fl2 ∘ id ⊗₁ c-A⊗B,C-from
      -- Step 7: distribute (X ∘ Y) ⊗ T-C using T-C = id ∘ T-C.
      ≈⟨ ⊗-resp-≈ ≈-Term-refl (≈-Term-sym idˡ) ⟩∘⟨refl ⟩
    (α⇐-A,B ∘ id ⊗₁ T-A⊗B) ⊗₁ (id ∘ T-C) ∘ α⇐-fl2 ∘ id ⊗₁ c-A⊗B,C-from
      ≈⟨ ⊗-∘-dist ⟩∘⟨refl ⟩
    ((α⇐-A,B ⊗₁ id) ∘ (id ⊗₁ T-A⊗B) ⊗₁ T-C) ∘ α⇐-fl2 ∘ id ⊗₁ c-A⊗B,C-from
      ≈⟨ FM.assoc ⟩
    (α⇐-A,B ⊗₁ id) ∘ (id ⊗₁ T-A⊗B) ⊗₁ T-C ∘ α⇐-fl2 ∘ id ⊗₁ c-A⊗B,C-from
      -- Step 8: align α⇐-fl2 with ((id ⊗ T-A⊗B) ⊗ T-C).
      ≈⟨ refl⟩∘⟨ FM.sym-assoc ⟩
    (α⇐-A,B ⊗₁ id) ∘ ((id ⊗₁ T-A⊗B) ⊗₁ T-C ∘ α⇐-fl2) ∘ id ⊗₁ c-A⊗B,C-from
      -- Step 9: α⇐-comm-sym on ((id ⊗ T-A⊗B) ⊗ T-C) ∘ α⇐-fl2.
      ≈⟨ refl⟩∘⟨ ≈-Term-sym (α⇐-comm id T-A⊗B T-C) ⟩∘⟨refl ⟩
    (α⇐-A,B ⊗₁ id) ∘ (α⇐-AB,C ∘ id ⊗₁ (T-A⊗B ⊗₁ T-C)) ∘ id ⊗₁ c-A⊗B,C-from
      -- Step 10: re-assoc.
      ≈⟨ refl⟩∘⟨ FM.assoc ⟩
    (α⇐-A,B ⊗₁ id) ∘ α⇐-AB,C ∘ id ⊗₁ (T-A⊗B ⊗₁ T-C) ∘ id ⊗₁ c-A⊗B,C-from
      -- Step 11: combine (id ⊗ ...) ∘ (id ⊗ ...) via sym ⊗-∘-dist + idˡ.
      ≈⟨ refl⟩∘⟨ refl⟩∘⟨ ≈-Term-sym ⊗-∘-dist ⟩
    (α⇐-A,B ⊗₁ id) ∘ α⇐-AB,C ∘ (id ∘ id) ⊗₁ ((T-A⊗B ⊗₁ T-C) ∘ c-A⊗B,C-from)
      ≈⟨ refl⟩∘⟨ refl⟩∘⟨ ⊗-resp-≈ idˡ ≈-Term-refl ⟩
    (α⇐-A,B ⊗₁ id) ∘ α⇐-AB,C ∘ id ⊗₁ T-AB⊗C ∎
    where
      T-A          = _≅_.to   (unflatten-flatten-≈ A)
      T-B          = _≅_.to   (unflatten-flatten-≈ B)
      T-C          = _≅_.to   (unflatten-flatten-≈ C)
      T-A⊗B        = _≅_.to   (unflatten-flatten-≈ (A ⊗₀ B))
      T-AB⊗C       = _≅_.to   (unflatten-flatten-≈ ((A ⊗₀ B) ⊗₀ C))
      α⇐-fl0       = α⇐ {Var x} {unit} {unflatten (flatten A)}
      α⇐-fl1       = α⇐ {Var x} {unflatten (flatten A)} {unflatten (flatten B)}
      α⇐-fl2       = α⇐ {Var x} {unflatten (flatten A ++ flatten B)}
                       {unflatten (flatten C)}
      α⇐-A,B       = α⇐ {Var x} {A} {B}
      α⇐-AB,C      = α⇐ {Var x} {A ⊗₀ B} {C}
      c-A,B-from   = _≅_.from (unflatten-++-≅ (flatten A) (flatten B))
      c-A⊗B,C-from = _≅_.from (unflatten-++-≅ (flatten A ++ flatten B) (flatten C))

bridge-α⇒-form-⊗-Var x A B C = begin
  bridge (α⇒ {Var x ⊗₀ A} {B} {C})
    -- Unfold F and T via decomp lemmas.
    ≈⟨ F-decomp-Var x A B C ⟩∘⟨ refl⟩∘⟨ T-decomp-Var x A B C ⟩
  ((id ⊗₁ F-ABC) ∘ α⇒-V,A,BC) ∘ α⇒-V⊗A ∘ ((α⇐-A,B ⊗₁ id) ∘ α⇐-AB,C ∘ (id ⊗₁ T-AB⊗C))
    ≈⟨ FM.assoc ⟩
  (id ⊗₁ F-ABC) ∘ α⇒-V,A,BC ∘ α⇒-V⊗A ∘ ((α⇐-A,B ⊗₁ id) ∘ α⇐-AB,C ∘ (id ⊗₁ T-AB⊗C))
    -- Group α⇒-V,A,BC ∘ α⇒-V⊗A so we can apply pentagon (sym).
    ≈⟨ refl⟩∘⟨ FM.sym-assoc ⟩
  (id ⊗₁ F-ABC) ∘ (α⇒-V,A,BC ∘ α⇒-V⊗A) ∘ ((α⇐-A,B ⊗₁ id) ∘ α⇐-AB,C ∘ (id ⊗₁ T-AB⊗C))
    -- Pentagon: α⇒-V,A,BC ∘ α⇒-V⊗A ≈ (id ⊗ α⇒-A,B,C) ∘ α⇒-V,AB,C ∘ (α⇒-V,A,B ⊗ id).
    ≈⟨ refl⟩∘⟨ ≈-Term-sym pentagon ⟩∘⟨refl ⟩
  (id ⊗₁ F-ABC) ∘ (id ⊗₁ α⇒-A,B,C ∘ α⇒-V,AB,C ∘ α⇒-V,A,B ⊗₁ id)
                 ∘ ((α⇐-A,B ⊗₁ id) ∘ α⇐-AB,C ∘ (id ⊗₁ T-AB⊗C))
    -- Now cancel pairs.  First unwrap two layers of assoc to fully right-associate.
    ≈⟨ refl⟩∘⟨ FM.assoc ⟩
  (id ⊗₁ F-ABC) ∘ id ⊗₁ α⇒-A,B,C ∘ (α⇒-V,AB,C ∘ α⇒-V,A,B ⊗₁ id)
                 ∘ ((α⇐-A,B ⊗₁ id) ∘ α⇐-AB,C ∘ (id ⊗₁ T-AB⊗C))
    ≈⟨ refl⟩∘⟨ refl⟩∘⟨ FM.assoc ⟩
  (id ⊗₁ F-ABC) ∘ id ⊗₁ α⇒-A,B,C ∘ α⇒-V,AB,C ∘ α⇒-V,A,B ⊗₁ id
                 ∘ ((α⇐-A,B ⊗₁ id) ∘ α⇐-AB,C ∘ (id ⊗₁ T-AB⊗C))
    -- Re-associate to bring (α⇒-V,A,B ⊗ id) and (α⇐-A,B ⊗ id) adjacent.
    ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ FM.sym-assoc ⟩
  (id ⊗₁ F-ABC) ∘ id ⊗₁ α⇒-A,B,C ∘ α⇒-V,AB,C ∘
    (α⇒-V,A,B ⊗₁ id ∘ (α⇐-A,B ⊗₁ id)) ∘ α⇐-AB,C ∘ (id ⊗₁ T-AB⊗C)
    -- Cancel α⇒-V,A,B ⊗ id ∘ α⇐-A,B ⊗ id ≈ id via ⊗-∘-dist + α⇒∘α⇐ + id⊗id.
    ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ collapse-α-VAB ⟩∘⟨refl ⟩
  (id ⊗₁ F-ABC) ∘ id ⊗₁ α⇒-A,B,C ∘ α⇒-V,AB,C ∘ id ∘ α⇐-AB,C ∘ (id ⊗₁ T-AB⊗C)
    -- Drop the id.
    ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ idˡ ⟩
  (id ⊗₁ F-ABC) ∘ id ⊗₁ α⇒-A,B,C ∘ α⇒-V,AB,C ∘ α⇐-AB,C ∘ (id ⊗₁ T-AB⊗C)
    -- Cancel α⇒-V,AB,C ∘ α⇐-V,AB,C ≈ id.
    ≈⟨ refl⟩∘⟨ refl⟩∘⟨ FM.sym-assoc ⟩
  (id ⊗₁ F-ABC) ∘ id ⊗₁ α⇒-A,B,C ∘ (α⇒-V,AB,C ∘ α⇐-AB,C) ∘ (id ⊗₁ T-AB⊗C)
    ≈⟨ refl⟩∘⟨ refl⟩∘⟨ α⇒∘α⇐≈id ⟩∘⟨refl ⟩
  (id ⊗₁ F-ABC) ∘ id ⊗₁ α⇒-A,B,C ∘ id ∘ (id ⊗₁ T-AB⊗C)
    ≈⟨ refl⟩∘⟨ refl⟩∘⟨ idˡ ⟩
  (id ⊗₁ F-ABC) ∘ id ⊗₁ α⇒-A,B,C ∘ (id ⊗₁ T-AB⊗C)
    -- Combine into id ⊗ (...) using sym ⊗-∘-dist twice.
    ≈⟨ refl⟩∘⟨ ≈-Term-sym ⊗-∘-dist ⟩
  (id ⊗₁ F-ABC) ∘ (id ∘ id) ⊗₁ (α⇒-A,B,C ∘ T-AB⊗C)
    ≈⟨ refl⟩∘⟨ ⊗-resp-≈ idˡ ≈-Term-refl ⟩
  (id ⊗₁ F-ABC) ∘ id ⊗₁ (α⇒-A,B,C ∘ T-AB⊗C)
    ≈⟨ ≈-Term-sym ⊗-∘-dist ⟩
  (id ∘ id) ⊗₁ (F-ABC ∘ α⇒-A,B,C ∘ T-AB⊗C)
    ≈⟨ ⊗-resp-≈ idˡ ≈-Term-refl ⟩
  id ⊗₁ (F-ABC ∘ α⇒-A,B,C ∘ T-AB⊗C)
    -- (F-ABC ∘ α⇒-A,B,C ∘ T-AB⊗C) is bridge (α⇒ {A}{B}{C}) by definition.
    ≈⟨ ⊗-resp-≈ ≈-Term-refl (bridge-α⇒-form A B C) ⟩
  id ⊗₁ α⇒-form-list (flatten A) (flatten B) (flatten C) ∎
  where
    F-ABC      = _≅_.from (unflatten-flatten-≈ (A ⊗₀ (B ⊗₀ C)))
    T-AB⊗C     = _≅_.to   (unflatten-flatten-≈ ((A ⊗₀ B) ⊗₀ C))
    α⇒-V,A,BC  = α⇒ {Var x} {A} {B ⊗₀ C}
    α⇒-V⊗A     = α⇒ {Var x ⊗₀ A} {B} {C}
    α⇒-A,B,C   = α⇒ {A} {B} {C}
    α⇒-V,AB,C  = α⇒ {Var x} {A ⊗₀ B} {C}
    α⇒-V,A,B   = α⇒ {Var x} {A} {B}
    α⇐-A,B     = α⇐ {Var x} {A} {B}
    α⇐-AB,C    = α⇐ {Var x} {A ⊗₀ B} {C}

    -- (α⇒-V,A,B ⊗ id) ∘ (α⇐-A,B ⊗ id) ≈ id, via ⊗-∘-dist + α⇒∘α⇐ + id⊗id.
    collapse-α-VAB
      : α⇒-V,A,B ⊗₁ id {C} ∘ α⇐-A,B ⊗₁ id {C} ≈Term id
    collapse-α-VAB = begin
      α⇒-V,A,B ⊗₁ id ∘ α⇐-A,B ⊗₁ id
        ≈⟨ ≈-Term-sym ⊗-∘-dist ⟩
      (α⇒-V,A,B ∘ α⇐-A,B) ⊗₁ (id ∘ id)
        ≈⟨ ⊗-resp-≈ α⇒∘α⇐≈id idˡ ⟩
      id ⊗₁ id
        ≈⟨ id⊗id≈id ⟩
      id ∎

-- bridge-α⇐-form is fully derived from bridge-α⇒-form using
-- `α⇒-α⇐-iso` + `bridge-∘` + `α⇐∘α⇒≈id` + `bridge-id-is-id`.
-- The chain: post-compose `bridge α⇐` with `α⇒-form ∘ α⇐-form` (= id),
-- use `bridge α⇒ ≈ α⇒-form` to fold back into `bridge`, recognize
-- `bridge α⇐ ∘ bridge α⇒` as `bridge (α⇐ ∘ α⇒)`, and apply
-- `α⇐∘α⇒≈id` + `bridge-id-is-id`.  Signature forward-declared above
-- so `bridge-α⇒-form-⊗-⊗` can use it.
bridge-α⇐-form A B C = begin
  bridge (α⇐ {A} {B} {C})
    ≈⟨ ≈-Term-sym idʳ ⟩
  bridge (α⇐ {A} {B} {C}) ∘ id
    ≈⟨ refl⟩∘⟨ ≈-Term-sym (α⇒-α⇐-iso (flatten A) (flatten B) (flatten C)) ⟩
  bridge (α⇐ {A} {B} {C}) ∘ (α⇒-form-list (flatten A) (flatten B) (flatten C)
                              ∘ α⇐-form-list (flatten A) (flatten B) (flatten C))
    ≈⟨ FM.sym-assoc ⟩
  (bridge (α⇐ {A} {B} {C}) ∘ α⇒-form-list (flatten A) (flatten B) (flatten C))
   ∘ α⇐-form-list (flatten A) (flatten B) (flatten C)
    ≈⟨ (refl⟩∘⟨ ≈-Term-sym (bridge-α⇒-form A B C)) ⟩∘⟨refl ⟩
  (bridge (α⇐ {A} {B} {C}) ∘ bridge (α⇒ {A} {B} {C}))
   ∘ α⇐-form-list (flatten A) (flatten B) (flatten C)
    ≈⟨ ≈-Term-sym (bridge-∘ α⇐ α⇒) ⟩∘⟨refl ⟩
  bridge (α⇐ {A} {B} {C} ∘ α⇒ {A} {B} {C})
   ∘ α⇐-form-list (flatten A) (flatten B) (flatten C)
    ≈⟨ bridge-resp-≈Term α⇐∘α⇒≈id ⟩∘⟨refl ⟩
  bridge (id {(A ⊗₀ B) ⊗₀ C}) ∘ α⇐-form-list (flatten A) (flatten B) (flatten C)
    ≈⟨ bridge-id-is-id ((A ⊗₀ B) ⊗₀ C) ⟩∘⟨refl ⟩
  id ∘ α⇐-form-list (flatten A) (flatten B) (flatten C)
    ≈⟨ idˡ ⟩
  α⇐-form-list (flatten A) (flatten B) (flatten C) ∎

-- Combine list-induction + bridge-form for α⇒-coherence.

α⇒-coherence
  : ∀ A B C
  → subst₂ HomTerm refl
            (cong unflatten (++-assoc (flatten A) (flatten B) (flatten C)))
            id
    ≈Term bridge (α⇒ {A} {B} {C})
α⇒-coherence A B C = begin
  subst₂ HomTerm refl (cong unflatten (++-assoc (flatten A) (flatten B) (flatten C))) id
    ≈⟨ ≡⇒≈Term (subst₂-refl-cod (++-assoc (flatten A) (flatten B) (flatten C))) ⟩
  subst (λ z → HomTerm (unflatten ((flatten A ++ flatten B) ++ flatten C)) (unflatten z))
        (++-assoc (flatten A) (flatten B) (flatten C)) id
    ≈⟨ α⇒-coh-list (flatten A) (flatten B) (flatten C) ⟩
  α⇒-form-list (flatten A) (flatten B) (flatten C)
    ≈⟨ ≈-Term-sym (bridge-α⇒-form A B C) ⟩
  bridge (α⇒ {A} {B} {C}) ∎

α⇐-coherence
  : ∀ A B C
  → subst₂ HomTerm
            (cong unflatten (++-assoc (flatten A) (flatten B) (flatten C)))
            refl id
    ≈Term bridge (α⇐ {A} {B} {C})
α⇐-coherence A B C = begin
  subst₂ HomTerm (cong unflatten (++-assoc (flatten A) (flatten B) (flatten C))) refl id
    ≈⟨ ≡⇒≈Term (subst₂-refl-dom (++-assoc (flatten A) (flatten B) (flatten C))) ⟩
  subst (λ z → HomTerm (unflatten z) (unflatten ((flatten A ++ flatten B) ++ flatten C)))
        (++-assoc (flatten A) (flatten B) (flatten C)) id
    ≈⟨ α⇐-coh-list (flatten A) (flatten B) (flatten C) ⟩
  α⇐-form-list (flatten A) (flatten B) (flatten C)
    ≈⟨ ≈-Term-sym (bridge-α⇐-form A B C) ⟩
  bridge (α⇐ {A} {B} {C}) ∎

--------------------------------------------------------------------------------
-- Wire the four ρ/α axioms via the constructive chain
-- shape → IH (decode-id-is-id) → coherence.

decode-roundtrip-ρ⇒
  : ∀ {A} → decode (ρ⇒ {A}) ≈Term bridge (ρ⇒ {A})
decode-roundtrip-ρ⇒ {A} = begin
  decode (ρ⇒ {A})
    ≈⟨ ≡⇒≈Term (decode-ρ⇒-shape A) ⟩
  subst₂ HomTerm refl (cong unflatten (++-identityʳ (flatten A)))
                       (decode (id {A ⊗₀ unit}))
    ≈⟨ subst₂-resp-≈Term refl (++-identityʳ (flatten A))
                          (decode-id-is-id (A ⊗₀ unit)) ⟩
  subst₂ HomTerm refl (cong unflatten (++-identityʳ (flatten A))) id
    ≈⟨ ρ⇒-coherence A ⟩
  bridge (ρ⇒ {A}) ∎

decode-roundtrip-ρ⇐
  : ∀ {A} → decode (ρ⇐ {A}) ≈Term bridge (ρ⇐ {A})
decode-roundtrip-ρ⇐ {A} = begin
  decode (ρ⇐ {A})
    ≈⟨ ≡⇒≈Term (decode-ρ⇐-shape A) ⟩
  subst₂ HomTerm (cong unflatten (++-identityʳ (flatten A))) refl
                       (decode (id {A ⊗₀ unit}))
    ≈⟨ subst₂-resp-≈Term (++-identityʳ (flatten A)) refl
                          (decode-id-is-id (A ⊗₀ unit)) ⟩
  subst₂ HomTerm (cong unflatten (++-identityʳ (flatten A))) refl id
    ≈⟨ ρ⇐-coherence A ⟩
  bridge (ρ⇐ {A}) ∎

decode-roundtrip-α⇒
  : ∀ {A B C} → decode (α⇒ {A} {B} {C}) ≈Term bridge (α⇒ {A} {B} {C})
decode-roundtrip-α⇒ {A} {B} {C} = begin
  decode (α⇒ {A} {B} {C})
    ≈⟨ ≡⇒≈Term (decode-α⇒-shape A B C) ⟩
  subst₂ HomTerm refl
          (cong unflatten (++-assoc (flatten A) (flatten B) (flatten C)))
          (decode (id {(A ⊗₀ B) ⊗₀ C}))
    ≈⟨ subst₂-resp-≈Term refl (++-assoc (flatten A) (flatten B) (flatten C))
                          (decode-id-is-id ((A ⊗₀ B) ⊗₀ C)) ⟩
  subst₂ HomTerm refl
          (cong unflatten (++-assoc (flatten A) (flatten B) (flatten C)))
          id
    ≈⟨ α⇒-coherence A B C ⟩
  bridge (α⇒ {A} {B} {C}) ∎

decode-roundtrip-α⇐
  : ∀ {A B C} → decode (α⇐ {A} {B} {C}) ≈Term bridge (α⇐ {A} {B} {C})
decode-roundtrip-α⇐ {A} {B} {C} = begin
  decode (α⇐ {A} {B} {C})
    ≈⟨ ≡⇒≈Term (decode-α⇐-shape A B C) ⟩
  subst₂ HomTerm
          (cong unflatten (++-assoc (flatten A) (flatten B) (flatten C)))
          refl (decode (id {(A ⊗₀ B) ⊗₀ C}))
    ≈⟨ subst₂-resp-≈Term (++-assoc (flatten A) (flatten B) (flatten C)) refl
                          (decode-id-is-id ((A ⊗₀ B) ⊗₀ C)) ⟩
  subst₂ HomTerm
          (cong unflatten (++-assoc (flatten A) (flatten B) (flatten C)))
          refl id
    ≈⟨ α⇐-coherence A B C ⟩
  bridge (α⇐ {A} {B} {C}) ∎

--------------------------------------------------------------------------------
-- The roundtrip proof, by induction on the term.

decode-roundtrip
  : ∀ {A B} (f : HomTerm A B) → decode f ≈Term bridge f
decode-roundtrip (Agen g)         = decode-roundtrip-Agen g
decode-roundtrip id               = decode-roundtrip-id
decode-roundtrip (g ∘ f)          =
  decode-roundtrip-∘ g f (decode-roundtrip g) (decode-roundtrip f)
decode-roundtrip (f ⊗₁ g)         =
  decode-roundtrip-⊗₁ f g (decode-roundtrip f) (decode-roundtrip g)
decode-roundtrip λ⇒               = decode-roundtrip-λ⇒
decode-roundtrip λ⇐               = decode-roundtrip-λ⇐
decode-roundtrip ρ⇒               = decode-roundtrip-ρ⇒
decode-roundtrip ρ⇐               = decode-roundtrip-ρ⇐
decode-roundtrip α⇒               = decode-roundtrip-α⇒
decode-roundtrip α⇐               = decode-roundtrip-α⇐
decode-roundtrip (σ ⦃ s ⦄)        = decode-roundtrip-σ ⦃ s ⦄
