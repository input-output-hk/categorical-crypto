{-# OPTIONS --safe --with-K #-}

--------------------------------------------------------------------------------
-- Safe extraction of constructive lemmas from `DecodeRoundtrip.agda`.
--
-- `DecodeRoundtrip.agda` co-resides with several postulates
-- (`decode-{∘,⊗,ρ⇒,ρ⇐,α⇒,α⇐}-shape`, `decode-roundtrip-{Agen,σ}`,
-- `c-iso-assoc-from-cons`, `bridge-α⇒-form-⊗-⊗`).  This file extracts
-- ONLY the constructive (postulate-free) content so it can be used in
-- `--safe` downstream code without inheriting those postulates.
--
-- Extracted (constructive):
--   * Bridge distributivity: `bridge-∘`, `bridge-⊗-decompose`, `bridge-⊗`.
--   * `decode-id-is-id-unit`, `decode-id-is-id-Var` (only the truly
--     constructive base-cases of `decode-id-is-id` — the `⊗₀` case
--     uses the `decode-⊗-shape` postulate).
--   * `bridge-id-is-id`, `bridge-λ⇒-is-id`, `bridge-λ⇐-is-id`.
--   * Subst helpers: `≡⇒≈Term`, `subst₂-resp-≈Term`,
--     `subst₂-refl-{cod,dom}`, `subst-{cod,dom}-cons`.
--   * Bridge forms for ρ: `bridge-ρ⇒-form`, `ρ⇐-naturality`,
--     `bridge-ρ⇐-form`.
--   * Coherence-list lemmas: `ρ⇒-coh-list`, `ρ⇐-coh-list`,
--     `α⇒-coh-list`, `α⇐-coh-list`, `α⇒-form-list`, `α⇐-form-list`.
--   * α-form isos: `α⇒-α⇐-iso`, `α⇐-α⇒-iso`.
--   * Mac Lane / solver helpers: `α⇒-λ⇐-collapse`, `pentagon-rewrite`,
--     `id-⊗-subst-bridge`, `id-⊗-respects-∘`, `α⇐-comm-top`,
--     `λ⇐-naturality`.
--   * Var-base case `bridge-α⇒-form-Var`.
--   * Unit/Var collapse helpers `F-unit⊗-collapse`, `T-unit⊗-collapse`,
--     `F-Vx⊗-collapse`, `T-Vx⊗-collapse`.
--
-- NOT extracted (depend transitively on postulates):
--   * `decode-id-is-id` for `A ⊗₀ B`: uses `decode-⊗-shape`.
--   * `decode-roundtrip-{∘,⊗₁,id,λ⇒,λ⇐,ρ⇒,ρ⇐,α⇒,α⇐}`: each chains via
--     a `decode-X-shape` postulate.
--   * `bridge-α⇒-form` for compound A: cons case relies on
--     `bridge-α⇒-form-⊗-⊗`.
--   * `bridge-α⇐-form`: depends on full `bridge-α⇒-form`.
--   * `c-iso-assoc-from` for cons: postulated cons-case.
--   * `α⇒-coherence`, `α⇐-coherence`: chain via `bridge-α⇒-form`.
--   * `ρ⇒-coherence`, `ρ⇐-coherence`: depend on `bridge-ρ⇒-form` (OK),
--     but the consumer-facing axiom needs `decode-ρ⇒-shape` (postulate),
--     so we ship the half that is constructive: `ρ⇒-coherence` itself.
--------------------------------------------------------------------------------

open import Categories.APROP
open import Categories.Category.Monoidal using (Monoidal)

module Categories.APROP.Hypergraph.Completeness.DecodeRoundtripSafe
  (sig : APROPSignature) where

open APROP sig
open import Categories.APROP.Hypergraph.FromAPROP sig
  using (flatten)
open import Categories.APROP.Hypergraph.Completeness.Unflatten sig
  using (unflatten; unflatten-flatten-≈; unflatten-++-≅)
open import Categories.APROP.Hypergraph.Completeness.DecodeAttempt sig
  using (decode; bridge)

open import Categories.Category using (Category)
open import Categories.Morphism FreeMonoidal using (_≅_)
-- Shared dual-associator commutativity.
open import Categories.PermuteCoherence.Faithfulness asFreeMonoidalData using (α⇐-comm)
open import Categories.Category.Monoidal.Properties Monoidal-FreeMonoidal
  using (module Kelly's)
open Kelly's using (coherence₁; coherence₂; coherence-inv₂; coherence₃)
open import Categories.Category.Monoidal.Utilities Monoidal-FreeMonoidal
  using (triangle-inv)
open import Data.List using (List; []; _∷_; _++_)
open import Data.List.Properties using (++-identityʳ; ++-assoc)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; sym; subst; subst₂)
open import Relation.Binary.PropositionalEquality.Properties using (subst-∘)

private
  module FM = Category FreeMonoidal

open FM.HomReasoning

--------------------------------------------------------------------------------
-- Foundation lemmas: `bridge-∘`, `bridge-⊗`.

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

bridge-⊗
  : ∀ {A B C D} (f : HomTerm A B) (g : HomTerm C D)
  → bridge (f ⊗₁ g)
  ≈Term _≅_.to   (unflatten-++-≅ (flatten B) (flatten D))
       ∘ (bridge f ⊗₁ bridge g)
       ∘ _≅_.from (unflatten-++-≅ (flatten A) (flatten C))
bridge-⊗ {A} {B} {C} {D} f g = begin
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
-- `decode (id {A})` base cases (constructive part only).  The `A ⊗₀ B`
-- case uses `decode-⊗-shape` (postulated in DecodeRoundtrip), so we
-- only extract the `unit` and `Var x` base-cases here.

decode-id-is-id-unit : decode (id {unit}) ≈Term id
decode-id-is-id-unit = begin
  (id ∘ id) ∘ id   ≈⟨ idʳ ⟩
  id ∘ id          ≈⟨ idˡ ⟩
  id               ∎

decode-id-is-id-Var : ∀ x → decode (id {Var x}) ≈Term id
decode-id-is-id-Var x = begin
  ((id ⊗₁ id) ∘ ((id ⊗₁ id) ∘ id)) ∘ id
                                    ≈⟨ idʳ ⟩
  (id ⊗₁ id) ∘ ((id ⊗₁ id) ∘ id)    ≈⟨ id⊗id≈id ⟩∘⟨refl ⟩
  id ∘ ((id ⊗₁ id) ∘ id)            ≈⟨ idˡ ⟩
  (id ⊗₁ id) ∘ id                   ≈⟨ idʳ ⟩
  id ⊗₁ id                          ≈⟨ id⊗id≈id ⟩
  id                                ∎

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
-- bridge (λ⇒) and bridge (λ⇐) reduce to `id`.

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

--------------------------------------------------------------------------------
-- Helpers for chaining `_≡_` and `≈Term`, and for transporting `≈Term`
-- across `subst₂`.

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
-- `subst (cong unflatten _)`-of-`id` workhorses.

subst₂-refl-cod
  : ∀ {As As' : List X} (eq : As ≡ As')
  → subst₂ HomTerm refl (cong unflatten eq) (id {unflatten As})
  ≡ subst (λ z → HomTerm (unflatten As) (unflatten z)) eq id
subst₂-refl-cod refl = refl

subst₂-refl-dom
  : ∀ {As As' : List X} (eq : As ≡ As')
  → subst₂ HomTerm (cong unflatten eq) refl (id {unflatten As})
  ≡ subst (λ z → HomTerm (unflatten z) (unflatten As)) eq id
subst₂-refl-dom refl = refl

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

-- The first, shared step of all four `*-coh-list` cons cases: pushing the
-- `cong (y ∷_)` of a `subst` through `unflatten` via `subst-∘`, re-binding the
-- substituted variable from the cons'd list to its tail.  The four cases then
-- finish with `subst-{cod,dom}-cons`.  `L`/`R` are the dom/cod endpoints
-- (one constant fixed side, the other the moving `unflatten z`); the cod
-- variants (ρ⇒, α⇒) and dom variants (ρ⇐, α⇐) only differ in which is which.
cons-coh-step
  : ∀ (y : X) {as as' : List X} (eq : as ≡ as') (L R : List X → ObjTerm)
      (m : HomTerm (L (y ∷ as)) (R (y ∷ as)))
  → subst (λ z → HomTerm (L z) (R z)) (cong (y ∷_) eq) m
    ≈Term subst (λ z → HomTerm (L (y ∷ z)) (R (y ∷ z))) eq m
cons-coh-step y eq L R m =
  ≡⇒≈Term (sym (subst-∘ {P = λ z → HomTerm (L z) (R z)} {f = y ∷_} eq))

--------------------------------------------------------------------------------
-- Bridge form for ρ⇒.

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

--------------------------------------------------------------------------------
-- ρ⇐-naturality, derived from ρ⇒-naturality + iso laws.

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

--------------------------------------------------------------------------------
-- Bridge form for ρ⇐.

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

--------------------------------------------------------------------------------
-- List-coherence for ρ⇒.

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
    ≈⟨ cons-coh-step y (++-identityʳ ys)
         (λ _ → Var y ⊗₀ unflatten (ys ++ [])) (λ z → unflatten z) id ⟩
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

--------------------------------------------------------------------------------
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
    ≈⟨ cons-coh-step y (++-identityʳ ys)
         (λ z → unflatten z) (λ _ → Var y ⊗₀ unflatten (ys ++ [])) id ⟩
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

--------------------------------------------------------------------------------
-- ρ⇒-coherence / ρ⇐-coherence: combine list-coherence with bridge-form.

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

--------------------------------------------------------------------------------
-- α-form lists and their list-induction lemmas.

α⇒-form-list
  : (xs ys zs : List X)
  → HomTerm (unflatten ((xs ++ ys) ++ zs)) (unflatten (xs ++ ys ++ zs))
α⇒-form-list []       ys zs = id
α⇒-form-list (x ∷ xs) ys zs = id {Var x} ⊗₁ α⇒-form-list xs ys zs

α⇐-form-list
  : (xs ys zs : List X)
  → HomTerm (unflatten (xs ++ ys ++ zs)) (unflatten ((xs ++ ys) ++ zs))
α⇐-form-list []       ys zs = id
α⇐-form-list (x ∷ xs) ys zs = id {Var x} ⊗₁ α⇐-form-list xs ys zs

α⇒-coh-list
  : ∀ (xs ys zs : List X)
  → subst (λ z → HomTerm (unflatten ((xs ++ ys) ++ zs)) (unflatten z))
          (++-assoc xs ys zs) id
    ≈Term α⇒-form-list xs ys zs
α⇒-coh-list []       ys zs = ≈-Term-refl
α⇒-coh-list (x ∷ xs) ys zs = begin
  subst (λ z → HomTerm (Var x ⊗₀ unflatten ((xs ++ ys) ++ zs)) (unflatten z))
        (cong (x ∷_) (++-assoc xs ys zs)) id
    ≈⟨ cons-coh-step x (++-assoc xs ys zs)
         (λ _ → Var x ⊗₀ unflatten ((xs ++ ys) ++ zs)) (λ z → unflatten z) id ⟩
  subst (λ z → HomTerm (Var x ⊗₀ unflatten ((xs ++ ys) ++ zs))
                        (Var x ⊗₀ unflatten z))
        (++-assoc xs ys zs) id
    ≈⟨ subst-cod-cons x (++-assoc xs ys zs) ⟩
  id {Var x} ⊗₁ subst (λ z → HomTerm (unflatten ((xs ++ ys) ++ zs)) (unflatten z))
                       (++-assoc xs ys zs) id
    ≈⟨ ⊗-resp-≈ ≈-Term-refl (α⇒-coh-list xs ys zs) ⟩
  id ⊗₁ α⇒-form-list xs ys zs ∎

α⇐-coh-list
  : ∀ (xs ys zs : List X)
  → subst (λ z → HomTerm (unflatten z) (unflatten ((xs ++ ys) ++ zs)))
          (++-assoc xs ys zs) id
    ≈Term α⇐-form-list xs ys zs
α⇐-coh-list []       ys zs = ≈-Term-refl
α⇐-coh-list (x ∷ xs) ys zs = begin
  subst (λ z → HomTerm (unflatten z) (Var x ⊗₀ unflatten ((xs ++ ys) ++ zs)))
        (cong (x ∷_) (++-assoc xs ys zs)) id
    ≈⟨ cons-coh-step x (++-assoc xs ys zs)
         (λ z → unflatten z) (λ _ → Var x ⊗₀ unflatten ((xs ++ ys) ++ zs)) id ⟩
  subst (λ z → HomTerm (Var x ⊗₀ unflatten z)
                        (Var x ⊗₀ unflatten ((xs ++ ys) ++ zs)))
        (++-assoc xs ys zs) id
    ≈⟨ subst-dom-cons x (++-assoc xs ys zs) ⟩
  id {Var x} ⊗₁ subst (λ z → HomTerm (unflatten z) (unflatten ((xs ++ ys) ++ zs)))
                       (++-assoc xs ys zs) id
    ≈⟨ ⊗-resp-≈ ≈-Term-refl (α⇐-coh-list xs ys zs) ⟩
  id ⊗₁ α⇐-form-list xs ys zs ∎

--------------------------------------------------------------------------------
-- α⇒-form / α⇐-form mutual inverses.

-- The composite of `id {Var w} ⊗₁ F` with `id {Var w} ⊗₁ G` collapses to
-- `id {Var w} ⊗₁ (F ∘ G)` — the cons summand shared by both α-form isos.
⊗-cons-step
  : ∀ {w} {A B : ObjTerm} (F : HomTerm A B) (G : HomTerm B A)
  → (id {Var w} ⊗₁ F) ∘ (id {Var w} ⊗₁ G) ≈Term id {Var w} ⊗₁ (F ∘ G)
⊗-cons-step F G = begin
  (id ⊗₁ F) ∘ (id ⊗₁ G)
    ≈⟨ ≈-Term-sym ⊗-∘-dist ⟩
  (id ∘ id) ⊗₁ (F ∘ G)
    ≈⟨ ⊗-resp-≈ idˡ ≈-Term-refl ⟩
  id ⊗₁ (F ∘ G) ∎

-- Both α-form isos are the same `id {Var x} ⊗₁`-distributing induction with the
-- two `*-form-list`s composed in opposite order; their cons cases share exactly
-- the `⊗-cons-step` collapse above.  (The composites are endo at different
-- objects — `unflatten ((xs ++ ys) ++ zs)` vs `unflatten (xs ++ ys ++ zs)` — so
-- a single dependently-typed helper would have to transport across that; we
-- instead keep the two short inductions and share their one nontrivial step.)
α⇒-α⇐-iso
  : ∀ (xs ys zs : List X)
  → α⇒-form-list xs ys zs ∘ α⇐-form-list xs ys zs ≈Term id
α⇒-α⇐-iso []       ys zs = idˡ
α⇒-α⇐-iso (x ∷ xs) ys zs = begin
  (id {Var x} ⊗₁ α⇒-form-list xs ys zs) ∘ (id {Var x} ⊗₁ α⇐-form-list xs ys zs)
    ≈⟨ ⊗-cons-step (α⇒-form-list xs ys zs) (α⇐-form-list xs ys zs) ⟩
  id ⊗₁ (α⇒-form-list xs ys zs ∘ α⇐-form-list xs ys zs)
    ≈⟨ ⊗-resp-≈ ≈-Term-refl (α⇒-α⇐-iso xs ys zs) ⟩
  id ⊗₁ id
    ≈⟨ id⊗id≈id ⟩
  id ∎

α⇐-α⇒-iso
  : ∀ (xs ys zs : List X)
  → α⇐-form-list xs ys zs ∘ α⇒-form-list xs ys zs ≈Term id
α⇐-α⇒-iso []       ys zs = idˡ
α⇐-α⇒-iso (x ∷ xs) ys zs = begin
  (id {Var x} ⊗₁ α⇐-form-list xs ys zs) ∘ (id {Var x} ⊗₁ α⇒-form-list xs ys zs)
    ≈⟨ ⊗-cons-step (α⇐-form-list xs ys zs) (α⇒-form-list xs ys zs) ⟩
  id ⊗₁ (α⇐-form-list xs ys zs ∘ α⇒-form-list xs ys zs)
    ≈⟨ ⊗-resp-≈ ≈-Term-refl (α⇐-α⇒-iso xs ys zs) ⟩
  id ⊗₁ id
    ≈⟨ id⊗id≈id ⟩
  id ∎

--------------------------------------------------------------------------------
-- Mac Lane / solver helpers.

α⇒-λ⇐-collapse
  : ∀ {X Y} → α⇒ {unit} {X} {Y} ∘ (λ⇐ {X} ⊗₁ id {Y}) ≈Term λ⇐ {X ⊗₀ Y}
α⇒-λ⇐-collapse {X} {Y} = lemma
  where open import Categories.APROP.Hypergraph.Completeness.CoherenceSolver sig
        open 2-objs X Y renaming (α⇒-λ⇐-collapse to lemma)

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

id-⊗-subst-bridge
  : ∀ {x : X} {xs₁ ys'} (e : xs₁ ≡ ys')
  → (id {Var x} ⊗₁ subst (λ z → HomTerm (unflatten xs₁) (unflatten z)) e id)
  ≈Term subst (λ z → HomTerm (Var x ⊗₀ unflatten xs₁) (Var x ⊗₀ unflatten z)) e id
id-⊗-subst-bridge refl = id⊗id≈id

id-⊗-respects-∘
  : ∀ {X A B C} (f : HomTerm A B) (g : HomTerm B C)
  → id {X} ⊗₁ (g ∘ f) ≈Term (id {X} ⊗₁ g) ∘ (id {X} ⊗₁ f)
id-⊗-respects-∘ f g = begin
  id ⊗₁ (g ∘ f)
    ≈⟨ ⊗-resp-≈ (≈-Term-sym idˡ) ≈-Term-refl ⟩
  (id ∘ id) ⊗₁ (g ∘ f)
    ≈⟨ ⊗-∘-dist ⟩
  id ⊗₁ g ∘ id ⊗₁ f ∎

-- Explicit-argument wrapper around the shared `α⇐-comm` from `Faithfulness`.
α⇐-comm-top
  : ∀ {X Y Z X' Y' Z' : ObjTerm}
    (f : HomTerm X X') (g : HomTerm Y Y') (h : HomTerm Z Z')
  → α⇐ {X'} {Y'} {Z'} ∘ f ⊗₁ (g ⊗₁ h)
  ≈Term (f ⊗₁ g) ⊗₁ h ∘ α⇐ {X} {Y} {Z}
α⇐-comm-top f g h = α⇐-comm {h = f} {i = g} {j = h}

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

--------------------------------------------------------------------------------
-- Helper for Var x bridge-α⇒ chase: collapse (ρ⇒ ⊗ f) ∘ α⇐ ∘ (id ⊗ λ⇐).

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

--------------------------------------------------------------------------------
-- F/T collapse lemmas for unit and Var x prefixes.

F-unit⊗-collapse
  : ∀ X → _≅_.from (unflatten-flatten-≈ (unit ⊗₀ X)) ∘ λ⇐
        ≈Term _≅_.from (unflatten-flatten-≈ X)
F-unit⊗-collapse X = begin
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

T-unit⊗-collapse
  : ∀ X → λ⇒ ∘ _≅_.to (unflatten-flatten-≈ (unit ⊗₀ X))
        ≈Term _≅_.to (unflatten-flatten-≈ X)
T-unit⊗-collapse X = begin
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

F-Vx⊗-collapse
  : ∀ x X → _≅_.from (unflatten-flatten-≈ (Var x ⊗₀ X))
          ≈Term id {Var x} ⊗₁ _≅_.from (unflatten-flatten-≈ X)
F-Vx⊗-collapse x X = begin
  ((id ⊗₁ λ⇒) ∘ α⇒) ∘ (ρ⇐ ⊗₁ F-X)
    ≈⟨ triangle ⟩∘⟨refl ⟩
  (ρ⇒ ⊗₁ id) ∘ (ρ⇐ ⊗₁ F-X)
    ≈⟨ ≈-Term-sym ⊗-∘-dist ⟩
  (ρ⇒ ∘ ρ⇐) ⊗₁ (id ∘ F-X)
    ≈⟨ ⊗-resp-≈ ρ⇒∘ρ⇐≈id idˡ ⟩
  id ⊗₁ F-X ∎
  where
    F-X = _≅_.from (unflatten-flatten-≈ X)

T-Vx⊗-collapse
  : ∀ x X → _≅_.to (unflatten-flatten-≈ (Var x ⊗₀ X))
          ≈Term id {Var x} ⊗₁ _≅_.to (unflatten-flatten-≈ X)
T-Vx⊗-collapse x X = collapse-ρ⇒-α⇐-λ⇐ (_≅_.to (unflatten-flatten-≈ X))

--------------------------------------------------------------------------------
-- Var-base case of bridge-α⇒-form (constructive: does not depend on
-- bridge-α⇒-form-⊗-⊗ postulate).

bridge-α⇒-form-Var
  : ∀ x B C → bridge (α⇒ {Var x} {B} {C})
            ≈Term α⇒-form-list (x ∷ []) (flatten B) (flatten C)
bridge-α⇒-form-Var x B C = begin
  bridge (α⇒ {Var x} {B} {C})
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
    ≈⟨ refl⟩∘⟨ refl⟩∘⟨ ⊗-resp-≈ (collapse-ρ⇒-α⇐-λ⇐ T-B) ≈-Term-refl ⟩∘⟨refl ⟩
  (id ⊗₁ F-BC) ∘ α⇒-VBC ∘
    ((id ⊗₁ T-B) ⊗₁ T-C ∘ α⇐-c2 ∘ id ⊗₁ cBC-from)
    ≈⟨ refl⟩∘⟨ FM.sym-assoc ⟩
  (id ⊗₁ F-BC) ∘ (α⇒-VBC ∘ (id ⊗₁ T-B) ⊗₁ T-C) ∘ α⇐-c2 ∘ id ⊗₁ cBC-from
    ≈⟨ refl⟩∘⟨ α-comm ⟩∘⟨refl ⟩
  (id ⊗₁ F-BC) ∘ (id ⊗₁ (T-B ⊗₁ T-C) ∘ α⇒-d) ∘ α⇐-c2 ∘ id ⊗₁ cBC-from
    ≈⟨ refl⟩∘⟨ FM.assoc ⟩
  (id ⊗₁ F-BC) ∘ id ⊗₁ (T-B ⊗₁ T-C) ∘ α⇒-d ∘ α⇐-c2 ∘ id ⊗₁ cBC-from
    ≈⟨ FM.sym-assoc ⟩
  ((id ⊗₁ F-BC) ∘ id ⊗₁ (T-B ⊗₁ T-C)) ∘ α⇒-d ∘ α⇐-c2 ∘ id ⊗₁ cBC-from
    ≈⟨ ≈-Term-sym ⊗-∘-dist ⟩∘⟨refl ⟩
  ((id ∘ id) ⊗₁ (F-BC ∘ T-B ⊗₁ T-C)) ∘ α⇒-d ∘ α⇐-c2 ∘ id ⊗₁ cBC-from
    ≈⟨ ⊗-resp-≈ idˡ collapse-F-BC ⟩∘⟨refl ⟩
  (id ⊗₁ cBC-to) ∘ α⇒-d ∘ α⇐-c2 ∘ id ⊗₁ cBC-from
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

--------------------------------------------------------------------------------
-- Unit-base case of bridge-α⇒-form (constructive: does not depend on
-- bridge-α⇒-form-⊗-⊗ postulate).

bridge-α⇒-form-unit
  : ∀ B C → bridge (α⇒ {unit} {B} {C})
          ≈Term α⇒-form-list [] (flatten B) (flatten C)
bridge-α⇒-form-unit B C = begin
  bridge (α⇒ {unit} {B} {C})
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
    ≈⟨ _≅_.isoʳ (unflatten-flatten-≈ (B ⊗₀ C)) ⟩
  id ∎
  where
    F-BC = _≅_.from (unflatten-flatten-≈ (B ⊗₀ C))
    T-B  = _≅_.to   (unflatten-flatten-≈ B)
    T-C  = _≅_.to   (unflatten-flatten-≈ C)
    cBC-from = _≅_.from (unflatten-++-≅ (flatten B) (flatten C))

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
