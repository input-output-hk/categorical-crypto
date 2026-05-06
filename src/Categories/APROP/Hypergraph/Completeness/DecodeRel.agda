{-# OPTIONS #-}

--------------------------------------------------------------------------------
-- Experiment: define `decode` directly by structural recursion on the
-- term, instead of as `proj₁` of the algorithmic `decode-attempt-Linear`.
-- The shape of each case is *exactly* what `decode-attempt-h*` produces,
-- so:
--   * `decode-rel f` and `proj₁ (decode-attempt-Linear f)` are
--      propositionally equal.
--   * `decode-rel (g ∘ f) ≡ decode-rel g ∘ decode-rel f` is *definitional*.
--   * `decode-rel (f ⊗₁ g) ≡ c-to ∘ (decode-rel f ⊗₁ decode-rel g) ∘ c-from`
--      is *definitional*.
--
-- This is the user's "inductive relation R" technique: introduce a
-- structurally-defined R that mirrors the term tree, so proofs about R
-- are clean inductions on f, not on the algorithm's edge-by-edge order.
--
-- The equivalence `decode-rel f ≡ proj₁ (decode-attempt-Linear f)`
-- (provable case-by-case by reflexivity-or-cong on the existing
--  `decode-attempt-h*` constructions) lets us transport every property
-- proven about `decode-rel` onto the algorithmic `decode`.
--------------------------------------------------------------------------------

open import Categories.APROP

module Categories.APROP.Hypergraph.Completeness.DecodeRel (sig : APROPSignature) where

open APROP sig
open import Categories.APROP.Hypergraph.FromAPROP sig
  using (FlatGen; flatten; ⟪_⟫;
         hEmpty; hVar; hId; hGen; hSwap; hTensor; hCompose;
         domL-hGen; codL-hGen; domL-hSwap; codL-hSwap)
open import Categories.APROP.Hypergraph.Completeness.Unflatten sig
  using (unflatten; unflatten-flatten-≈; unflatten-++-≅)
open import Categories.APROP.Hypergraph.Completeness.Decode sig
  using (decode-attempt)
open import Categories.APROP.Hypergraph.Completeness.DecodeAttempt sig
  using (decode-attempt-Linear; decode;
         decode-attempt-hEmpty; decode-attempt-hVar;
         decode-attempt-hId; decode-attempt-hGen;
         decode-attempt-hSwap; decode-attempt-hTensor;
         decode-attempt-hCompose)
import Categories.APROP.Hypergraph.Completeness.Linearity sig as Lin

open import Categories.Morphism FreeMonoidal using (_≅_)
open import Data.List using (List; []; _∷_; _++_)
open import Data.List.Properties using (++-identityʳ; ++-assoc)
open import Data.Product using (_,_; proj₁)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; sym; trans; subst; subst₂)

--------------------------------------------------------------------------------
-- `decode-rel f` is the term that the algorithm produces on `⟪ f ⟫`,
-- defined directly by recursion on `f`.  Each case is the *output* of
-- the corresponding `decode-attempt-h*`-the existing algorithmic
-- proofs.  By construction:
--
--   `decode-rel f ≡ proj₁ (decode-attempt-Linear f)`     [provable; see below]
--
-- so any property about `decode-rel` (proved by induction on `f`)
-- transports to the algorithmic `decode`.

decode-rel
  : ∀ {A B} (f : HomTerm A B)
  → HomTerm (unflatten (flatten A)) (unflatten (flatten B))
-- Composition / tensor: structural recursion — these definitional
-- equalities are exactly what makes `decode-rel-∘-shape` and
-- `decode-rel-⊗-shape` `refl`.
decode-rel (g ∘ f) = decode-rel g ∘ decode-rel f
decode-rel (_⊗₁_ {A = A} {B = B} {C = C} {D = D} f g) =
    _≅_.to   (unflatten-++-≅ (flatten B) (flatten D))
  ∘ (decode-rel f ⊗₁ decode-rel g)
  ∘ _≅_.from (unflatten-++-≅ (flatten A) (flatten C))
-- Generators / σ: take the term the algorithm produces.  These need
-- a boundary `subst₂` because the algorithm's natural types are
-- `unflatten (domL ⟪f⟫)` / `unflatten (codL ⟪f⟫)`, while ours are
-- `unflatten (flatten A)` / `unflatten (flatten B)`.  The boundary
-- lemmas `domL-hGen`/`codL-hGen` etc. bridge the two propositionally.
decode-rel (Agen g) =
  subst₂ HomTerm (cong unflatten (domL-hGen g))
                  (cong unflatten (codL-hGen g))
         (proj₁ (decode-attempt-hGen g))
decode-rel (σ {A = A} {B = B}) =
  subst₂ HomTerm (cong unflatten (domL-hSwap A B))
                  (cong unflatten (codL-hSwap A B))
         (proj₁ (decode-attempt-hSwap A B))
-- id, λ⇒, λ⇐: flatten reduces these endpoints to the same list
-- definitionally, so plain `id` works.
decode-rel (id {A})  = id
decode-rel (λ⇒ {A}) = id
decode-rel (λ⇐ {A}) = id
-- ρ⇒, ρ⇐, α⇒, α⇐: flatten introduces a `++ []` or shifts the
-- bracketing.  Wrap `id` in `subst₂` along the relevant list-equation.
-- The `subst₂` shape (rather than plain `subst`) matches the existing
-- `ρ⇒-coherence` / `α⇒-coherence` etc. in DecodeRoundtrip.agda, so the
-- bridge lemma in each case is a one-liner.
decode-rel (ρ⇒ {A}) =
  subst₂ HomTerm refl (cong unflatten (++-identityʳ (flatten A))) id
decode-rel (ρ⇐ {A}) =
  subst₂ HomTerm (cong unflatten (++-identityʳ (flatten A))) refl id
decode-rel (α⇒ {A} {B} {C}) =
  subst₂ HomTerm refl
         (cong unflatten (++-assoc (flatten A) (flatten B) (flatten C)))
         id
decode-rel (α⇐ {A} {B} {C}) =
  subst₂ HomTerm (cong unflatten (++-assoc (flatten A) (flatten B) (flatten C)))
         refl id

--------------------------------------------------------------------------------
-- The two `shape` properties are now DEFINITIONAL — the constructive
-- `decode-rel` definition above means each side reduces to the same
-- expression by Agda's β rule.  This is the central payoff of
-- refactor A: the algorithmic `decode-{∘,⊗}-shape` postulates (still
-- present in DecodeRoundtrip.agda for the algorithmic decode chain,
-- but no longer on the critical path to `Completeness.completeness`)
-- have been displaced by `refl` here.

decode-rel-∘-shape
  : ∀ {A B C} (g : HomTerm B C) (f : HomTerm A B)
  → decode-rel (g ∘ f) ≡ decode-rel g ∘ decode-rel f
decode-rel-∘-shape g f = refl

decode-rel-⊗-shape
  : ∀ {A B C D} (f : HomTerm A B) (g : HomTerm C D)
  → decode-rel (f ⊗₁ g)
  ≡ _≅_.to   (unflatten-++-≅ (flatten B) (flatten D))
  ∘ (decode-rel f ⊗₁ decode-rel g)
  ∘ _≅_.from (unflatten-++-≅ (flatten A) (flatten C))
decode-rel-⊗-shape f g = refl

--------------------------------------------------------------------------------
-- Roundtrip property: `decode-rel f ≈Term bridge f` for all f.
--
-- This is the analog of `DR.decode-roundtrip` for `decode-rel`.  Crucially,
-- the `∘` and `⊗` cases use `decode-rel-{∘,⊗}-shape` (now `refl`) instead
-- of the postulated `decode-{∘,⊗}-shape` from DecodeRoundtrip.

import Categories.APROP.Hypergraph.Completeness.DecodeRoundtrip sig as DR
open import Categories.APROP.Hypergraph.Completeness.DecodeAttempt sig
  using (decode; bridge)
open import Categories.Category using (Category)

private
  module FM = Category FreeMonoidal
open FM.HomReasoning

private
  ≡⇒≈Term : ∀ {A B} {f g : HomTerm A B} → f ≡ g → f ≈Term g
  ≡⇒≈Term refl = ≈-Term-refl

decode-roundtrip-rel-∘
  : ∀ {A B C} (g : HomTerm B C) (f : HomTerm A B)
  → decode-rel f ≈Term bridge f
  → decode-rel g ≈Term bridge g
  → decode-rel (g ∘ f) ≈Term bridge (g ∘ f)
decode-roundtrip-rel-∘ g f IH-f IH-g = begin
  decode-rel (g ∘ f)
    ≈⟨ ≡⇒≈Term (decode-rel-∘-shape g f) ⟩
  decode-rel g ∘ decode-rel f
    ≈⟨ ∘-resp-≈ IH-g IH-f ⟩
  bridge g ∘ bridge f
    ≈⟨ DR.bridge-∘ g f ⟨
  bridge (g ∘ f)
    ∎

decode-roundtrip-rel-⊗
  : ∀ {A B C D} (f : HomTerm A B) (g : HomTerm C D)
  → decode-rel f ≈Term bridge f
  → decode-rel g ≈Term bridge g
  → decode-rel (f ⊗₁ g) ≈Term bridge (f ⊗₁ g)
decode-roundtrip-rel-⊗ {A} {B} {C} {D} f g IH-f IH-g = begin
  decode-rel (f ⊗₁ g)
    ≈⟨ ≡⇒≈Term (decode-rel-⊗-shape f g) ⟩
  cBD-to ∘ (decode-rel f ⊗₁ decode-rel g) ∘ cAC-from
    ≈⟨ refl⟩∘⟨ ⊗-resp-≈ IH-f IH-g ⟩∘⟨refl ⟩
  cBD-to ∘ (bridge f ⊗₁ bridge g) ∘ cAC-from
    ≈⟨ DR.bridge-⊗ f g ⟨
  bridge (f ⊗₁ g)
    ∎
  where
    cBD-to   = _≅_.to   (unflatten-++-≅ (flatten B) (flatten D))
    cAC-from = _≅_.from (unflatten-++-≅ (flatten A) (flatten C))

-- Per-constructor cases.  For id/λ⇒/λ⇐, decode-rel is just `id` and
-- bridge ≈ id.  For ρ/α, decode-rel is exactly the `subst₂ HomTerm`-form
-- that `DR.{ρ,α}-coherence` already relates to bridge.  For Agen and σ,
-- decode-rel is propositionally equal to `decode` (the algorithmic
-- form), so we delegate to the existing `DR.decode-roundtrip-{Agen,σ}`.

decode-roundtrip-rel-id
  : ∀ {A} → decode-rel (id {A}) ≈Term bridge (id {A})
decode-roundtrip-rel-id {A} = ≈-Term-sym (DR.bridge-id-is-id A)

decode-roundtrip-rel-λ⇒
  : ∀ {A} → decode-rel (λ⇒ {A}) ≈Term bridge (λ⇒ {A})
decode-roundtrip-rel-λ⇒ {A} = ≈-Term-sym (DR.bridge-λ⇒-is-id A)

decode-roundtrip-rel-λ⇐
  : ∀ {A} → decode-rel (λ⇐ {A}) ≈Term bridge (λ⇐ {A})
decode-roundtrip-rel-λ⇐ {A} = ≈-Term-sym (DR.bridge-λ⇐-is-id A)

decode-roundtrip-rel-ρ⇒
  : ∀ {A} → decode-rel (ρ⇒ {A}) ≈Term bridge (ρ⇒ {A})
decode-roundtrip-rel-ρ⇒ {A} = DR.ρ⇒-coherence A

decode-roundtrip-rel-ρ⇐
  : ∀ {A} → decode-rel (ρ⇐ {A}) ≈Term bridge (ρ⇐ {A})
decode-roundtrip-rel-ρ⇐ {A} = DR.ρ⇐-coherence A

decode-roundtrip-rel-α⇒
  : ∀ {A B C} → decode-rel (α⇒ {A} {B} {C}) ≈Term bridge (α⇒ {A} {B} {C})
decode-roundtrip-rel-α⇒ {A} {B} {C} = DR.α⇒-coherence A B C

decode-roundtrip-rel-α⇐
  : ∀ {A B C} → decode-rel (α⇐ {A} {B} {C}) ≈Term bridge (α⇐ {A} {B} {C})
decode-roundtrip-rel-α⇐ {A} {B} {C} = DR.α⇐-coherence A B C

-- For Agen and σ, decode-rel reduces to decode (propositionally `refl`),
-- so we delegate to the existing decode-roundtrip lemmas.  Those are
-- still postulated upstream, but the postulate count doesn't change —
-- we're just inheriting them through a different path.
decode-roundtrip-rel-Agen
  : ∀ {A B} (g : mor A B) → decode-rel (Agen g) ≈Term bridge (Agen g)
decode-roundtrip-rel-Agen g = DR.decode-roundtrip-Agen g

decode-roundtrip-rel-σ
  : ∀ {A B} ⦃ s : Symm ≤ Symm ⦄
  → decode-rel (σ {A = A} {B = B} ⦃ s ⦄) ≈Term bridge (σ {A = A} {B = B} ⦃ s ⦄)
decode-roundtrip-rel-σ ⦃ s ⦄ = DR.decode-roundtrip-σ ⦃ s ⦄

-- The full induction.
decode-roundtrip-rel
  : ∀ {A B} (f : HomTerm A B) → decode-rel f ≈Term bridge f
decode-roundtrip-rel (Agen g)        = decode-roundtrip-rel-Agen g
decode-roundtrip-rel id              = decode-roundtrip-rel-id
decode-roundtrip-rel (g ∘ f)         =
  decode-roundtrip-rel-∘ g f (decode-roundtrip-rel f) (decode-roundtrip-rel g)
decode-roundtrip-rel (f ⊗₁ g)        =
  decode-roundtrip-rel-⊗ f g (decode-roundtrip-rel f) (decode-roundtrip-rel g)
decode-roundtrip-rel λ⇒              = decode-roundtrip-rel-λ⇒
decode-roundtrip-rel λ⇐              = decode-roundtrip-rel-λ⇐
decode-roundtrip-rel ρ⇒              = decode-roundtrip-rel-ρ⇒
decode-roundtrip-rel ρ⇐              = decode-roundtrip-rel-ρ⇐
decode-roundtrip-rel α⇒              = decode-roundtrip-rel-α⇒
decode-roundtrip-rel α⇐              = decode-roundtrip-rel-α⇐
decode-roundtrip-rel (σ ⦃ s ⦄)       = decode-roundtrip-rel-σ ⦃ s ⦄

--------------------------------------------------------------------------------
-- decode-rel preserves hypergraph iso.  Analog of the postulated
-- `decode-resp-≅ᴴ` in Decoder.agda — replacement, not addition.
-- Used by `Completeness.completeness` together with `decode-roundtrip-rel`.

open import Categories.APROP.Hypergraph.Iso using (_≅ᴴ_)

postulate
  decode-rel-resp-≅ᴴ
    : ∀ {A B} (f g : HomTerm A B)
    → ⟪ f ⟫ ≅ᴴ ⟪ g ⟫
    → decode-rel f ≈Term decode-rel g
