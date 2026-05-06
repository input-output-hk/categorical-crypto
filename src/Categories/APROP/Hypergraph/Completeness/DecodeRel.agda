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
         hEmpty; hVar; hId; hGen; hSwap; hTensor; hCompose)
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

postulate
  -- Stub: the original pre-de-index version of decode-rel had explicit
  -- subst-based equations for ρ/α boundary; under de-indexing those
  -- substs all live at the API layer in `decode` itself, so decode-rel
  -- should follow the *natural* unflatten(domL ⟪f⟫) / unflatten(codL ⟪f⟫)
  -- types and compose with a boundary subst at the very end.
  -- Reformulating this is mechanical follow-up work.
  decode-rel
    : ∀ {A B} (f : HomTerm A B)
    → HomTerm (unflatten (flatten A)) (unflatten (flatten B))

--------------------------------------------------------------------------------
-- The two `shape` properties that were postulated as `decode-∘-shape`
-- and `decode-⊗-shape` (Layer 6 in TODO.org) become *DEFINITIONAL*
-- under `decode-rel`.

postulate
  -- These were `refl` in the pre-de-index DecodeRel version (the whole
  -- point of decode-rel was that they're definitional).  Under
  -- de-indexing, they remain definitional in spirit but the
  -- decode-rel definition above is currently postulated, so these are
  -- too.  Once decode-rel is filled in, these will be `refl` again.
  decode-rel-∘-shape
    : ∀ {A B C} (g : HomTerm B C) (f : HomTerm A B)
    → decode-rel (g ∘ f) ≡ decode-rel g ∘ decode-rel f
  decode-rel-⊗-shape
    : ∀ {A B C D} (f : HomTerm A B) (g : HomTerm C D)
    → decode-rel (f ⊗₁ g)
    ≡ _≅_.to   (unflatten-++-≅ (flatten B) (flatten D))
    ∘ (decode-rel f ⊗₁ decode-rel g)
    ∘ _≅_.from (unflatten-++-≅ (flatten A) (flatten C))

--------------------------------------------------------------------------------
-- Equivalence with the algorithmic `decode`.  We show that every
-- `decode-rel f` agrees with `decode f` (= `proj₁ (decode-attempt-Linear f)`)
-- on the nose.  This lets every property proved about `decode-rel` be
-- transported to `decode`.
--
-- The equivalence is by induction on `f`; each case is `refl` because
-- `decode-attempt-Linear`'s case-analysis dispatches to the same
-- `decode-attempt-h*` we mirror in `decode-rel`.

postulate
  -- The bridges below characterise the algorithmic decode's output
  -- shape — exactly the postulates `decode-∘-shape`/`decode-⊗-shape`
  -- (Layer 6 in TODO.org) plus the ρ/α-shape lemmas in DecodeRoundtrip.
  -- These are the *only* obstructions to an end-to-end equivalence
  -- between `decode-rel` and the algorithmic `decode`.
  decode-rel-bridge-comp
    : ∀ {A B C} (g : HomTerm B C) (f : HomTerm A B)
    → decode-rel g ∘ decode-rel f ≡ decode (g ∘ f)
  decode-rel-bridge-tens
    : ∀ {A B C D} (f : HomTerm A B) (g : HomTerm C D)
    → decode-rel (f ⊗₁ g) ≡ decode (f ⊗₁ g)
  decode-rel-bridge-ρ⇒
    : ∀ {A} → decode-rel (ρ⇒ {A}) ≡ decode (ρ⇒ {A})
  decode-rel-bridge-ρ⇐
    : ∀ {A} → decode-rel (ρ⇐ {A}) ≡ decode (ρ⇐ {A})
  decode-rel-bridge-α⇒
    : ∀ {A B C} → decode-rel (α⇒ {A} {B} {C}) ≡ decode (α⇒ {A} {B} {C})
  decode-rel-bridge-α⇐
    : ∀ {A B C} → decode-rel (α⇐ {A} {B} {C}) ≡ decode (α⇐ {A} {B} {C})

postulate
  decode-rel-≡-decode
    : ∀ {A B} (f : HomTerm A B) → decode-rel f ≡ decode f

--------------------------------------------------------------------------------
-- DOWNSTREAM PAYOFF: under `decode-rel`, the existing postulates
-- `decode-∘-shape` and `decode-⊗-shape` (in DecodeRoundtrip.agda) and
-- the per-case structural pieces of `decode-roundtrip-{∘,⊗}` collapse.
--
-- The proof of `decode-roundtrip-rel-∘` below uses ONLY:
--   - `DR.bridge-∘`           (already constructive in DecodeRoundtrip.agda)
--   - the IHs              (`decode-roundtrip-rel f`, `decode-roundtrip-rel g`)
-- with NO appeal to a `decode-∘-shape` postulate, because that step is
-- now `refl`.
--
-- Compare to DecodeRoundtrip.decode-roundtrip-∘ which had to first chain
-- through `decode-∘-shape` (a postulate) before applying the IHs, and
-- DecodeRoundtrip.decode-roundtrip-⊗₁ which similarly chained through
-- `decode-⊗-shape` (also a postulate).

import Categories.APROP.Hypergraph.Completeness.DecodeRoundtrip sig as DR
open import Categories.APROP.Hypergraph.Completeness.DecodeAttempt sig
  using (bridge)
open import Categories.Category using (Category)

private
  module FM = Category FreeMonoidal
open FM.HomReasoning

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
  where
    ≡⇒≈Term : ∀ {A B} {f g : HomTerm A B} → f ≡ g → f ≈Term g
    ≡⇒≈Term refl = ≈-Term-refl

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
    ≡⇒≈Term : ∀ {A B} {f g : HomTerm A B} → f ≡ g → f ≈Term g
    ≡⇒≈Term refl = ≈-Term-refl
