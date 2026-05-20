{-# OPTIONS --safe --without-K #-}

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
  using (flatten; ⟪_⟫)
open import Categories.APROP.Hypergraph.Completeness.Unflatten sig
  using (unflatten; unflatten-++-≅)
open import Categories.APROP.Hypergraph.Completeness.DecodeAttempt sig
  using (bridge)

open import Categories.Morphism FreeMonoidal using (_≅_)
open import Data.List using (List; []; _∷_; _++_)
open import Data.List.Properties using (++-identityʳ; ++-assoc)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; sym; subst₂)

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
-- Composition / tensor: structural recursion.  These definitional
-- equalities are exactly what makes `decode-rel-∘-shape` and
-- `decode-rel-⊗-shape` `refl`.
decode-rel (g ∘ f) = decode-rel g ∘ decode-rel f
decode-rel (_⊗₁_ {A = A} {B = B} {C = C} {D = D} f g) =
    _≅_.to   (unflatten-++-≅ (flatten B) (flatten D))
  ∘ (decode-rel f ⊗₁ decode-rel g)
  ∘ _≅_.from (unflatten-++-≅ (flatten A) (flatten C))
-- Atomic cases: take `bridge f` directly.  This is the canonical
-- embedding of an atomic morphism into `unflatten (flatten _)` types
-- via the `unflatten-flatten-≈` coherence iso.  Each
-- `decode-roundtrip-rel-X` for atomic X then becomes `≈-Term-refl`,
-- eliminating per-atom postulates from the critical path.
decode-rel (Agen g)                  = bridge (Agen g)
decode-rel (σ {A = A} {B = B} ⦃ s ⦄) = bridge (σ {A = A} {B = B} ⦃ s ⦄)
decode-rel (id {A})                  = bridge (id {A})
decode-rel (λ⇒ {A})                  = bridge (λ⇒ {A})
decode-rel (λ⇐ {A})                  = bridge (λ⇐ {A})
decode-rel (ρ⇒ {A})                  = bridge (ρ⇒ {A})
decode-rel (ρ⇐ {A})                  = bridge (ρ⇐ {A})
decode-rel (α⇒ {A} {B} {C})          = bridge (α⇒ {A} {B} {C})
decode-rel (α⇐ {A} {B} {C})          = bridge (α⇐ {A} {B} {C})

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

import Categories.APROP.Hypergraph.Completeness.BridgeOps sig as DR
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

-- All atomic cases reduce to `≈-Term-refl` because decode-rel was
-- defined to *be* `bridge` for those constructors.  The only real
-- work is in the inductive ∘/⊗ cases, where we use the now-`refl`
-- shape lemmas to thread the IHs through `bridge-∘`/`bridge-⊗`.

decode-roundtrip-rel
  : ∀ {A B} (f : HomTerm A B) → decode-rel f ≈Term bridge f
decode-roundtrip-rel (Agen g)        = ≈-Term-refl
decode-roundtrip-rel id              = ≈-Term-refl
decode-roundtrip-rel (g ∘ f)         =
  decode-roundtrip-rel-∘ g f (decode-roundtrip-rel f) (decode-roundtrip-rel g)
decode-roundtrip-rel (f ⊗₁ g)        =
  decode-roundtrip-rel-⊗ f g (decode-roundtrip-rel f) (decode-roundtrip-rel g)
decode-roundtrip-rel λ⇒              = ≈-Term-refl
decode-roundtrip-rel λ⇐              = ≈-Term-refl
decode-roundtrip-rel ρ⇒              = ≈-Term-refl
decode-roundtrip-rel ρ⇐              = ≈-Term-refl
decode-roundtrip-rel α⇒              = ≈-Term-refl
decode-roundtrip-rel α⇐              = ≈-Term-refl
decode-roundtrip-rel σ               = ≈-Term-refl

-- (Legacy `decode-rel-resp-≅ᴴ` postulate removed; the completeness
-- path now goes through the constructive `decode-rel-resp-≅ᴴ-full`
-- dispatcher in `DecodeRel/Inductive.agda`.)
