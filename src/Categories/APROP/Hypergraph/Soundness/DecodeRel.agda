{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- `decode-rel` defines `decode` directly by structural recursion on the
-- term (rather than as `proj₁` of the algorithmic `decode-attempt-Linear`).
-- Each case mirrors the `decode-attempt-h*` output, so the `∘`/`⊗` shape
-- equalities become DEFINITIONAL and proofs about `decode-rel` are clean
-- inductions on `f`.  `decode-rel f ≡ proj₁ (decode-attempt-Linear f)` is
-- provable case-by-case, transporting properties onto the algorithmic decode.
--------------------------------------------------------------------------------

open import Categories.APROP

module Categories.APROP.Hypergraph.Soundness.DecodeRel (sig : APROPSignature) where

open APROP sig
open import Categories.APROP.Hypergraph.FromAPROP sig
  using (flatten; ⟪_⟫)
open import Categories.APROP.Hypergraph.Soundness.Unflatten sig
  using (unflatten; unflatten-++-≅)
open import Categories.APROP.Hypergraph.Soundness.DecodeAttempt sig
  using (bridge)

open import Categories.Morphism FreeMonoidal using (_≅_)
open import Data.List using (List; []; _∷_; _++_)
open import Data.List.Properties using (++-identityʳ; ++-assoc)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; sym; subst₂)

decode-rel
  : ∀ {A B} (f : HomTerm A B)
  → HomTerm (unflatten (flatten A)) (unflatten (flatten B))
-- Composition / tensor: structural recursion (makes the shape lemmas `refl`).
decode-rel (g ∘ f) = decode-rel g ∘ decode-rel f
decode-rel (_⊗₁_ {A = A} {B = B} {C = C} {D = D} f g) =
    _≅_.to   (unflatten-++-≅ (flatten B) (flatten D))
  ∘ (decode-rel f ⊗₁ decode-rel g)
  ∘ _≅_.from (unflatten-++-≅ (flatten A) (flatten C))
-- Atomic cases: `bridge f` directly (the canonical embedding via the
-- `unflatten-flatten-≈` iso), so each atomic roundtrip is `≈-Term-refl`.
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
-- The two `shape` properties are DEFINITIONAL: each side β-reduces to the
-- same expression, so both proofs are `refl`.

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
-- Roundtrip property: `decode-rel f ≈Term bridge f` for all f.  The `∘`/`⊗`
-- cases use the now-`refl` `decode-rel-{∘,⊗}-shape`.

import Categories.APROP.Hypergraph.Soundness.BridgeOps sig as DR
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

-- Atomic cases are `≈-Term-refl` (decode-rel *is* `bridge` there); the ∘/⊗
-- cases thread the IHs through `bridge-∘`/`bridge-⊗`.

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
