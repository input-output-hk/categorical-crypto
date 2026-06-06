{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- The `bridge-∘` / `bridge-⊗` / `bridge-⊗-decompose` distributivity
-- lemmas: fully constructive, factored out so downstream modules
-- type-check under `--safe` without the rest of `DecodeRoundtrip`.
--------------------------------------------------------------------------------

open import Categories.APROP

module Categories.APROP.Hypergraph.Completeness.BridgeOps (sig : APROPSignature) where

open APROP sig
open import Categories.APROP.Hypergraph.FromAPROP sig using (flatten)
open import Categories.APROP.Hypergraph.Completeness.Unflatten sig
  using (unflatten-flatten-≈; unflatten-++-≅)
open import Categories.APROP.Hypergraph.Completeness.DecodeAttempt sig
  using (bridge)

open import Categories.Category using (Category)
open import Categories.Morphism FreeMonoidal using (_≅_)

private
  module FM = Category FreeMonoidal

open FM.HomReasoning

--------------------------------------------------------------------------------
-- bridge-∘: bridge distributes over composition (modulo iso cancellation).
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

-- Distribute ⊗ over the `(≅.from ∘ _ ∘ ≅.to)` composition defining `bridge`.
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

-- bridge-⊗: bridge distributes over tensor (modulo unflatten-++-≅ coherence).
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
