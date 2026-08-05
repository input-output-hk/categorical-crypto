{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- σ-block algebra: `hexagon₂` (the dual hexagon at the α⇐ level, private
-- staircase step) and `σ-A⊗B-expand` (the expansion of the compound-object
-- braiding `σ {A⊗B} {C}` into atomic crossings framed by associators).
--
-- `σ-A⊗B-expand` is the sole export consumed downstream (by
-- `Strict.Embed`).  Everything here is derived from the FreeMonoidal
-- (symmetric) axioms alone.
--------------------------------------------------------------------------------

open import Categories.FreeMonoidal

-- Stated over an arbitrary `FreeMonoidalData` with a symmetric structure;
-- the body uses only the free (symmetric) monoidal structure.
module Categories.FreeSMC.SigmaBlockHexagon
  (d : FreeMonoidalData) ⦃ s≤v : Symm ≤ FreeMonoidalData.v d ⦄ where

open FreeMonoidal d

open import Categories.Category using (Category)

private
  module FM = Category FreeMonoidal

open FM.HomReasoning

--------------------------------------------------------------------------------
-- hexagon₂: the dual hexagon at the α⇐ level.  `Symmetric` already carries it
-- (derived from `hexagon` + `commutative` by the library's `symmetricHelper`);
-- the two statements differ only by `Commutation`'s bracketing.

open import Categories.Category.Monoidal.Symmetric Monoidal-FreeMonoidal
  using (Symmetric)

private
  module S = Symmetric Symmetric-Monoidal

  hexagon₂
    : ∀ {X Y Z : ObjTerm}
    → (σ {A = X} {B = Z} ⊗₁ id {A = Y}) ∘ α⇐ {A = X} {B = Z} {C = Y}
        ∘ (id {A = X} ⊗₁ σ {A = Y} {B = Z})
      ≈Term α⇐ {A = Z} {B = X} {C = Y} ∘ σ {A = X ⊗₀ Y} {B = Z}
        ∘ α⇐ {A = X} {B = Y} {C = Z}
  hexagon₂ = ≈-Term-sym assoc ○ S.hexagon₂ ○ assoc

--------------------------------------------------------------------------------
-- σ_{A⊗B,C} expansion via hexagon₂ (rearranged):
--   σ_{A⊗B,C} ≈ α⇒_{C,A,B} ∘ (σ_{A,C} ⊗ id_B) ∘ α⇐_{A,C,B}
--                          ∘ (id_A ⊗ σ_{B,C}) ∘ α⇒_{A,B,C}
σ-A⊗B-expand
  : ∀ {A B C : ObjTerm}
  → σ {A = A ⊗₀ B} {B = C}
    ≈Term α⇒ {A = C} {B = A} {C = B}
            ∘ (σ {A = A} {B = C} ⊗₁ id {A = B})
            ∘ α⇐ {A = A} {B = C} {C = B}
            ∘ (id {A = A} ⊗₁ σ {A = B} {B = C})
            ∘ α⇒ {A = A} {B = B} {C = C}
σ-A⊗B-expand {A} {B} {C} =
    begin
      σ
        ≈⟨ ≈-Term-sym idˡ ⟩
      id ∘ σ
        ≈⟨ (≈-Term-sym α⇒∘α⇐≈id) ⟩∘⟨refl ⟩
      (α⇒ ∘ α⇐) ∘ σ
        ≈⟨ assoc ⟩
      α⇒ ∘ (α⇐ ∘ σ)
        ≈⟨ refl⟩∘⟨ (≈-Term-sym idʳ) ⟩
      α⇒ ∘ ((α⇐ ∘ σ) ∘ id)
        ≈⟨ refl⟩∘⟨ (refl⟩∘⟨ (≈-Term-sym α⇐∘α⇒≈id)) ⟩
      α⇒ ∘ ((α⇐ ∘ σ) ∘ (α⇐ ∘ α⇒))
        ≈⟨ refl⟩∘⟨ (≈-Term-trans (≈-Term-sym assoc)
               (assoc ⟩∘⟨refl)) ⟩
      α⇒ ∘ ((α⇐ ∘ (σ ∘ α⇐)) ∘ α⇒)
        ≈⟨ refl⟩∘⟨ ((≈-Term-sym assoc) ⟩∘⟨refl) ⟩
      α⇒ ∘ (((α⇐ ∘ σ) ∘ α⇐) ∘ α⇒)
        -- center α⇐ ∘ σ ∘ α⇐ rewritten by hexagon₂ (sym).
        ≈⟨ refl⟩∘⟨ ((≈-Term-trans assoc (≈-Term-sym hexagon₂)) ⟩∘⟨refl) ⟩
      α⇒ ∘ (((σ ⊗₁ id) ∘ α⇐ ∘ (id ⊗₁ σ)) ∘ α⇒)
        ≈⟨ refl⟩∘⟨ assoc ⟩
      α⇒ ∘ ((σ ⊗₁ id) ∘ ((α⇐ ∘ (id ⊗₁ σ)) ∘ α⇒))
        ≈⟨ refl⟩∘⟨ (refl⟩∘⟨ assoc) ⟩
      α⇒ ∘ ((σ ⊗₁ id) ∘ (α⇐ ∘ ((id ⊗₁ σ) ∘ α⇒)))
        ≈⟨ refl⟩∘⟨ (refl⟩∘⟨ (refl⟩∘⟨ ≈-Term-refl)) ⟩
      α⇒ ∘ (σ ⊗₁ id) ∘ α⇐ ∘ (id ⊗₁ σ) ∘ α⇒
    ∎
