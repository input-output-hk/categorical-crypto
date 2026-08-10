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
module Categories.FreeMonoidal.SigmaBlockHexagon
  (d : FreeMonoidalData) ⦃ s≤v : Symm ≤ FreeMonoidalData.v d ⦄ where

open FreeMonoidal d

open import Categories.Category using (Category)
open import Categories.Morphism.Reasoning FreeMonoidal
  using (cancelˡ; cancelʳ; assoc²εβ)

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
-- Read right-to-left: re-bracket the RHS until `hexagon₂`'s left-hand side is
-- exposed in the middle, rewrite it, then the two associator pairs cancel
-- (`cancelˡ` on the outside, `cancelʳ` on the inside).  The `hexagon₂` step is
-- the only content; everything else is `Morphism.Reasoning` bookkeeping.
σ-A⊗B-expand =
  ⟺ ( (refl⟩∘⟨ assoc²εβ)
    ○ (refl⟩∘⟨ (hexagon₂ ⟩∘⟨refl))
    ○ (refl⟩∘⟨ assoc)
    ○ cancelˡ α⇒∘α⇐≈id
    ○ cancelʳ α⇐∘α⇒≈id )
