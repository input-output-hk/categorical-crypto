{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- σ-block algebra: `hexagon₂` (the dual hexagon at the α⇐ level) and
-- `σ-A⊗B-expand` (the expansion of the compound-object braiding
-- `σ {A⊗B} {C}` into atomic crossings framed by associators).
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
-- hexagon₂: the dual hexagon at the α⇐ level (derived from the standard
-- hexagon):
--   σ ⊗ id ∘ α⇐ ∘ id ⊗ σ ≈ α⇐ ∘ σ ∘ α⇐
-- at type X⊗(Y⊗Z) → (Z⊗X)⊗Y.

private
  h₁R∘h₂R≈id
    : ∀ {X Y Z : ObjTerm}
    → (α⇒ {A = X} {B = Y} {C = Z} ∘ σ {A = Z} {B = X ⊗₀ Y}
        ∘ α⇒ {A = Z} {B = X} {C = Y})
      ∘ (α⇐ {A = Z} {B = X} {C = Y} ∘ σ {A = X ⊗₀ Y} {B = Z}
          ∘ α⇐ {A = X} {B = Y} {C = Z})
      ≈Term id
  h₁R∘h₂R≈id {X} {Y} {Z} =
    begin
      (α⇒ ∘ σ ∘ α⇒)
        ∘ (α⇐ ∘ σ ∘ α⇐)
        ≈⟨ assoc ⟩
      α⇒ ∘ ((σ ∘ α⇒) ∘ (α⇐ ∘ σ ∘ α⇐))
        ≈⟨ refl⟩∘⟨ assoc ⟩
      α⇒ ∘ σ ∘ (α⇒ ∘ (α⇐ ∘ σ ∘ α⇐))
        ≈⟨ refl⟩∘⟨ (refl⟩∘⟨ (≈-Term-sym assoc)) ⟩
      α⇒ ∘ σ ∘ ((α⇒ ∘ α⇐) ∘ σ ∘ α⇐)
        ≈⟨ refl⟩∘⟨ (refl⟩∘⟨ (α⇒∘α⇐≈id ⟩∘⟨refl)) ⟩
      α⇒ ∘ σ ∘ (id ∘ σ ∘ α⇐)
        ≈⟨ refl⟩∘⟨ (refl⟩∘⟨ idˡ) ⟩
      α⇒ ∘ σ ∘ (σ ∘ α⇐)
        ≈⟨ refl⟩∘⟨ (≈-Term-sym assoc) ⟩
      α⇒ ∘ (σ ∘ σ) ∘ α⇐
        ≈⟨ refl⟩∘⟨ (σ∘σ≈id ⟩∘⟨refl) ⟩
      α⇒ ∘ id ∘ α⇐
        ≈⟨ refl⟩∘⟨ idˡ ⟩
      α⇒ ∘ α⇐
        ≈⟨ α⇒∘α⇐≈id ⟩
      id
    ∎

  h₂L∘h₁L≈id
    : ∀ {X Y Z : ObjTerm}
    → ((σ {A = X} {B = Z} ⊗₁ id {A = Y}) ∘ α⇐ {A = X} {B = Z} {C = Y}
        ∘ (id {A = X} ⊗₁ σ {A = Y} {B = Z}))
      ∘ ((id {A = X} ⊗₁ σ {A = Z} {B = Y}) ∘ α⇒ {A = X} {B = Z} {C = Y}
          ∘ (σ {A = Z} {B = X} ⊗₁ id {A = Y}))
      ≈Term id
  h₂L∘h₁L≈id {X} {Y} {Z} =
    begin
      ((σ ⊗₁ id) ∘ α⇐ ∘ (id ⊗₁ σ))
        ∘ ((id ⊗₁ σ) ∘ α⇒ ∘ (σ ⊗₁ id))
        ≈⟨ assoc ⟩
      (σ ⊗₁ id) ∘ ((α⇐ ∘ (id ⊗₁ σ))
        ∘ ((id ⊗₁ σ) ∘ α⇒ ∘ (σ ⊗₁ id)))
        ≈⟨ refl⟩∘⟨ assoc ⟩
      (σ ⊗₁ id) ∘ α⇐ ∘ ((id ⊗₁ σ)
        ∘ ((id ⊗₁ σ) ∘ α⇒ ∘ (σ ⊗₁ id)))
        ≈⟨ refl⟩∘⟨ (refl⟩∘⟨ (≈-Term-sym assoc)) ⟩
      (σ ⊗₁ id) ∘ α⇐ ∘ ((id ⊗₁ σ) ∘ (id ⊗₁ σ))
        ∘ α⇒ ∘ (σ ⊗₁ id)
        ≈⟨ refl⟩∘⟨ (refl⟩∘⟨ ((≈-Term-trans (≈-Term-sym ⊗-∘-dist)
                            (≈-Term-trans (⊗-resp-≈ idˡ σ∘σ≈id) id⊗id≈id)) ⟩∘⟨refl)) ⟩
      (σ ⊗₁ id) ∘ α⇐ ∘ id ∘ α⇒ ∘ (σ ⊗₁ id)
        ≈⟨ refl⟩∘⟨ (refl⟩∘⟨ idˡ) ⟩
      (σ ⊗₁ id) ∘ α⇐ ∘ (α⇒ ∘ (σ ⊗₁ id))
        ≈⟨ refl⟩∘⟨ (≈-Term-sym assoc) ⟩
      (σ ⊗₁ id) ∘ (α⇐ ∘ α⇒) ∘ (σ ⊗₁ id)
        ≈⟨ refl⟩∘⟨ (α⇐∘α⇒≈id ⟩∘⟨refl) ⟩
      (σ ⊗₁ id) ∘ id ∘ (σ ⊗₁ id)
        ≈⟨ refl⟩∘⟨ idˡ ⟩
      (σ ⊗₁ id) ∘ (σ ⊗₁ id)
        ≈⟨ ≈-Term-trans (≈-Term-sym ⊗-∘-dist)
             (≈-Term-trans (⊗-resp-≈ σ∘σ≈id idˡ) id⊗id≈id) ⟩
      id
    ∎

hexagon₂
  : ∀ {X Y Z : ObjTerm}
  → (σ {A = X} {B = Z} ⊗₁ id {A = Y}) ∘ α⇐ {A = X} {B = Z} {C = Y}
      ∘ (id {A = X} ⊗₁ σ {A = Y} {B = Z})
    ≈Term α⇐ {A = Z} {B = X} {C = Y} ∘ σ {A = X ⊗₀ Y} {B = Z}
      ∘ α⇐ {A = X} {B = Y} {C = Z}
hexagon₂ {X} {Y} {Z} =
  let h₂L = (σ {A = X} {B = Z} ⊗₁ id {A = Y}) ∘ α⇐ {A = X} {B = Z} {C = Y}
              ∘ (id {A = X} ⊗₁ σ {A = Y} {B = Z})
      h₁L = (id {A = X} ⊗₁ σ {A = Z} {B = Y}) ∘ α⇒ {A = X} {B = Z} {C = Y}
              ∘ (σ {A = Z} {B = X} ⊗₁ id {A = Y})
      h₁R = α⇒ {A = X} {B = Y} {C = Z} ∘ σ {A = Z} {B = X ⊗₀ Y}
              ∘ α⇒ {A = Z} {B = X} {C = Y}
      h₂R = α⇐ {A = Z} {B = X} {C = Y} ∘ σ {A = X ⊗₀ Y} {B = Z}
              ∘ α⇐ {A = X} {B = Y} {C = Z}
  in begin
    h₂L
      ≈⟨ ≈-Term-sym idʳ ⟩
    h₂L ∘ id
      ≈⟨ refl⟩∘⟨ (≈-Term-sym h₁R∘h₂R≈id) ⟩
    h₂L ∘ (h₁R ∘ h₂R)
      ≈⟨ refl⟩∘⟨ ((≈-Term-sym hexagon) ⟩∘⟨refl) ⟩
    h₂L ∘ (h₁L ∘ h₂R)
      ≈⟨ ≈-Term-sym assoc ⟩
    (h₂L ∘ h₁L) ∘ h₂R
      ≈⟨ h₂L∘h₁L≈id ⟩∘⟨refl ⟩
    id ∘ h₂R
      ≈⟨ idˡ ⟩
    h₂R
    ∎

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
