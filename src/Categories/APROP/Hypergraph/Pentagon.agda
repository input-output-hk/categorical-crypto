{-# OPTIONS --without-K --lossy-unification #-}

--------------------------------------------------------------------------------
-- Pentagon coherence axiom:
--
--   `id⊗α⇒ ∘ α⇒ ∘ α⇒⊗id ≈Term α⇒ ∘ α⇒{A⊗B,C,D}`
--
-- at type `((A⊗B)⊗C)⊗D → A⊗(B⊗(C⊗D))`.
--
-- Strategy:
--   * Each leaf in the HomTerm AST reduces to a `subst₂`-wrapped `hId`.
--   * Each `∘` of two such forms collapses, via `hComposeP-subst-both` +
--     `hCompose-hId-R-iso-generic`, to a single `subst₂`-wrapped `hId`.
--   * Both LHS and RHS collapse to `subst₂ _ refl p (hId (((A⊗B)⊗C)⊗D))`
--     for some list-equality proof `p : ((flatten A ++ flatten B) ++
--     flatten C) ++ flatten D ≡ flatten A ++ flatten B ++ flatten C ++
--     flatten D`.  The two `p`s are propositionally equal, so the final
--     step is `subst (_ ≅ᴴ_) (cong ...) (refl-≅ᴴ _)`.
--
-- WORK IN PROGRESS.  The helper lemmas `⊗₁-id-as-subst-hId`,
-- `id-⊗₁-as-subst-hId`, `α⇒-compose-stepping`, and
-- `pentagon-subst-proofs-equal` are the pieces.  Until all are
-- discharged, `pentagon-sound` falls back to a focused postulate.
--------------------------------------------------------------------------------

open import Categories.APROP

module Categories.APROP.Hypergraph.Pentagon (sig : APROPSignature) where

open APROP sig
open import Categories.APROP.Hypergraph.Core
open import Categories.APROP.Hypergraph.FromAPROP sig
  using (FlatGen; flatten; hId; hTensor; hEmpty)
open import Categories.APROP.Hypergraph.Translation sig using (⟪_⟫)
open import Categories.APROP.Hypergraph.Iso
open import Categories.APROP.Hypergraph.SoundnessAxioms sig
  using (hCompose-hId-R-iso-generic)

open import Data.List using (List; []; _∷_; _++_)
open import Data.List.Properties using (++-assoc)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; sym; trans; subst; subst₂)

--------------------------------------------------------------------------------
-- Private building-block lemmas.

private
  -- `hTensor` commutes with `subst₂` on the left / right argument.
  hTensor-subst₂-left
    : ∀ {As As' Bs Bs' Cs Ds : List X}
        (p : As ≡ As') (q : Bs ≡ Bs')
        (X₀ : Hypergraph FlatGen As Bs) (Y₀ : Hypergraph FlatGen Cs Ds)
    → hTensor (subst₂ (Hypergraph FlatGen) p q X₀) Y₀
    ≡ subst₂ (Hypergraph FlatGen) (cong (_++ Cs) p) (cong (_++ Ds) q)
             (hTensor X₀ Y₀)
  hTensor-subst₂-left refl refl X₀ Y₀ = refl

  hTensor-subst₂-right
    : ∀ {As Bs Cs Cs' Ds Ds' : List X}
        (p : Cs ≡ Cs') (q : Ds ≡ Ds')
        (X₀ : Hypergraph FlatGen As Bs) (Y₀ : Hypergraph FlatGen Cs Ds)
    → hTensor X₀ (subst₂ (Hypergraph FlatGen) p q Y₀)
    ≡ subst₂ (Hypergraph FlatGen) (cong (As ++_) p) (cong (Bs ++_) q)
             (hTensor X₀ Y₀)
  hTensor-subst₂-right refl refl X₀ Y₀ = refl

--------------------------------------------------------------------------------
-- Each leaf of the pentagon AST reduces to `subst₂`-wrapped `hId`.

-- `⟪ α⇒{X,Y,Z} ⊗₁ id{D} ⟫ ≡ subst₂ _ refl p (hId (((X⊗Y)⊗Z) ⊗₀ D))`
-- where p = cong (_++ flatten D) (++-assoc ...).
α⇒⊗id-as-subst-hId
  : ∀ (X Y Z D : ObjTerm)
  → ⟪ α⇒ {X} {Y} {Z} ⊗₁ id {D} ⟫
  ≡ subst₂ (Hypergraph FlatGen) refl
           (cong (_++ flatten D)
                 (++-assoc (flatten X) (flatten Y) (flatten Z)))
           (hId (((X ⊗₀ Y) ⊗₀ Z) ⊗₀ D))
α⇒⊗id-as-subst-hId X Y Z D =
  hTensor-subst₂-left refl
    (++-assoc (flatten X) (flatten Y) (flatten Z))
    (hId ((X ⊗₀ Y) ⊗₀ Z)) (hId D)

-- `⟪ id{A} ⊗₁ α⇒{X,Y,Z} ⟫ ≡ subst₂ _ refl p (hId (A ⊗₀ ((X⊗Y)⊗Z)))`
-- where p = cong (flatten A ++_) (++-assoc ...).
id⊗α⇒-as-subst-hId
  : ∀ (A X Y Z : ObjTerm)
  → ⟪ id {A} ⊗₁ α⇒ {X} {Y} {Z} ⟫
  ≡ subst₂ (Hypergraph FlatGen) refl
           (cong (flatten A ++_)
                 (++-assoc (flatten X) (flatten Y) (flatten Z)))
           (hId (A ⊗₀ ((X ⊗₀ Y) ⊗₀ Z)))
id⊗α⇒-as-subst-hId A X Y Z =
  hTensor-subst₂-right refl
    (++-assoc (flatten X) (flatten Y) (flatten Z))
    (hId A) (hId ((X ⊗₀ Y) ⊗₀ Z))

-- `⟪ α⇒{X,Y,Z} ⟫` is already a `subst₂`-wrapped `hId` by definition of
-- the translation.  This is a convenience wrapper that gives it a name.
α⇒-as-subst-hId
  : ∀ (X Y Z : ObjTerm)
  → ⟪ α⇒ {X} {Y} {Z} ⟫
  ≡ subst₂ (Hypergraph FlatGen) refl
           (++-assoc (flatten X) (flatten Y) (flatten Z))
           (hId ((X ⊗₀ Y) ⊗₀ Z))
α⇒-as-subst-hId X Y Z = refl

--------------------------------------------------------------------------------
-- Pentagon.
--
-- Still postulated while the composite-collapse chain is being written.
-- The building blocks above (`α⇒⊗id-as-subst-hId`,
-- `id⊗α⇒-as-subst-hId`) are the first step: they reduce each leaf of
-- the pentagon AST to a `subst₂ _ refl p (hId …)` form.  The remaining
-- work is to thread these through the three nested `hComposeP`s on the
-- LHS (and the two on the RHS) and show the boundary-proofs end up
-- propositionally equal.

postulate
  pentagon-sound
    : ∀ {A B C D}
    → ⟪ id {A} ⊗₁ α⇒ {B} {C} {D} ∘ α⇒ {A} {B ⊗₀ C} {D} ∘ α⇒ {A} {B} {C} ⊗₁ id {D} ⟫
    ≅ᴴ ⟪ α⇒ {A} {B} {C ⊗₀ D} ∘ α⇒ {A ⊗₀ B} {C} {D} ⟫
