{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- Hypergraph-certified free equations can be interpreted in any target SMC.
--------------------------------------------------------------------------------

open import Categories.APROP using (APROPSignature; module APROP)

module Categories.APROP.Hypergraph.Solver.Frontend.Core (sig : APROPSignature) where

open import Categories.APROP.Hypergraph.Model.Iso using (_≅ᴴ_)
open import Categories.APROP.Hypergraph.Model.Translation sig using (⟪_⟫)
open import Categories.APROP.Hypergraph.Soundness sig using (soundness)
open import Categories.Category.Monoidal.Bundle using (SymmetricMonoidalCategory)
open import Categories.FreeMonoidal
open import Categories.Functor using (Functor)
open import Level using (_⊔_)

open APROP sig

module Target {o ℓ e} (C : SymmetricMonoidalCategory o ℓ e)
  (let module C = SymmetricMonoidalCategory C)
  (let ⟦v⟧ = fromMC {v = Symm} C.monoidalCategory (λ ⦃ _ ⦄ → C.symmetric))
  (⟦_⟧ᵖ₀ : X → C.Obj)
  (let open FreeObjInterp Symm X ⟦v⟧ ⟦_⟧ᵖ₀ using (⟦_⟧₀))
  (⟦_⟧ᵖ₁ : ∀ {x y} → mor x y → ⟦ x ⟧₀ C.⇒ ⟦ y ⟧₀)
  where

  ffd : FreeFunctorData asFreeMonoidalData {o} {ℓ} {e}
  ffd = record { ⟦v⟧ = ⟦v⟧ ; ⟦_⟧ᵖ₀ = ⟦_⟧ᵖ₀ ; ⟦_⟧ᵖ₁ = ⟦_⟧ᵖ₁ }

  open FreeFunctor ffd public using (⟦_⟧₁; freeFunctor)

  -- `⟦ t ⟧₁` is definitionally the corresponding `Tgt`-expression,
  -- meaning that goals can be stated in `C` directly.
  module Tgt = ⟦_⟧ᵥ.Cat ⟦v⟧

  solveH : ∀ {A B} (f g : HomTerm A B) → ⟪ f ⟫ ≅ᴴ ⟪ g ⟫ → ⟦ f ⟧₁ C.≈ ⟦ g ⟧₁
  solveH f g iso = Functor.F-resp-≈ freeFunctor (soundness {f = f} {g = g} iso)

  record Rule : Set (o ⊔ ℓ ⊔ e) where
    constructor mkRule
    field {P Q} : ObjTerm
          lhs rhs : HomTerm P Q
          sound   : ⟦ lhs ⟧₁ C.≈ ⟦ rhs ⟧₁
