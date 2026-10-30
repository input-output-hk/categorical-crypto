{-# OPTIONS --safe --without-K #-}

open import Categories.APROP

module Categories.APROP.Hypergraph.Solver.Frontend.Drive (sig : APROPSignature) where

open import Categories.APROP.Hypergraph.Model.Iso
open import Categories.APROP.Hypergraph.Model.Translation sig
open import Categories.APROP.Hypergraph.Solver.Frontend.Core sig
open import Categories.APROP.Hypergraph.Solver.Match.FindIso sig
open import Categories.APROP.Hypergraph.Solver.Rewrite.Balance sig
open import Categories.APROP.Hypergraph.Solver.Rewrite.Carve sig
open import Categories.APROP.Hypergraph.Solver.Rewrite.Deep sig
open import Categories.Category.Monoidal.Bundle
open import Categories.FreeMonoidal

open import Data.List.Base
open import Data.Maybe.Base using (Maybe; just; nothing; _<∣>_)
open import Data.Nat.Base
open import Data.Product.Base using (Σ; _,_; proj₁; proj₂)

open APROP sig

private variable A B : ObjTerm

module Drive {o ℓ e} (C : SymmetricMonoidalCategory o ℓ e)
  (let module C = SymmetricMonoidalCategory C)
  (let ⟦v⟧ = fromMC {v = Symm} C.monoidalCategory (λ ⦃ _ ⦄ → C.symmetric))
  (⟦_⟧ᵖ₀ : X → C.Obj)
  (let open FreeObjInterp Symm X ⟦v⟧ ⟦_⟧ᵖ₀ using (⟦_⟧₀))
  (⟦_⟧ᵖ₁ : ∀ {x y} → mor x y → ⟦ x ⟧₀ C.⇒ ⟦ y ⟧₀)
  where

  open Target C ⟦_⟧ᵖ₀ ⟦_⟧ᵖ₁

  -- A dependent with-abstraction would normalize the iso's frame translation
  -- while its context is still abstract. Match a Maybe argument instead;
  -- see frameM for the shared neutral-frame rationale.
  private
    fireWith
      : (s frameL frameR : HomTerm A B)
      → ⟦ frameL ⟧₁ C.≈ ⟦ frameR ⟧₁
      → Maybe (⟪ s ⟫ ≅ᴴ ⟪ frameL ⟫)
      → Maybe (Σ (HomTerm A B) (λ t → ⟦ s ⟧₁ C.≈ ⟦ t ⟧₁))
    fireWith s frameL frameR rule nothing    = nothing
    fireWith s frameL frameR rule (just iso) =
      just (frameR , C.Equiv.trans (solveH s frameL iso) rule)

    tryFoc : (r : Rule) → ∀ {A B} (s : HomTerm A B)
           → Maybe (Foc A B (Rule.P r) (Rule.Q r))
           → Maybe (Σ (HomTerm A B) (λ t → ⟦ s ⟧₁ C.≈ ⟦ t ⟧₁))
    tryFoc r s nothing               = nothing
    tryFoc r s (just (k , pre , post)) =
      fireWith s frameL frameR
        (C.∘-resp-≈ʳ (C.∘-resp-≈ˡ (C.⊗.F-resp-≈ (C.Equiv.refl , Rule.sound r))))
        (withTranslation s (λ H → withTranslation frameL (findIsoᵀ H)))
      where frameL = reassocBal post ∘ (id {k} ⊗₁ Rule.lhs r) ∘ reassocBal pre
            frameR = reassocBal post ∘ (id {k} ⊗₁ Rule.rhs r) ∘ reassocBal pre

  driveStep : List Rule → ∀ {A B} (s : HomTerm A B)
            → Maybe (Σ (HomTerm A B) (λ t → ⟦ s ⟧₁ C.≈ ⟦ t ⟧₁))
  driveStep []       s = nothing
  driveStep (r ∷ rs) s =
    tryFoc r s (deepFocₙ s (Rule.lhs r) zero) <∣> driveStep rs s

  drive : List Rule → ℕ → ∀ {A B} (s : HomTerm A B) → Σ (HomTerm A B) (λ t → ⟦ s ⟧₁ C.≈ ⟦ t ⟧₁)
  drive rs zero       s = s , C.Equiv.refl
  drive rs (suc fuel) s with driveStep rs s
  ... | nothing       = s , C.Equiv.refl
  ... | just (t , pf) =
        proj₁ rec , C.Equiv.trans pf (proj₂ rec)
    where rec = drive rs fuel t
