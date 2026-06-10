{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- The `bridge-∘` / `bridge-⊗` distributivity lemmas: fully constructive,
-- factored out so downstream modules type-check under `--safe` without the
-- rest of `DecodeRoundtrip`.
--------------------------------------------------------------------------------

open import Categories.APROP

module Categories.APROP.Hypergraph.Soundness.BridgeOps (sig : APROPSignature) where

open APROP sig
open import Categories.APROP.Hypergraph.FromAPROP sig using (flatten)
open import Categories.APROP.Hypergraph.Soundness.Unflatten sig
  using (unflatten; unflatten-flatten-≈; unflatten-++-≅)
open import Categories.APROP.Hypergraph.Soundness.DecodeAttempt sig
  using (bridge)

open import Categories.Category using (Category)
open import Categories.Category.Monoidal using (MonoidalCategory)
open import Categories.Morphism FreeMonoidal using (_≅_)
-- Morphism-variable monoidal solver: discharges `bridge-⊗` (pure
-- interchange/reassociation around opaque generators) as one `solveMor!`.
open import Categories.SolverFrontend using (module FinSetup)
open import Data.Product using (_,_)
open import Data.Fin.Patterns using (0F; 1F; 2F; 3F; 4F; 5F; 6F; 7F; 8F; 9F)
import Data.Vec as Vec
open import Data.List using (_++_)

private
  module FM = Category FreeMonoidal

  -- the free monoidal category itself, as the solver's target bundle.
  FMC : MonoidalCategory _ _ _
  FMC = record { U = FreeMonoidal ; monoidal = Monoidal-FreeMonoidal }

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

-- bridge-⊗: bridge distributes over tensor (modulo unflatten-++-≅ coherence).
bridge-⊗
  : ∀ {A B C D} (f : HomTerm A B) (g : HomTerm C D)
  → bridge (f ⊗₁ g)
  ≈Term _≅_.to   (unflatten-++-≅ (flatten B) (flatten D))
       ∘ (bridge f ⊗₁ bridge g)
       ∘ _≅_.from (unflatten-++-≅ (flatten A) (flatten C))
bridge-⊗ {A} {B} {C} {D} f g = solveMor! lhsᵗ rhsᵗ
  where
    -- atoms: 0-3 ↦ A B C D, 4-7 ↦ their unflattens,
    -- 8 ↦ unflatten (fA++fC), 9 ↦ unflatten (fB++fD)
    open FinSetup FMC
      ( A Vec.∷ B Vec.∷ C Vec.∷ D
          Vec.∷ unflatten (flatten A) Vec.∷ unflatten (flatten B)
          Vec.∷ unflatten (flatten C) Vec.∷ unflatten (flatten D)
          Vec.∷ unflatten (flatten A ++ flatten C)
          Vec.∷ unflatten (flatten B ++ flatten D) Vec.∷ Vec.[] )
    v0 = V 0F ; v1 = V 1F ; v2 = V 2F ; v3 = V 3F ; v4 = V 4F
    v5 = V 5F ; v6 = V 6F ; v7 = V 7F ; v8 = V 8F ; v9 = V 9F
    -- generators: f, g, F-B, F-D, T-A, T-C, cBD-to, cAC-from
    open Sig {8} (λ { 0F → v0 , v1
                    ; 1F → v2 , v3
                    ; 2F → v1 , v5
                    ; 3F → v3 , v7
                    ; 4F → v4 , v0
                    ; 5F → v6 , v2
                    ; 6F → v5 ⊗ᵒ v7 , v9
                    ; 7F → v8 , v4 ⊗ᵒ v6 })
    open WithGen (λ { (genS 0F) → f
                    ; (genS 1F) → g
                    ; (genS 2F) → _≅_.from (unflatten-flatten-≈ B)
                    ; (genS 3F) → _≅_.from (unflatten-flatten-≈ D)
                    ; (genS 4F) → _≅_.to   (unflatten-flatten-≈ A)
                    ; (genS 5F) → _≅_.to   (unflatten-flatten-≈ C)
                    ; (genS 6F) → _≅_.to   (unflatten-++-≅ (flatten B) (flatten D))
                    ; (genS 7F) → _≅_.from (unflatten-++-≅ (flatten A) (flatten C)) })
    gf = gen 0F ; gg = gen 1F ; gFB = gen 2F ; gFD = gen 3F
    gTA = gen 4F ; gTC = gen 5F ; gcBD = gen 6F ; gcAC = gen 7F
    lhsᵗ rhsᵗ : S.HomTerm v8 v9
    lhsᵗ = S._∘_ (S._∘_ gcBD (S._⊗₁_ gFB gFD))
                 (S._∘_ (S._⊗₁_ gf gg) (S._∘_ (S._⊗₁_ gTA gTC) gcAC))
    rhsᵗ = S._∘_ gcBD
                 (S._∘_ (S._⊗₁_ (S._∘_ gFB (S._∘_ gf gTA))
                                (S._∘_ gFD (S._∘_ gg gTC)))
                        gcAC)
