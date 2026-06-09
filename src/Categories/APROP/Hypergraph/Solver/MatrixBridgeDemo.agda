{-# OPTIONS --without-K #-}

--------------------------------------------------------------------------------
-- FEASIBILITY SPIKE — end-to-end DEMONSTRATION.
--
-- Reuses the `Solver.Tests` signature (atoms `Fin 3`; generators
-- `f : a₀→a₁`, `g : a₁→a₂`, `h : a₂→a₀`) and pushes two concrete
-- *isomorphic* hypergraphs through the matrix bridge:
--
--     ⟪ LHS ⟫ , ⟪ RHS ⟫
--       │ hg→mat
--       ▼
--     BlockMatrix Bool , BlockMatrix Bool
--       │ align    (canonical read of the matrix alignment)
--       ▼
--     Alignment (φ , ψ)
--       │ matIso→hgIso
--       ▼
--     ⟪ LHS ⟫ ≅ᴴ ⟪ RHS ⟫
--       │ soundness-full-wired
--       ▼
--     LHS ≈Term RHS              (a genuine free-SMC equation)
--
-- The example is σ-naturality:  σ ∘ (f ⊗ g)  vs  (g ⊗ f) ∘ σ.
--------------------------------------------------------------------------------

module Categories.APROP.Hypergraph.Solver.MatrixBridgeDemo where

open import Data.Fin using (Fin; zero; suc)
open import Data.Nat using (ℕ)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Categories.APROP using (module APROP)
open import Categories.FreeMonoidal

-- Reuse the concrete signature + generators from the existing test suite.
open import Categories.APROP.Hypergraph.Solver.Tests
  using (mySig; mySigDec)

open APROP mySig
open import Categories.APROP.Hypergraph.Core using (Hypergraph)
open import Categories.APROP.Hypergraph.FromAPROP mySig using (FlatGen)
open import Categories.APROP.Hypergraph.Iso using (_≅ᴴ_)
open import Categories.APROP.Hypergraph.Translation mySig using (⟪_⟫)
open import Categories.APROP.Hypergraph.SoundnessFullWired mySigDec
  using (soundness-full-wired)
open import Categories.APROP.Hypergraph.Solver.MatrixBridge mySigDec
  using (hg→mat; align; matIso→hgIso; Alignment)

-- `ObjTerm`, `Var`, `unit`, `_⊗₀_`, `HomTerm`, `Agen`, `σ`, `_∘_`, `_⊗₁_`,
-- `≈Term` are all in scope via `open APROP mySig` above.

private
  a₀ a₁ : ObjTerm
  a₀ = Var zero
  a₁ = Var (suc zero)
  a₂ : ObjTerm
  a₂ = Var (suc (suc zero))

-- Pull the three generators back in (Tests keeps `MyMor` private at the
-- value level, but the constructors are re-derivable via the signature's
-- `mor`; re-import them directly from Tests).
open import Categories.APROP.Hypergraph.Solver.Tests using (MyMor)
open MyMor

--------------------------------------------------------------------------------
-- The two sides of σ-naturality.

LHS RHS : HomTerm (a₀ ⊗₀ a₁) (a₂ ⊗₀ a₁)
LHS = σ {a₁} {a₂} ∘ (Agen f ⊗₁ Agen g)        -- f:a₀→a₁, g:a₁→a₂ ; σ swaps a₁,a₂
RHS = (Agen g ⊗₁ Agen f) ∘ σ {a₀} {a₁}        -- g:a₁→a₂, f:a₀→a₁

H J : Hypergraph FlatGen
H = ⟪ LHS ⟫
J = ⟪ RHS ⟫

--------------------------------------------------------------------------------
-- Step 1 — encode both hypergraphs as matrices.  These genuinely compute.

matH = hg→mat H
matJ = hg→mat J

--------------------------------------------------------------------------------
-- Step 2 — the vertex/edge counts agree (checked by `refl`), so the
-- canonical matrix alignment is well-defined.  THIS is the index
-- reconciliation made concrete: both pruned translations land on the same
-- `nV`/`nE`, so the matrices share a layout and `align` reads off a
-- count-coercion bijection.

nV-eq : Hypergraph.nV H ≡ Hypergraph.nV J
nV-eq = refl

nE-eq : Hypergraph.nE H ≡ Hypergraph.nE J
nE-eq = refl

theAlignment : Alignment H J
theAlignment = align H J matH matJ nV-eq nE-eq

--------------------------------------------------------------------------------
-- Step 3 — assemble the hypergraph isomorphism from the alignment.

theIso : ⟪ LHS ⟫ ≅ᴴ ⟪ RHS ⟫
theIso = matIso→hgIso theAlignment

--------------------------------------------------------------------------------
-- Step 4 — feed it through soundness to obtain a genuine `≈Term`.

σ-naturality : LHS ≈Term RHS
σ-naturality = soundness-full-wired theIso
