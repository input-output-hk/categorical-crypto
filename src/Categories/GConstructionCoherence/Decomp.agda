{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- Free decompositions of the two coherence sides into the three segments:
--
--   lhs-decomp : lhsᵗ ≈ L₂ᵗ ∘ L₁ᵗ ∘ L₀ᵗ
--   rhs-decomp : rhsᵗ ≈ R₂ᵗ ∘ R₁ᵗ ∘ R₀ᵗ
--
-- Every hop is a one-liner through the splitting front-end:
--   * pure-assoc regroupings go through `solveSplitR?` (reassoc + refl —
--     no solver leaf, near-free);
--   * single-change hops between  H ∘ (D ∘ T)  and  H ∘ (D' ∘ T)
--     (identical H, T; D-units explicitly bracketed) go through
--     `solveSplit?` — the head peels by refl/∘-cuts and the solver runs
--     only on the small (D , D') pair (1–3 boxes, ≤ ~19 morphisms).
--------------------------------------------------------------------------------

-- STATUS (2026-06-10): DESIGN COMPLETE, TYPE-VALIDATED; OBLIGATION EVALUATION
-- EXCEEDS INTERACTIVE COMPUTE.  Terms.agda (all segment interfaces + routing
-- isos) typechecks.  The solver obligations in Wiring0/1/2 are well-typed but
-- each forces a findIsoᵀ evaluation whose per-call cost at this 8-atom
-- signature is dominated by raw-⟪⟫ type-conversion overhead (ob₂, the
-- SMALLEST: >20 min, timed out).  Residual options: (a) batch/overnight
-- compute, (b) hand-prove the three 1-box naturality squares with free
-- combinators (~150-400 LOC, no solver), (c) eliminate the per-call
-- type-conversion overhead.  See docs/smc-solver-performance.md.
module Categories.GConstructionCoherence.Decomp where

open import Data.Maybe.Base using (from-just)

open import Categories.GConstructionCoherence.Terms
open import Categories.APROP.Hypergraph.Solver.Split gSigDec
  using (solveSplit?; solveSplitR?)

private
  _⊕_ = ≈-Term-trans
  infixr 4 _⊕_

-- ===== lhs ==================================================================
private
  lA lB lC : HomTerm _ _
  lA = βᵗ ∘ ((αᵗ ⊗₁ id) ∘ (βᵗ ∘ ((m₀ᵗ ⊗₁ id) ∘ (βᵗ ∘ (((id ⊗₁ f' ∘ γᵗ) ⊗₁ id) ∘ βᵗ)))))
  lB = βᵗ ∘ ((αᵗ ⊗₁ id) ∘ (βᵗ ∘ ((m₀ᵗ ⊗₁ id) ∘ (βᵗ ∘ ((((id ⊗₁ f') ⊗₁ id) ∘ (γᵗ ⊗₁ id)) ∘ βᵗ)))))
  lC = βᵗ ∘ ((αᵗ ⊗₁ id) ∘ (βᵗ ∘ (((αᵗ ⊗₁ id) ∘ (((h' ⊗₁ id) ⊗₁ id) ∘ (((id ⊗₁ g') ⊗₁ id) ∘ (γᵗ ⊗₁ id))))
                              ∘ (βᵗ ∘ ((((id ⊗₁ f') ⊗₁ id) ∘ (γᵗ ⊗₁ id)) ∘ βᵗ)))))

lhs-decomp : lhsᵗ ≈Term (L₂ᵗ ∘ L₁ᵗ ∘ L₀ᵗ)
lhs-decomp =
      from-just (solveSplitR? lhsᵗ lA)             -- pure assoc
  ⊕ from-just (solveSplit?  lA   lB)               -- leaf: expand (id⊗f'∘γ)⊗id
  ⊕ from-just (solveSplit?  lB   lC)               -- leaf: expand+serialize m₀⊗id
  ⊕ from-just (solveSplitR? lC (L₂ᵗ ∘ L₁ᵗ ∘ L₀ᵗ))  -- pure assoc regroup

-- ===== rhs ==================================================================
private
  rA rB rB' rC rC' rD rD' rE rE' rF : HomTerm _ _
  -- pure assoc of rhsᵗ
  rA  = (αᵗ ⊗₁ id) ∘ (α⇐ ∘ ((id ⊗₁ k₀ᵗ) ∘ (α⇒ ∘ (((h' ⊗₁ id ∘ γᵗ) ⊗₁ id)))))
  -- leaf: expand (h'⊗id ∘ γ)⊗id
  rB  = (αᵗ ⊗₁ id) ∘ (α⇐ ∘ ((id ⊗₁ k₀ᵗ) ∘ (α⇒ ∘ ((((h' ⊗₁ id) ⊗₁ id) ∘ (γᵗ ⊗₁ id))))))
  -- assoc: isolate the (α⇒ ∘ h-layer) unit against γᵗ⊗id
  rB' = (αᵗ ⊗₁ id) ∘ (α⇐ ∘ ((id ⊗₁ k₀ᵗ) ∘ ((α⇒ ∘ ((h' ⊗₁ id) ⊗₁ id)) ∘ (γᵗ ⊗₁ id))))
  -- leaf: float h' above α⇒
  rC  = (αᵗ ⊗₁ id) ∘ (α⇐ ∘ ((id ⊗₁ k₀ᵗ) ∘ (((h' ⊗₁ id) ∘ α⇒) ∘ (γᵗ ⊗₁ id))))
  -- assoc: pair (id⊗k₀ ∘ h'⊗id) against (α⇒ ∘ γᵗ⊗id)
  rC' = (αᵗ ⊗₁ id) ∘ (α⇐ ∘ (((id ⊗₁ k₀ᵗ) ∘ (h' ⊗₁ id)) ∘ (α⇒ ∘ (γᵗ ⊗₁ id))))
  -- leaf: interchange h' past id⊗k₀
  rD  = (αᵗ ⊗₁ id) ∘ (α⇐ ∘ (((h' ⊗₁ id) ∘ (id ⊗₁ k₀ᵗ)) ∘ (α⇒ ∘ (γᵗ ⊗₁ id))))
  -- assoc: pair (α⇐ ∘ h'⊗id) against the rest
  rD' = (αᵗ ⊗₁ id) ∘ ((α⇐ ∘ (h' ⊗₁ id)) ∘ ((id ⊗₁ k₀ᵗ) ∘ (α⇒ ∘ (γᵗ ⊗₁ id))))
  -- leaf: float h' above α⇐
  rE  = (αᵗ ⊗₁ id) ∘ ((((h' ⊗₁ id) ⊗₁ id) ∘ α⇐) ∘ ((id ⊗₁ k₀ᵗ) ∘ (α⇒ ∘ (γᵗ ⊗₁ id))))
  -- assoc: re-nest so id⊗k₀ is the isolated unit
  rE' = (αᵗ ⊗₁ id) ∘ (((h' ⊗₁ id) ⊗₁ id) ∘ (α⇐ ∘ ((id ⊗₁ k₀ᵗ) ∘ (α⇒ ∘ (γᵗ ⊗₁ id)))))
  -- leaf: expand id⊗k₀
  rF  = (αᵗ ⊗₁ id) ∘ (((h' ⊗₁ id) ⊗₁ id) ∘ (α⇐ ∘
          (((id ⊗₁ αᵗ) ∘ ((id ⊗₁ (g' ⊗₁ id)) ∘ ((id ⊗₁ (id ⊗₁ f')) ∘ (id ⊗₁ γᵗ))))
           ∘ (α⇒ ∘ (γᵗ ⊗₁ id)))))

rhs-decomp : rhsᵗ ≈Term (R₂ᵗ ∘ R₁ᵗ ∘ R₀ᵗ)
rhs-decomp =
      from-just (solveSplitR? rhsᵗ rA)
  ⊕ from-just (solveSplit?  rA   rB)
  ⊕ from-just (solveSplitR? rB   rB')
  ⊕ from-just (solveSplit?  rB'  rC)
  ⊕ from-just (solveSplitR? rC   rC')
  ⊕ from-just (solveSplit?  rC'  rD)
  ⊕ from-just (solveSplitR? rD   rD')
  ⊕ from-just (solveSplit?  rD'  rE)
  ⊕ from-just (solveSplitR? rE   rE')
  ⊕ from-just (solveSplit?  rE'  rF)
  ⊕ from-just (solveSplitR? rF (R₂ᵗ ∘ R₁ᵗ ∘ R₀ᵗ))
