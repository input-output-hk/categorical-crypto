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

-- Call-pattern performance rule (docs/smc-solver-performance.md, "the 8-atom
-- wall"): forcing must be routed through refl-checked equations (`step!`/
-- `stepR!`, from `Terms`), never `from-just`/inferred witnesses (slow path).
-- The companion spelling rule for instantiated signature types now belongs to
-- `Split`, which owns the gate and spells `⟪_⟫`/`soundness` from one
-- `sig`.
module Categories.GConstructionCoherence.Decomp where

open import Relation.Binary.PropositionalEquality using (refl)

open import Categories.GConstructionCoherence.Terms

private
  Dom Cod : ObjTerm
  Dom = ((A⁺ ⊗₀ E⁻) ⊗₀ (D⁻ ⊗₀ D⁺)) ⊗₀ (B⁻ ⊗₀ B⁺)
  Cod = ((A⁻ ⊗₀ E⁺) ⊗₀ (D⁻ ⊗₀ D⁺)) ⊗₀ (B⁻ ⊗₀ B⁺)

  _⊕_ : ∀ {f g h : HomTerm Dom Cod} → f ≈Term g → g ≈Term h → f ≈Term h
  _⊕_ = ≈-Term-trans
  infixr 4 _⊕_

-- ===== lhs ==================================================================
private
  lA lB lC : HomTerm Dom Cod
  lA = βᵗ ∘ ((αᵗ ⊗₁ id) ∘ (βᵗ ∘ ((m₀ᵗ ⊗₁ id) ∘ (βᵗ ∘ (((id ⊗₁ f' ∘ γᵗ) ⊗₁ id) ∘ βᵗ)))))
  lB = βᵗ ∘ ((αᵗ ⊗₁ id) ∘ (βᵗ ∘ ((m₀ᵗ ⊗₁ id) ∘ (βᵗ ∘ ((((id ⊗₁ f') ⊗₁ id) ∘ (γᵗ ⊗₁ id)) ∘ βᵗ)))))
  lC = βᵗ ∘ ((αᵗ ⊗₁ id) ∘ (βᵗ ∘ (((αᵗ ⊗₁ id) ∘ (((h' ⊗₁ id) ⊗₁ id) ∘ (((id ⊗₁ g') ⊗₁ id) ∘ (γᵗ ⊗₁ id))))
                              ∘ (βᵗ ∘ ((((id ⊗₁ f') ⊗₁ id) ∘ (γᵗ ⊗₁ id)) ∘ βᵗ)))))

lhs-decomp : lhsᵗ ≈Term (L₂ᵗ ∘ L₁ᵗ ∘ L₀ᵗ)
lhs-decomp =
      stepR! lhsᵗ lA refl             -- pure assoc
  ⊕ step! lA lB refl               -- leaf: expand (id⊗f'∘γ)⊗id
  ⊕ step! lB lC refl               -- leaf: expand+serialize m₀⊗id
  ⊕ stepR! lC (L₂ᵗ ∘ L₁ᵗ ∘ L₀ᵗ) refl  -- pure assoc regroup

-- ===== rhs ==================================================================
rhs-decomp : rhsᵗ ≈Term (R₂ᵗ ∘ R₁ᵗ ∘ R₀ᵗ)
rhs-decomp = stepR! rhsᵗ (R₂ᵗ ∘ R₁ᵗ ∘ R₀ᵗ) refl
