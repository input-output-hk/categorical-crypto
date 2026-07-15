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

-- Two call-pattern performance rules (docs/smc-solver-performance.md,
-- "the 8-atom wall"):
--   * forcing must be routed through refl-checked equations (`force!`),
--     never `from-just`/inferred witnesses (slow elaborator path);
--   * instantiated types must be SPELLED as the consuming signature spells
--     them (Translation (APROPSignatureDec.sig gSigDec), not Translation gSig).
module Categories.GConstructionCoherence.Decomp where

open import Data.Bool.Base using (true)
open import Data.Maybe.Base using (Maybe; just; is-just)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Categories.GConstructionCoherence.Terms
open import Categories.APROP.Hypergraph.Solver.Split gSigDec
  using (solveSplit?; solveSplitR?)

private
  Dom Cod : ObjTerm
  Dom = ((A⁺ ⊗₀ E⁻) ⊗₀ (D⁻ ⊗₀ D⁺)) ⊗₀ (B⁻ ⊗₀ B⁺)
  Cod = ((A⁻ ⊗₀ E⁺) ⊗₀ (D⁻ ⊗₀ D⁺)) ⊗₀ (B⁻ ⊗₀ B⁺)

  _⊕_ : ∀ {f g h : HomTerm Dom Cod} → f ≈Term g → g ≈Term h → f ≈Term h
  _⊕_ = ≈-Term-trans
  infixr 4 _⊕_

  -- refl-routed forcing (never from-just: see "the 8-atom wall")
  force! : ∀ {a} {A : Set a} (m : Maybe A) → is-just m ≡ true → A
  force! (just x) _ = x

  step!  : ∀ {A B} (f g : HomTerm A B) → is-just (solveSplit?  f g) ≡ true → f ≈Term g
  step!  f g ok = force! (solveSplit?  f g) ok

  stepR! : ∀ {A B} (f g : HomTerm A B) → is-just (solveSplitR? f g) ≡ true → f ≈Term g
  stepR! f g ok = force! (solveSplitR? f g) ok

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
private
  rA rB rB' rC rC' rD rD' rE rE' rF : HomTerm Dom Cod
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
      stepR! rhsᵗ rA refl
  ⊕ step! rA rB refl
  ⊕ stepR! rB rB' refl
  ⊕ step! rB' rC refl
  ⊕ stepR! rC rC' refl
  ⊕ step! rC' rD refl
  ⊕ stepR! rD rD' refl
  ⊕ step! rD' rE refl
  ⊕ stepR! rE rE' refl
  ⊕ step! rE' rF refl
  ⊕ stepR! rF (R₂ᵗ ∘ R₁ᵗ ∘ R₀ᵗ) refl
