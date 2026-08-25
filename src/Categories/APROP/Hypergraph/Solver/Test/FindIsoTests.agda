{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- Smoke tests for `findIso`, threaded through `soundness`.
-- Each test has the form
--
--   test : f ≈Term g
--   test = solve!
--
-- where `solve!`'s implicit `T (is-just (findIso ⟪ f ⟫ ⟪ g ⟫))` obligation is
-- discharged by `⊤`'s eta exactly when `findIso` reduces to `just _` at
-- type-check time — so a green file still means the search RAN — and the found
-- iso is routed through the strict `soundness` pipeline to a syntactic `≈Term`
-- equation.  `f` and `g` are read back from the goal (`_≈Term_` is indexed by
-- them), so each test states its equation ONCE.  `⟪_⟫` is the *pruned*
-- translation, under which the equation-shaped sides have matching vertex
-- counts so `findIso` succeeds.
--------------------------------------------------------------------------------

module Categories.APROP.Hypergraph.Solver.Test.FindIsoTests where

open import Data.Bool.Base using (T)
open import Data.Maybe using (is-just; to-witness-T)

open import Categories.APROP using (module APROP)
open import Categories.APROP.Hypergraph.Solver.Test.ThreeGens
  using (a₀; a₁; a₂; f; g; h; mySig; mySigDec)

--------------------------------------------------------------------------------
-- Bring in the term language, the solver, and the soundness theorem.

open import Categories.APROP.Hypergraph.Model.Translation mySig using (⟪_⟫)
open import Categories.APROP.Hypergraph.Solver.Match.FindIso mySigDec using (findIso)
open APROP mySig

--------------------------------------------------------------------------------
-- The soundness theorem (axiom-free), giving closed `--safe` test theorems.

open import Categories.APROP.Hypergraph.Soundness mySigDec using (soundness)

-- The gate the tests below go through.  (`GConstructionCoherence.Wiring.solve!`
-- is the same door with an explicit `is-just … ≡ true` argument.)
-- (`lhs`/`rhs`, not `f`/`g`: the fixture's generators are already called
-- `f`/`g`/`h`, so those names cannot be pattern variables here.)
solve! : ∀ {A B} {lhs rhs : HomTerm A B}
       → {_ : T (is-just (findIso ⟪ lhs ⟫ ⟪ rhs ⟫))} → lhs ≈Term rhs
solve! {lhs = l} {r} {pf} = soundness {f = l} {g = r} (to-witness-T (findIso ⟪ l ⟫ ⟪ r ⟫) pf)

--------------------------------------------------------------------------------
-- Tests for each equation-shaped `_≈Term_` constructor.

test-idˡ : id ∘ Agen f ≈Term Agen f
test-idˡ = solve!

test-idʳ : Agen f ∘ id ≈Term Agen f
test-idʳ = solve!

test-assoc : (Agen h ∘ Agen g) ∘ Agen f ≈Term Agen h ∘ (Agen g ∘ Agen f)
test-assoc = solve!

test-≈-refl : Agen f ≈Term Agen f
test-≈-refl = solve!

test-id⊗id : id {a₀} ⊗₁ id {a₁} ≈Term id {a₀ ⊗₀ a₁}
test-id⊗id = solve!

test-⊗-∘-dist
  : (Agen g ∘ Agen f) ⊗₁ (Agen f ∘ Agen h)
  ≈Term Agen g ⊗₁ Agen f ∘ Agen f ⊗₁ Agen h
test-⊗-∘-dist = solve!

test-λ⇐∘λ⇒ : λ⇐ ∘ λ⇒ {a₀} ≈Term id {unit ⊗₀ a₀}
test-λ⇐∘λ⇒ = solve!

test-λ⇒∘λ⇐ : λ⇒ ∘ λ⇐ {a₀} ≈Term id {a₀}
test-λ⇒∘λ⇐ = solve!

test-ρ⇐∘ρ⇒ : ρ⇐ ∘ ρ⇒ {a₀} ≈Term id {a₀ ⊗₀ unit}
test-ρ⇐∘ρ⇒ = solve!

test-ρ⇒∘ρ⇐ : ρ⇒ ∘ ρ⇐ {a₀} ≈Term id {a₀}
test-ρ⇒∘ρ⇐ = solve!

test-α⇐∘α⇒ : α⇐ ∘ α⇒ {a₀} {a₁} {a₂} ≈Term id {(a₀ ⊗₀ a₁) ⊗₀ a₂}
test-α⇐∘α⇒ = solve!

test-α⇒∘α⇐ : α⇒ ∘ α⇐ {a₀} {a₁} {a₂} ≈Term id {a₀ ⊗₀ (a₁ ⊗₀ a₂)}
test-α⇒∘α⇐ = solve!

test-λ⇒∘id⊗f : λ⇒ ∘ (id {unit} ⊗₁ Agen f) ≈Term Agen f ∘ λ⇒
test-λ⇒∘id⊗f = solve!

test-ρ⇒∘f⊗id : ρ⇒ ∘ (Agen f ⊗₁ id {unit}) ≈Term Agen f ∘ ρ⇒
test-ρ⇒∘f⊗id = solve!

test-α-comm
  : α⇒ ∘ ((Agen f ⊗₁ Agen g) ⊗₁ Agen h)
  ≈Term (Agen f ⊗₁ (Agen g ⊗₁ Agen h)) ∘ α⇒
test-α-comm = solve!

test-triangle : id {a₀} ⊗₁ λ⇒ {a₁} ∘ α⇒ {a₀} {unit} {a₁} ≈Term ρ⇒ {a₀} ⊗₁ id {a₁}
test-triangle = solve!

test-pentagon
  : (id {a₀} ⊗₁ α⇒ {a₁} {a₂} {a₀})
       ∘ α⇒ {a₀} {a₁ ⊗₀ a₂} {a₀}
       ∘ (α⇒ {a₀} {a₁} {a₂} ⊗₁ id {a₀})
  ≈Term α⇒ {a₀} {a₁} {a₂ ⊗₀ a₀}
       ∘ α⇒ {a₀ ⊗₀ a₁} {a₂} {a₀}
test-pentagon = solve!

test-σ∘σ : σ ∘ σ {a₀} {a₁} ≈Term id {a₀ ⊗₀ a₁}
test-σ∘σ = solve!

test-σ∘[f⊗g] : σ ∘ (Agen f ⊗₁ Agen g) ≈Term (Agen g ⊗₁ Agen f) ∘ σ
test-σ∘[f⊗g] = solve!

test-hexagon
  : id {a₁} ⊗₁ σ ∘ α⇒ {a₁} {a₀} {a₂} ∘ σ ⊗₁ id {a₂}
  ≈Term α⇒ {a₁} {a₂} {a₀} ∘ σ {a₀} {a₁ ⊗₀ a₂} ∘ α⇒ {a₀} {a₁} {a₂}
test-hexagon = solve!
