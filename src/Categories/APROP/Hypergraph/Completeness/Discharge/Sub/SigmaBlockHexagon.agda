{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- σ-block algebra: σ-block-involutive, σ-block-natural{₁,₃},
-- hexagon₂ (dual hexagon), and σ-block-hexagon (Yang-Baxter braid at the
-- σ-block level).
--
-- `permute (swap k k' p)` produces the WRAPPED pattern
--
--     σ-block = α⇒ ∘ (σ ⊗ id) ∘ α⇐    : A ⊗ (B ⊗ C) → B ⊗ (A ⊗ C)
--
-- which operates on the right-associated unflatten shape, whereas
-- `FreeMonoidal.hexagon` targets the BARE σ.  To handle Yang-Baxter
-- cascades at the `permute` level we lift the standard algebra to the
-- σ-block level.  Everything below is derived from the FreeMonoidal
-- (symmetric) axioms alone.
--------------------------------------------------------------------------------

open import Categories.FreeMonoidal

-- Stated over an arbitrary `FreeMonoidalData` with a symmetric structure;
-- the body uses only the free (symmetric) monoidal structure.
module Categories.APROP.Hypergraph.Completeness.Discharge.Sub.SigmaBlockHexagon
  (d : FreeMonoidalData) ⦃ s≤v : Symm ≤ FreeMonoidalData.v d ⦄ where

open FreeMonoidal d

open import Categories.Category using (Category)

open import Categories.PermuteCoherence.Faithfulness d using (α⇐-comm)

-- Mac-Lane coherence solver, used to discharge the pure-associator framing
-- lemmas below (`pentagon-flip-right`, `α⇐∘id⊗α⇒-rewrite`,
-- `α⇐-stack-from-pentagon`) in one line each.
open import Categories.MonoidalCoherence using (module Solver)
import Data.Vec as Vec
open Vec using (Vec)
open import Data.Fin using (Fin; zero; suc)

private
  module FM = Category FreeMonoidal

open FM.HomReasoning

-- σ-block: matches what `permute (swap k k' p)` produces (modulo the
-- (id ⊗₁ (id ⊗₁ permute p)) outer prefix).
σ-block : ∀ {A B C : ObjTerm} → HomTerm (A ⊗₀ (B ⊗₀ C)) (B ⊗₀ (A ⊗₀ C))
σ-block = α⇒ ∘ (σ ⊗₁ id) ∘ α⇐

-- σ-block-natural₃: σ-block is natural in the third argument.
σ-block-natural₃
  : ∀ {A B C D : ObjTerm} {f : HomTerm C D}
  → (α⇒ ∘ (σ {A = A} {B = B} ⊗₁ id) ∘ α⇐) ∘ (id ⊗₁ (id ⊗₁ f))
    ≈Term (id ⊗₁ (id ⊗₁ f)) ∘ (α⇒ ∘ (σ ⊗₁ id) ∘ α⇐)
σ-block-natural₃ {A} {B} {C} {D} {f} =
  let lhs→common =
        begin
          (α⇒ ∘ (σ ⊗₁ id) ∘ α⇐) ∘ (id ⊗₁ (id ⊗₁ f))
            ≈⟨ assoc ⟩
          α⇒ ∘ ((σ ⊗₁ id) ∘ α⇐) ∘ (id ⊗₁ (id ⊗₁ f))
            ≈⟨ refl⟩∘⟨ assoc ⟩
          α⇒ ∘ (σ ⊗₁ id) ∘ (α⇐ ∘ (id ⊗₁ (id ⊗₁ f)))
            ≈⟨ refl⟩∘⟨ (refl⟩∘⟨ α⇐-comm) ⟩
          α⇒ ∘ (σ ⊗₁ id) ∘ (((id ⊗₁ id) ⊗₁ f) ∘ α⇐)
            ≈⟨ refl⟩∘⟨ (≈-Term-sym assoc) ⟩
          α⇒ ∘ ((σ ⊗₁ id) ∘ ((id ⊗₁ id) ⊗₁ f)) ∘ α⇐
            ≈⟨ refl⟩∘⟨ ((≈-Term-trans (≈-Term-sym ⊗-∘-dist)
                            (⊗-resp-≈ (≈-Term-trans (refl⟩∘⟨ id⊗id≈id) idʳ)
                                      idˡ)) ⟩∘⟨refl) ⟩
          α⇒ ∘ (σ ⊗₁ f) ∘ α⇐
        ∎
      rhs→common =
        begin
          (id ⊗₁ (id ⊗₁ f)) ∘ (α⇒ ∘ (σ ⊗₁ id) ∘ α⇐)
            ≈⟨ ≈-Term-sym assoc ⟩
          ((id ⊗₁ (id ⊗₁ f)) ∘ α⇒) ∘ ((σ ⊗₁ id) ∘ α⇐)
            ≈⟨ (≈-Term-sym α-comm) ⟩∘⟨refl ⟩
          (α⇒ ∘ ((id ⊗₁ id) ⊗₁ f)) ∘ ((σ ⊗₁ id) ∘ α⇐)
            ≈⟨ assoc ⟩
          α⇒ ∘ (((id ⊗₁ id) ⊗₁ f) ∘ ((σ ⊗₁ id) ∘ α⇐))
            ≈⟨ refl⟩∘⟨ (≈-Term-sym assoc) ⟩
          α⇒ ∘ ((((id ⊗₁ id) ⊗₁ f)) ∘ (σ ⊗₁ id)) ∘ α⇐
            ≈⟨ refl⟩∘⟨ ((≈-Term-trans (≈-Term-sym ⊗-∘-dist)
                            (⊗-resp-≈ (≈-Term-trans (id⊗id≈id ⟩∘⟨refl) idˡ)
                                      idʳ)) ⟩∘⟨refl) ⟩
          α⇒ ∘ (σ ⊗₁ f) ∘ α⇐
        ∎
  in ≈-Term-trans lhs→common (≈-Term-sym rhs→common)

-- σ-block-natural₁: σ-block is natural in the first argument, at type
-- A⊗(B⊗C) → B⊗(A'⊗C) where f : A → A'.
σ-block-natural₁
  : ∀ {A A' B C : ObjTerm} {f : HomTerm A A'}
  → (α⇒ {A = B} {B = A'} {C = C} ∘ ((σ {A = A'} {B = B}) ⊗₁ id) ∘ α⇐ {A = A'} {B = B} {C = C}) ∘ (f ⊗₁ id {A = B ⊗₀ C})
    ≈Term (id {A = B} ⊗₁ (f ⊗₁ id {A = C}))
            ∘ (α⇒ {A = B} {B = A} {C = C} ∘ ((σ {A = A} {B = B}) ⊗₁ id) ∘ α⇐ {A = A} {B = B} {C = C})
σ-block-natural₁ {A} {A'} {B} {C} {f} =
  let lhs→common =
        begin
          (α⇒ ∘ (σ ⊗₁ id) ∘ α⇐) ∘ (f ⊗₁ id)
            ≈⟨ assoc ⟩
          α⇒ ∘ ((σ ⊗₁ id) ∘ α⇐) ∘ (f ⊗₁ id)
            ≈⟨ refl⟩∘⟨ assoc ⟩
          α⇒ ∘ (σ ⊗₁ id) ∘ (α⇐ ∘ (f ⊗₁ id))
            ≈⟨ refl⟩∘⟨ (refl⟩∘⟨ (≈-Term-trans
                     (refl⟩∘⟨ (⊗-resp-≈ ≈-Term-refl (≈-Term-sym id⊗id≈id)))
                     α⇐-comm)) ⟩
          α⇒ ∘ (σ ⊗₁ id) ∘ (((f ⊗₁ id) ⊗₁ id) ∘ α⇐)
            ≈⟨ refl⟩∘⟨ (≈-Term-sym assoc) ⟩
          α⇒ ∘ ((σ ⊗₁ id) ∘ ((f ⊗₁ id) ⊗₁ id)) ∘ α⇐
            ≈⟨ refl⟩∘⟨ ((≈-Term-trans (≈-Term-sym ⊗-∘-dist)
                            (⊗-resp-≈ σ∘[f⊗g]≈[g⊗f]∘σ idˡ)) ⟩∘⟨refl) ⟩
          α⇒ ∘ (((id ⊗₁ f) ∘ σ) ⊗₁ id) ∘ α⇐
            ≈⟨ refl⟩∘⟨ ((≈-Term-trans
                              (⊗-resp-≈ ≈-Term-refl (≈-Term-sym idˡ))
                              ⊗-∘-dist) ⟩∘⟨refl) ⟩
          α⇒ ∘ (((id ⊗₁ f) ⊗₁ id) ∘ ((σ ⊗₁ id))) ∘ α⇐
            ≈⟨ refl⟩∘⟨ assoc ⟩
          α⇒ ∘ ((id ⊗₁ f) ⊗₁ id) ∘ (σ ⊗₁ id) ∘ α⇐
            ≈⟨ ≈-Term-sym assoc ⟩
          (α⇒ ∘ ((id ⊗₁ f) ⊗₁ id)) ∘ ((σ ⊗₁ id) ∘ α⇐)
            ≈⟨ α-comm ⟩∘⟨refl ⟩
          ((id ⊗₁ (f ⊗₁ id)) ∘ α⇒) ∘ ((σ ⊗₁ id) ∘ α⇐)
            ≈⟨ assoc ⟩
          (id ⊗₁ (f ⊗₁ id)) ∘ (α⇒ ∘ (σ ⊗₁ id) ∘ α⇐)
        ∎
  in lhs→common

--------------------------------------------------------------------------------
-- hexagon₂: the dual hexagon at the α⇐ level (derived from the standard
-- hexagon):
--   σ ⊗ id ∘ α⇐ ∘ id ⊗ σ ≈ α⇐ ∘ σ ∘ α⇐
-- at type X⊗(Y⊗Z) → (Z⊗X)⊗Y.

private
  h₁L∘h₂L≈id
    : ∀ {X Y Z : ObjTerm}
    → ((id {A = X} ⊗₁ σ {A = Z} {B = Y}) ∘ α⇒ {A = X} {B = Z} {C = Y}
        ∘ (σ {A = Z} {B = X} ⊗₁ id {A = Y}))
      ∘ ((σ {A = X} {B = Z} ⊗₁ id {A = Y}) ∘ α⇐ {A = X} {B = Z} {C = Y}
          ∘ (id {A = X} ⊗₁ σ {A = Y} {B = Z}))
      ≈Term id
  h₁L∘h₂L≈id {X} {Y} {Z} =
    begin
      ((id ⊗₁ σ) ∘ α⇒ ∘ (σ ⊗₁ id))
        ∘ ((σ ⊗₁ id) ∘ α⇐ ∘ (id ⊗₁ σ))
        ≈⟨ assoc ⟩
      (id ⊗₁ σ) ∘ ((α⇒ ∘ (σ ⊗₁ id))
        ∘ ((σ ⊗₁ id) ∘ α⇐ ∘ (id ⊗₁ σ)))
        ≈⟨ refl⟩∘⟨ assoc ⟩
      (id ⊗₁ σ) ∘ α⇒ ∘ ((σ ⊗₁ id)
        ∘ ((σ ⊗₁ id) ∘ α⇐ ∘ (id ⊗₁ σ)))
        ≈⟨ refl⟩∘⟨ (refl⟩∘⟨ (≈-Term-sym assoc)) ⟩
      (id ⊗₁ σ) ∘ α⇒ ∘ ((σ ⊗₁ id) ∘ (σ ⊗₁ id))
        ∘ α⇐ ∘ (id ⊗₁ σ)
        ≈⟨ refl⟩∘⟨ (refl⟩∘⟨ ((≈-Term-trans (≈-Term-sym ⊗-∘-dist)
                            (≈-Term-trans (⊗-resp-≈ σ∘σ≈id idˡ) id⊗id≈id)) ⟩∘⟨refl)) ⟩
      (id ⊗₁ σ) ∘ α⇒ ∘ id ∘ α⇐ ∘ (id ⊗₁ σ)
        ≈⟨ refl⟩∘⟨ (refl⟩∘⟨ idˡ) ⟩
      (id ⊗₁ σ) ∘ α⇒ ∘ (α⇐ ∘ (id ⊗₁ σ))
        ≈⟨ refl⟩∘⟨ (≈-Term-sym assoc) ⟩
      (id ⊗₁ σ) ∘ (α⇒ ∘ α⇐) ∘ (id ⊗₁ σ)
        ≈⟨ refl⟩∘⟨ (α⇒∘α⇐≈id ⟩∘⟨refl) ⟩
      (id ⊗₁ σ) ∘ id ∘ (id ⊗₁ σ)
        ≈⟨ refl⟩∘⟨ idˡ ⟩
      (id ⊗₁ σ) ∘ (id ⊗₁ σ)
        ≈⟨ ≈-Term-trans (≈-Term-sym ⊗-∘-dist)
             (≈-Term-trans (⊗-resp-≈ idˡ σ∘σ≈id) id⊗id≈id) ⟩
      id
    ∎

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
-- Pentagon-shifted identities for σ-block-hexagon.

private
  -- pentagon-flip-right: (id_P ⊗ α⇐_{Q,R,S}) ∘ α⇒_{P,Q,R⊗S}
  --                    ≈ α⇒_{P,Q⊗R,S} ∘ (α⇒_{P,Q,R} ⊗ id_S) ∘ α⇐_{P⊗Q,R,S}.
  pentagon-flip-right
    : ∀ {P Q R S : ObjTerm}
    → (id {A = P} ⊗₁ α⇐ {A = Q} {B = R} {C = S})
        ∘ α⇒ {A = P} {B = Q} {C = R ⊗₀ S}
      ≈Term α⇒ {A = P} {B = Q ⊗₀ R} {C = S}
              ∘ (α⇒ {A = P} {B = Q} {C = R} ⊗₁ id {A = S})
              ∘ α⇐ {A = P ⊗₀ Q} {B = R} {C = S}
  pentagon-flip-right {P} {Q} {R} {S} = solveM
      ((idˢ ⊗₁ˢ α⇐ˢ {A = q} {r} {s}) ∘ˢ α⇒ˢ {A = p} {q} {r ⊗₀ˢ s})
      (α⇒ˢ {A = p} {q ⊗₀ˢ r} {s}
        ∘ˢ (α⇒ˢ {A = p} {q} {r} ⊗₁ˢ idˢ)
        ∘ˢ α⇐ˢ {A = p ⊗₀ˢ q} {r} {s})
    where
      vars : Vec ObjTerm 4
      vars = P Vec.∷ Q Vec.∷ R Vec.∷ S Vec.∷ Vec.[]
      open Solver (record { U = FreeMonoidal ; monoidal = Monoidal-FreeMonoidal })
                  {n = 4} vars
        using (solveM)
        renaming (α⇒ to α⇒ˢ; α⇐ to α⇐ˢ; id to idˢ; _∘_ to _∘ˢ_;
                  _⊗₁_ to _⊗₁ˢ_; _⊗₀_ to _⊗₀ˢ_; Var to Varˢ)
      p q r s : _
      p = Varˢ zero
      q = Varˢ (suc zero)
      r = Varˢ (suc (suc zero))
      s = Varˢ (suc (suc (suc zero)))

--------------------------------------------------------------------------------
-- α⇐∘id⊗α⇒-rewrite: α⇐_{P,Q,R⊗S} ∘ (id_P ⊗ α⇒_{Q,R,S})
--   ≈ α⇒_{P⊗Q,R,S} ∘ (α⇐_{P,Q,R} ⊗ id_S) ∘ α⇐_{P,Q⊗R,S}.

private
  α⇐∘id⊗α⇒-rewrite
    : ∀ {P Q R S : ObjTerm}
    → α⇐ {A = P} {B = Q} {C = R ⊗₀ S}
        ∘ (id {A = P} ⊗₁ α⇒ {A = Q} {B = R} {C = S})
      ≈Term α⇒ {A = P ⊗₀ Q} {B = R} {C = S}
              ∘ (α⇐ {A = P} {B = Q} {C = R} ⊗₁ id {A = S})
              ∘ α⇐ {A = P} {B = Q ⊗₀ R} {C = S}
  α⇐∘id⊗α⇒-rewrite {P} {Q} {R} {S} = solveM
      (α⇐ˢ {A = p} {q} {r ⊗₀ˢ s} ∘ˢ (idˢ ⊗₁ˢ α⇒ˢ {A = q} {r} {s}))
      (α⇒ˢ {A = p ⊗₀ˢ q} {r} {s}
        ∘ˢ (α⇐ˢ {A = p} {q} {r} ⊗₁ˢ idˢ)
        ∘ˢ α⇐ˢ {A = p} {q ⊗₀ˢ r} {s})
    where
      vars : Vec ObjTerm 4
      vars = P Vec.∷ Q Vec.∷ R Vec.∷ S Vec.∷ Vec.[]
      open Solver (record { U = FreeMonoidal ; monoidal = Monoidal-FreeMonoidal })
                  {n = 4} vars
        using (solveM)
        renaming (α⇒ to α⇒ˢ; α⇐ to α⇐ˢ; id to idˢ; _∘_ to _∘ˢ_;
                  _⊗₁_ to _⊗₁ˢ_; _⊗₀_ to _⊗₀ˢ_; Var to Varˢ)
      p q r s : _
      p = Varˢ zero
      q = Varˢ (suc zero)
      r = Varˢ (suc (suc zero))
      s = Varˢ (suc (suc (suc zero)))

--------------------------------------------------------------------------------
-- σ-block-hexagon: Yang-Baxter braid at the σ-block level (4-object).
--
--   (id_C ⊗ σ-block_{A,B,D}) ∘ σ-block_{A,C,B⊗D} ∘ (id_A ⊗ σ-block_{B,C,D})
--     ≈Term σ-block_{B,C,A⊗D} ∘ (id_B ⊗ σ-block_{A,C,D}) ∘ σ-block_{A,B,C⊗D}
--
-- at type A ⊗ (B ⊗ (C ⊗ D)) → C ⊗ (B ⊗ (A ⊗ D)).  Both sides implement
-- the transposition of A and C with B,D fixed — the Yang-Baxter braid
-- relation s₂ s₁ s₂ = s₁ s₂ s₁.  The proof reduces both sides to a common
-- normal form via pentagon-coherence rewrites and the bare hexagon.
--------------------------------------------------------------------------------

-- Tail-only hexagon: bare hexagon ⊗ id_W.  At objects A, B, C:
--   id_B ⊗ σ_{A,C} ∘ α⇒_{B,A,C} ∘ σ_{A,B} ⊗ id_C
--     ≈ α⇒_{B,C,A} ∘ σ_{A,B⊗C} ∘ α⇒_{A,B,C}.
private
  hexagon-with-tail
    : ∀ {A B C W : ObjTerm}
    → (((id {A = B} ⊗₁ σ {A = A} {B = C}) ⊗₁ id {A = W})
        ∘ (α⇒ {A = B} {B = A} {C = C} ⊗₁ id {A = W})
        ∘ ((σ {A = A} {B = B} ⊗₁ id {A = C}) ⊗₁ id {A = W}))
      ≈Term ((α⇒ {A = B} {B = C} {C = A} ⊗₁ id {A = W})
              ∘ (σ {A = A} {B = B ⊗₀ C} ⊗₁ id {A = W})
              ∘ (α⇒ {A = A} {B = B} {C = C} ⊗₁ id {A = W}))
  hexagon-with-tail {A} {B} {C} {W} =
    begin
      ((id ⊗₁ σ) ⊗₁ id) ∘ (α⇒ ⊗₁ id) ∘ ((σ ⊗₁ id) ⊗₁ id)
        ≈⟨ refl⟩∘⟨ (≈-Term-trans (≈-Term-sym ⊗-∘-dist)
               (⊗-resp-≈ ≈-Term-refl idˡ)) ⟩
      ((id ⊗₁ σ) ⊗₁ id) ∘ ((α⇒ ∘ (σ ⊗₁ id)) ⊗₁ id)
        ≈⟨ ≈-Term-trans (≈-Term-sym ⊗-∘-dist)
             (⊗-resp-≈ ≈-Term-refl idˡ) ⟩
      ((id ⊗₁ σ) ∘ α⇒ ∘ (σ ⊗₁ id)) ⊗₁ id
        ≈⟨ ⊗-resp-≈ hexagon ≈-Term-refl ⟩
      (α⇒ ∘ σ ∘ α⇒) ⊗₁ id
        ≈⟨ ≈-Term-trans (⊗-resp-≈ ≈-Term-refl (≈-Term-sym idˡ)) ⊗-∘-dist ⟩
      (α⇒ ⊗₁ id) ∘ ((σ ∘ α⇒) ⊗₁ id)
        ≈⟨ refl⟩∘⟨ (≈-Term-trans (⊗-resp-≈ ≈-Term-refl (≈-Term-sym idˡ)) ⊗-∘-dist) ⟩
      (α⇒ ⊗₁ id) ∘ (σ ⊗₁ id) ∘ (α⇒ ⊗₁ id)
    ∎

--------------------------------------------------------------------------------
-- σ⊗id-collapse-middle: for the central α⇐∘(σ⊗id)∘α⇒ chunk,
--   α⇐_{C⊗A,B,D} ∘ (σ_{A,C} ⊗ id_{B⊗D}) ∘ α⇒_{A⊗C,B,D}
--     ≈ ((σ_{A,C} ⊗ id_B) ⊗ id_D)
-- by sliding σ⊗id past α via α⇐-comm, then collapsing α⇐∘α⇒≈id.

private
  σ⊗id-collapse-middle
    : ∀ {A B C D : ObjTerm}
    → α⇐ {A = C ⊗₀ A} {B = B} {C = D}
        ∘ (σ {A = A} {B = C} ⊗₁ id {A = B ⊗₀ D})
        ∘ α⇒ {A = A ⊗₀ C} {B = B} {C = D}
      ≈Term ((σ {A = A} {B = C} ⊗₁ id {A = B}) ⊗₁ id {A = D})
  σ⊗id-collapse-middle {A} {B} {C} {D} =
    begin
      α⇐ ∘ (σ ⊗₁ id) ∘ α⇒
        ≈⟨ refl⟩∘⟨ ((⊗-resp-≈ ≈-Term-refl (≈-Term-sym id⊗id≈id)) ⟩∘⟨refl) ⟩
      α⇐ ∘ (σ ⊗₁ (id ⊗₁ id)) ∘ α⇒
        ≈⟨ ≈-Term-sym assoc ⟩
      (α⇐ ∘ (σ ⊗₁ (id ⊗₁ id))) ∘ α⇒
        ≈⟨ α⇐-comm ⟩∘⟨refl ⟩
      (((σ ⊗₁ id) ⊗₁ id) ∘ α⇐) ∘ α⇒
        ≈⟨ assoc ⟩
      ((σ ⊗₁ id) ⊗₁ id) ∘ (α⇐ ∘ α⇒)
        ≈⟨ refl⟩∘⟨ α⇐∘α⇒≈id ⟩
      ((σ ⊗₁ id) ⊗₁ id) ∘ id
        ≈⟨ idʳ ⟩
      ((σ ⊗₁ id) ⊗₁ id)
    ∎

--------------------------------------------------------------------------------
-- ## Pentagon-stack identity used in σ-block-hexagon:
--   α⇐_{P,Q⊗R,S} ∘ (id_P ⊗ α⇐_{Q,R,S})
--     ≈ (α⇒_{P,Q,R} ⊗ id_S) ∘ α⇐_{P⊗Q,R,S} ∘ α⇐_{P,Q,R⊗S}.

private
  α⇐-stack-from-pentagon
    : ∀ {P Q R S : ObjTerm}
    → α⇐ {A = P} {B = Q ⊗₀ R} {C = S}
        ∘ (id {A = P} ⊗₁ α⇐ {A = Q} {B = R} {C = S})
      ≈Term (α⇒ {A = P} {B = Q} {C = R} ⊗₁ id {A = S})
              ∘ α⇐ {A = P ⊗₀ Q} {B = R} {C = S}
              ∘ α⇐ {A = P} {B = Q} {C = R ⊗₀ S}
  α⇐-stack-from-pentagon {P} {Q} {R} {S} = solveM
      (α⇐ˢ {A = p} {q ⊗₀ˢ r} {s} ∘ˢ (idˢ ⊗₁ˢ α⇐ˢ {A = q} {r} {s}))
      ((α⇒ˢ {A = p} {q} {r} ⊗₁ˢ idˢ)
        ∘ˢ α⇐ˢ {A = p ⊗₀ˢ q} {r} {s}
        ∘ˢ α⇐ˢ {A = p} {q} {r ⊗₀ˢ s})
    where
      vars : Vec ObjTerm 4
      vars = P Vec.∷ Q Vec.∷ R Vec.∷ S Vec.∷ Vec.[]
      open Solver (record { U = FreeMonoidal ; monoidal = Monoidal-FreeMonoidal })
                  {n = 4} vars
        using (solveM)
        renaming (α⇒ to α⇒ˢ; α⇐ to α⇐ˢ; id to idˢ; _∘_ to _∘ˢ_;
                  _⊗₁_ to _⊗₁ˢ_; _⊗₀_ to _⊗₀ˢ_; Var to Varˢ)
      p q r s : _
      p = Varˢ zero
      q = Varˢ (suc zero)
      r = Varˢ (suc (suc zero))
      s = Varˢ (suc (suc (suc zero)))

--------------------------------------------------------------------------------
-- The σ-block-hexagon proof reduces both sides to a common inner-form
--
--   common = α⇒_{C,B,A⊗D} ∘ α⇒_{C⊗B,A,D}
--          ∘ [inner ⊗ id_D] ∘ α⇐_{A⊗B,C,D} ∘ α⇐_{A,B,C⊗D}
--
-- where `inner : (A⊗B)⊗C → (C⊗B)⊗A` is the 3-letter reverse permutation,
-- with two equivalent forms (related by hexagon₁):
--   inner-L = α⇐_{C,B,A} ∘ (id_C ⊗ σ_{A,B}) ∘ σ_{A⊗B,C}
--   inner-R = σ_{A,C⊗B} ∘ (id_A ⊗ σ_{B,C}) ∘ α⇒_{A,B,C}.

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

-- inner-eq: inner-L ≈ inner-R, where
--   inner-L = α⇐_{C,B,A} ∘ (id_C ⊗ σ_{A,B}) ∘ σ_{A⊗B,C}
--   inner-R = σ_{A,C⊗B} ∘ (id_A ⊗ σ_{B,C}) ∘ α⇒_{A,B,C}.
-- Expand σ_{A⊗B,C}, apply hexagon₁ at the center, then cancel α-isos.
inner-eq
  : ∀ {A B C : ObjTerm}
  → α⇐ {A = C} {B = B} {C = A}
      ∘ (id {A = C} ⊗₁ σ {A = A} {B = B})
      ∘ σ {A = A ⊗₀ B} {B = C}
    ≈Term σ {A = A} {B = C ⊗₀ B}
            ∘ (id {A = A} ⊗₁ σ {A = B} {B = C})
            ∘ α⇒ {A = A} {B = B} {C = C}
inner-eq {A} {B} {C} =
    begin
      α⇐ ∘ (id ⊗₁ σ) ∘ σ
        ≈⟨ refl⟩∘⟨ (refl⟩∘⟨ σ-A⊗B-expand) ⟩
      α⇐ ∘ (id ⊗₁ σ) ∘ (α⇒ ∘ (σ ⊗₁ id) ∘ α⇐ ∘ (id ⊗₁ σ) ∘ α⇒)
        -- Reassociate to expose ((id ⊗ σ) ∘ α⇒ ∘ (σ ⊗ id)) for hexagon.
        ≈⟨ ≈-Term-sym assoc ⟩
      (α⇐ ∘ (id ⊗₁ σ)) ∘ (α⇒ ∘ (σ ⊗₁ id) ∘ α⇐ ∘ (id ⊗₁ σ) ∘ α⇒)
        ≈⟨ refl⟩∘⟨ (≈-Term-sym assoc) ⟩
      (α⇐ ∘ (id ⊗₁ σ)) ∘ ((α⇒ ∘ (σ ⊗₁ id)) ∘ α⇐ ∘ (id ⊗₁ σ) ∘ α⇒)
        ≈⟨ ≈-Term-sym assoc ⟩
      ((α⇐ ∘ (id ⊗₁ σ)) ∘ (α⇒ ∘ (σ ⊗₁ id))) ∘ α⇐ ∘ (id ⊗₁ σ) ∘ α⇒
        ≈⟨ assoc ⟩∘⟨refl ⟩
      (α⇐ ∘ ((id ⊗₁ σ) ∘ (α⇒ ∘ (σ ⊗₁ id)))) ∘ α⇐ ∘ (id ⊗₁ σ) ∘ α⇒
        ≈⟨ (refl⟩∘⟨ (≈-Term-sym assoc)) ⟩∘⟨refl ⟩
      (α⇐ ∘ (((id ⊗₁ σ) ∘ α⇒) ∘ (σ ⊗₁ id))) ∘ α⇐ ∘ (id ⊗₁ σ) ∘ α⇒
        ≈⟨ (refl⟩∘⟨ assoc) ⟩∘⟨refl ⟩
      (α⇐ ∘ ((id ⊗₁ σ) ∘ α⇒ ∘ (σ ⊗₁ id))) ∘ α⇐ ∘ (id ⊗₁ σ) ∘ α⇒
        ≈⟨ (refl⟩∘⟨ hexagon) ⟩∘⟨refl ⟩
      (α⇐ ∘ (α⇒ ∘ σ ∘ α⇒)) ∘ α⇐ ∘ (id ⊗₁ σ) ∘ α⇒
        ≈⟨ (≈-Term-sym assoc) ⟩∘⟨refl ⟩
      ((α⇐ ∘ α⇒) ∘ σ ∘ α⇒) ∘ α⇐ ∘ (id ⊗₁ σ) ∘ α⇒
        ≈⟨ (α⇐∘α⇒≈id ⟩∘⟨refl) ⟩∘⟨refl ⟩
      (id ∘ σ ∘ α⇒) ∘ α⇐ ∘ (id ⊗₁ σ) ∘ α⇒
        ≈⟨ idˡ ⟩∘⟨refl ⟩
      (σ ∘ α⇒) ∘ α⇐ ∘ (id ⊗₁ σ) ∘ α⇒
        ≈⟨ assoc ⟩
      σ ∘ (α⇒ ∘ α⇐ ∘ (id ⊗₁ σ) ∘ α⇒)
        ≈⟨ refl⟩∘⟨ (≈-Term-sym assoc) ⟩
      σ ∘ ((α⇒ ∘ α⇐) ∘ (id ⊗₁ σ) ∘ α⇒)
        ≈⟨ refl⟩∘⟨ (α⇒∘α⇐≈id ⟩∘⟨refl) ⟩
      σ ∘ (id ∘ (id ⊗₁ σ) ∘ α⇒)
        ≈⟨ refl⟩∘⟨ idˡ ⟩
      σ ∘ ((id ⊗₁ σ) ∘ α⇒)
        ≈⟨ ≈-Term-sym assoc ⟩
      (σ ∘ (id ⊗₁ σ)) ∘ α⇒
        ≈⟨ assoc ⟩
      σ ∘ (id ⊗₁ σ) ∘ α⇒
    ∎

--------------------------------------------------------------------------------
-- The common normal form (NF-R) for σ-block-hexagon's two sides.

private
  inner-R : ∀ {A B C : ObjTerm} → HomTerm ((A ⊗₀ B) ⊗₀ C) ((C ⊗₀ B) ⊗₀ A)
  inner-R {A} {B} {C} = σ {A = A} {B = C ⊗₀ B}
                      ∘ (id {A = A} ⊗₁ σ {A = B} {B = C})
                      ∘ α⇒ {A = A} {B = B} {C = C}

  NF-R : ∀ {A B C D : ObjTerm}
       → HomTerm (A ⊗₀ (B ⊗₀ (C ⊗₀ D))) (C ⊗₀ (B ⊗₀ (A ⊗₀ D)))
  NF-R {A} {B} {C} {D}
    = α⇒ {A = C} {B = B} {C = A ⊗₀ D}
    ∘ α⇒ {A = C ⊗₀ B} {B = A} {C = D}
    ∘ (inner-R {A} {B} {C} ⊗₁ id {A = D})
    ∘ α⇐ {A = A ⊗₀ B} {B = C} {C = D}
    ∘ α⇐ {A = A} {B = B} {C = C ⊗₀ D}

  -- id ⊗ (f ∘ g) ≈ (id ⊗ f) ∘ (id ⊗ g).
  id⊗-dist
    : ∀ {X Y₁ Y₂ Y₃ : ObjTerm}
        {f : HomTerm Y₂ Y₃} {g : HomTerm Y₁ Y₂}
    → id {A = X} ⊗₁ (f ∘ g) ≈Term (id ⊗₁ f) ∘ (id ⊗₁ g)
  id⊗-dist = ≈-Term-trans (⊗-resp-≈ (≈-Term-sym idˡ) ≈-Term-refl) ⊗-∘-dist

  -- Rewrite (id ⊗ σ-block) as three (id ⊗ ?) factors.
  id⊗σ-block-expand
    : ∀ {X A B C : ObjTerm}
    → id {A = X} ⊗₁ σ-block {A = A} {B = B} {C = C}
      ≈Term (id {A = X} ⊗₁ α⇒ {A = B} {B = A} {C = C})
              ∘ (id ⊗₁ (σ {A = A} {B = B} ⊗₁ id {A = C}))
              ∘ (id ⊗₁ α⇐ {A = A} {B = B} {C = C})
  id⊗σ-block-expand =
    ≈-Term-trans id⊗-dist (refl⟩∘⟨ id⊗-dist)

--------------------------------------------------------------------------------
-- LHS-to-NF-R: both sides reduce to NF-R via a chain of pentagon +
-- hexagon₂ rewrites (steps A–I below).

private
  -- LHS after expanding σ-block definitions via id⊗σ-block-expand.
  LHS-expanded
    : ∀ {A B C D : ObjTerm}
    → HomTerm (A ⊗₀ (B ⊗₀ (C ⊗₀ D))) (C ⊗₀ (B ⊗₀ (A ⊗₀ D)))
  LHS-expanded {A} {B} {C} {D}
    = ((id {A = C} ⊗₁ α⇒ {A = B} {B = A} {C = D})
        ∘ (id ⊗₁ (σ {A = A} {B = B} ⊗₁ id {A = D}))
        ∘ (id ⊗₁ α⇐ {A = A} {B = B} {C = D}))
    ∘ (α⇒ {A = C} {B = A} {C = B ⊗₀ D}
        ∘ (σ {A = A} {B = C} ⊗₁ id {A = B ⊗₀ D})
        ∘ α⇐ {A = A} {B = C} {C = B ⊗₀ D})
    ∘ ((id {A = A} ⊗₁ α⇒ {A = C} {B = B} {C = D})
        ∘ (id ⊗₁ (σ {A = B} {B = C} ⊗₁ id {A = D}))
        ∘ (id ⊗₁ α⇐ {A = B} {B = C} {C = D}))

  LHS-to-expanded
    : ∀ {A B C D : ObjTerm}
    → (id {A = C} ⊗₁ σ-block {A = A} {B = B} {C = D})
        ∘ σ-block {A = A} {B = C} {C = B ⊗₀ D}
        ∘ (id {A = A} ⊗₁ σ-block {A = B} {B = C} {C = D})
      ≈Term LHS-expanded {A} {B} {C} {D}
  LHS-to-expanded =
    ∘-resp-≈ id⊗σ-block-expand
      (refl⟩∘⟨ id⊗σ-block-expand)

--------------------------------------------------------------------------------
-- `LHS-expanded ≈ NF-R` (= α⇒ ∘ α⇒ ∘ (inner-R ⊗ id) ∘ α⇐ ∘ α⇐) via the
-- 9-step chain step-A … step-I:
--   A: flatten the 3 grouped triples into a 9-morphism chain.
--   B: pentagon-flip-right at e3-e4, α⇐∘id⊗α⇒-rewrite at e6-e7.
--   C/D: group + collapse the middle α⇐ ∘ (σ⊗id) ∘ α⇒ via σ⊗id-collapse-middle.
--   E: α-comm / α⇐-comm to convert (id ⊗ (σ⊗id_D)) to ((id⊗σ)⊗id).
--   F: hexagon-with-tail at the inner (id_C⊗σ) ∘ α⇒ ∘ (σ⊗id_B), then cancel.
--   G/H: pentagon / α⇐-stack-from-pentagon at the top/bottom boundaries.
--   I: factor the 3 middle (X ⊗ id_D) pieces into (inner-R ⊗ id_D).

private
  LHS-to-NF-R : ∀ {A B C D : ObjTerm}
              → LHS-expanded {A} {B} {C} {D} ≈Term NF-R {A} {B} {C} {D}
  LHS-to-NF-R {A} {B} {C} {D} = begin
      LHS-expanded {A} {B} {C} {D}
        -- A: 4 assoc rotations.
        ≈⟨ ≈-Term-trans assoc
             (≈-Term-trans (refl⟩∘⟨ assoc)
               (≈-Term-trans (refl⟩∘⟨ (refl⟩∘⟨ (refl⟩∘⟨ assoc)))
                 (refl⟩∘⟨ (refl⟩∘⟨ (refl⟩∘⟨ (refl⟩∘⟨ assoc)))))) ⟩
      (id {A = C} ⊗₁ α⇒ {A = B} {B = A} {C = D})
        ∘ (id ⊗₁ (σ {A = A} {B = B} ⊗₁ id {A = D}))
        ∘ (id ⊗₁ α⇐ {A = A} {B = B} {C = D})
        ∘ (α⇒ {A = C} {B = A} {C = B ⊗₀ D})
        ∘ (σ {A = A} {B = C} ⊗₁ id {A = B ⊗₀ D})
        ∘ (α⇐ {A = A} {B = C} {C = B ⊗₀ D})
        ∘ (id {A = A} ⊗₁ α⇒ {A = C} {B = B} {C = D})
        ∘ (id ⊗₁ (σ {A = B} {B = C} ⊗₁ id {A = D}))
        ∘ (id ⊗₁ α⇐ {A = B} {B = C} {C = D})
        ≈⟨ refl⟩∘⟨                  -- under e1
             (refl⟩∘⟨              -- under e2
               (≈-Term-trans
                 (≈-Term-trans (≈-Term-sym assoc)   -- e3 ∘ (e4 ∘ Y) → (e3 ∘ e4) ∘ Y
                   (≈-Term-trans (pentagon-flip-right ⟩∘⟨refl)  -- (e3 ∘ e4) → p1 ∘ (p2 ∘ p3)
                     (≈-Term-trans assoc                  -- (p1 ∘ (p2 ∘ p3)) ∘ Y → p1 ∘ ((p2 ∘ p3) ∘ Y)
                       (refl⟩∘⟨ assoc))))    -- p1 ∘ ((p2 ∘ p3) ∘ Y) → p1 ∘ (p2 ∘ (p3 ∘ Y))
                 (refl⟩∘⟨            -- under p1
                   (refl⟩∘⟨          -- under p2
                     (refl⟩∘⟨        -- under p3
                       (refl⟩∘⟨      -- under e5
                         (≈-Term-trans (≈-Term-sym assoc)  -- e6 ∘ (e7 ∘ Z) → (e6 ∘ e7) ∘ Z
                           (≈-Term-trans (α⇐∘id⊗α⇒-rewrite ⟩∘⟨refl)
                             (≈-Term-trans assoc
                               (refl⟩∘⟨ assoc)))))))))) ⟩
      (id {A = C} ⊗₁ α⇒ {A = B} {B = A} {C = D})
        ∘ (id ⊗₁ (σ {A = A} {B = B} ⊗₁ id {A = D}))
        ∘ (α⇒ {A = C} {B = A ⊗₀ B} {C = D})
        ∘ (α⇒ {A = C} {B = A} {C = B} ⊗₁ id {A = D})
        ∘ (α⇐ {A = C ⊗₀ A} {B = B} {C = D})
        ∘ (σ {A = A} {B = C} ⊗₁ id {A = B ⊗₀ D})
        ∘ (α⇒ {A = A ⊗₀ C} {B = B} {C = D})
        ∘ (α⇐ {A = A} {B = C} {C = B} ⊗₁ id {A = D})
        ∘ (α⇐ {A = A} {B = C ⊗₀ B} {C = D})
        ∘ (id ⊗₁ (σ {A = B} {B = C} ⊗₁ id {A = D}))
        ∘ (id ⊗₁ α⇐ {A = B} {B = C} {C = D})
        -- C: group p3 ∘ e5 ∘ q1 into a 3-element composition for collapse.
        ≈⟨ refl⟩∘⟨       -- under e1
             (refl⟩∘⟨   -- under e2
               (refl⟩∘⟨ -- under p1
                 (refl⟩∘⟨ -- under p2
                   (≈-Term-trans
                     (refl⟩∘⟨ (≈-Term-sym assoc))
                     (≈-Term-sym assoc))))) ⟩
      (id {A = C} ⊗₁ α⇒ {A = B} {B = A} {C = D})
        ∘ (id ⊗₁ (σ {A = A} {B = B} ⊗₁ id {A = D}))
        ∘ (α⇒ {A = C} {B = A ⊗₀ B} {C = D})
        ∘ (α⇒ {A = C} {B = A} {C = B} ⊗₁ id {A = D})
        ∘ ((α⇐ {A = C ⊗₀ A} {B = B} {C = D}
            ∘ (σ {A = A} {B = C} ⊗₁ id {A = B ⊗₀ D})
            ∘ (α⇒ {A = A ⊗₀ C} {B = B} {C = D}))
            ∘ (α⇐ {A = A} {B = C} {C = B} ⊗₁ id {A = D})
            ∘ (α⇐ {A = A} {B = C ⊗₀ B} {C = D})
            ∘ (id ⊗₁ (σ {A = B} {B = C} ⊗₁ id {A = D}))
            ∘ (id ⊗₁ α⇐ {A = B} {B = C} {C = D}))
        -- D: collapse the middle α⇐ ∘ (σ⊗id) ∘ α⇒ → ((σ⊗id_B) ⊗ id_D).
        ≈⟨ refl⟩∘⟨ (refl⟩∘⟨ (refl⟩∘⟨ (refl⟩∘⟨ (σ⊗id-collapse-middle ⟩∘⟨refl)))) ⟩
      (id {A = C} ⊗₁ α⇒ {A = B} {B = A} {C = D})
        ∘ (id ⊗₁ (σ {A = A} {B = B} ⊗₁ id {A = D}))
        ∘ (α⇒ {A = C} {B = A ⊗₀ B} {C = D})
        ∘ (α⇒ {A = C} {B = A} {C = B} ⊗₁ id {A = D})
        ∘ (((σ {A = A} {B = C} ⊗₁ id {A = B}) ⊗₁ id {A = D})
            ∘ (α⇐ {A = A} {B = C} {C = B} ⊗₁ id {A = D})
            ∘ (α⇐ {A = A} {B = C ⊗₀ B} {C = D})
            ∘ (id ⊗₁ (σ {A = B} {B = C} ⊗₁ id {A = D}))
            ∘ (id ⊗₁ α⇐ {A = B} {B = C} {C = D}))
        -- E: α-comm (sym) push e2 past p1; α⇐-comm push e8 past q3.
        ≈⟨ refl⟩∘⟨                  -- under e1
             (≈-Term-trans                       -- rewrite (a): push e2 past p1
               (≈-Term-trans (≈-Term-sym assoc)
                 (≈-Term-trans ((≈-Term-sym α-comm) ⟩∘⟨refl)
                   (≈-Term-trans assoc
                     ≈-Term-refl)))
               -- rewrite (b): navigate 5 levels, push e8 past q3
               (refl⟩∘⟨ (refl⟩∘⟨ (refl⟩∘⟨ (refl⟩∘⟨ (refl⟩∘⟨ (≈-Term-trans (≈-Term-sym assoc)
                           (≈-Term-trans (α⇐-comm ⟩∘⟨refl)
                             assoc))))))
               )) ⟩
      (id {A = C} ⊗₁ α⇒ {A = B} {B = A} {C = D})
        ∘ (α⇒ {A = C} {B = B ⊗₀ A} {C = D})
        ∘ ((id {A = C} ⊗₁ σ {A = A} {B = B}) ⊗₁ id {A = D})
        ∘ (α⇒ {A = C} {B = A} {C = B} ⊗₁ id {A = D})
        ∘ ((σ {A = A} {B = C} ⊗₁ id {A = B}) ⊗₁ id {A = D})
        ∘ (α⇐ {A = A} {B = C} {C = B} ⊗₁ id {A = D})
        ∘ ((id {A = A} ⊗₁ σ {A = B} {B = C}) ⊗₁ id {A = D})
        ∘ (α⇐ {A = A} {B = B ⊗₀ C} {C = D})
        ∘ (id {A = A} ⊗₁ α⇐ {A = B} {B = C} {C = D})
        -- F: hexagon-with-tail on pieces 3,4,5, then cancel α⇒⊗id ∘ α⇐⊗id.
        ≈⟨ refl⟩∘⟨                       -- under e1
             (refl⟩∘⟨                   -- under α⇒
               (≈-Term-trans
                 -- group pieces 3-4-5
                 (≈-Term-trans
                   (refl⟩∘⟨ (≈-Term-sym assoc))
                   (≈-Term-sym assoc))
                 -- hexagon-with-tail + cancel α⇒⊗id ∘ α⇐⊗id
                 (≈-Term-trans
                   ((hexagon-with-tail {A = A} {B = C} {C = B} {W = D}) ⟩∘⟨refl)
                   (≈-Term-trans assoc
                     (refl⟩∘⟨ (≈-Term-trans assoc
                         (refl⟩∘⟨ (≈-Term-trans (≈-Term-sym assoc)
                             (≈-Term-trans
                               ((≈-Term-trans (≈-Term-sym ⊗-∘-dist)
                                   (≈-Term-trans (⊗-resp-≈ α⇒∘α⇐≈id idˡ) id⊗id≈id)) ⟩∘⟨refl)
                               idˡ))))))))) ⟩
      (id {A = C} ⊗₁ α⇒ {A = B} {B = A} {C = D})
        ∘ (α⇒ {A = C} {B = B ⊗₀ A} {C = D})
        ∘ (α⇒ {A = C} {B = B} {C = A} ⊗₁ id {A = D})
        ∘ (σ {A = A} {B = C ⊗₀ B} ⊗₁ id {A = D})
        ∘ ((id {A = A} ⊗₁ σ {A = B} {B = C}) ⊗₁ id {A = D})
        ∘ (α⇐ {A = A} {B = B ⊗₀ C} {C = D})
        ∘ (id {A = A} ⊗₁ α⇐ {A = B} {B = C} {C = D})
        -- G: group top 3, apply pentagon, distribute.
        ≈⟨ ≈-Term-trans
             (≈-Term-trans (refl⟩∘⟨ (≈-Term-sym assoc))
               (≈-Term-sym assoc))
             (≈-Term-trans (pentagon ⟩∘⟨refl)
               assoc) ⟩
      (α⇒ {A = C} {B = B} {C = A ⊗₀ D})
        ∘ (α⇒ {A = C ⊗₀ B} {B = A} {C = D})
        ∘ (σ {A = A} {B = C ⊗₀ B} ⊗₁ id {A = D})
        ∘ ((id {A = A} ⊗₁ σ {A = B} {B = C}) ⊗₁ id {A = D})
        ∘ (α⇐ {A = A} {B = B ⊗₀ C} {C = D})
        ∘ (id {A = A} ⊗₁ α⇐ {A = B} {B = C} {C = D})
        -- H: α⇐-stack-from-pentagon at the bottom boundary.
        ≈⟨ refl⟩∘⟨    -- under α⇒_{C,B,A⊗D}
             (refl⟩∘⟨  -- under α⇒_{C⊗B,A,D}
               (refl⟩∘⟨  -- under σ⊗id
                 (refl⟩∘⟨  -- under (id⊗σ)⊗id
                   α⇐-stack-from-pentagon))) ⟩
      (α⇒ {A = C} {B = B} {C = A ⊗₀ D})
        ∘ (α⇒ {A = C ⊗₀ B} {B = A} {C = D})
        ∘ (σ {A = A} {B = C ⊗₀ B} ⊗₁ id {A = D})
        ∘ ((id {A = A} ⊗₁ σ {A = B} {B = C}) ⊗₁ id {A = D})
        ∘ (α⇒ {A = A} {B = B} {C = C} ⊗₁ id {A = D})
        ∘ (α⇐ {A = A ⊗₀ B} {B = C} {C = D})
        ∘ (α⇐ {A = A} {B = B} {C = C ⊗₀ D})
        -- I: factor the 3 (X ⊗ id_D) pieces into a single (inner-R ⊗ id_D).
        ≈⟨ refl⟩∘⟨  -- under α⇒_{C,B,A⊗D}
             (refl⟩∘⟨  -- under α⇒_{C⊗B,A,D}
               (≈-Term-trans
                 (≈-Term-trans (refl⟩∘⟨ (≈-Term-sym assoc))
                   (≈-Term-sym assoc))
                 (
                   -- merge (σ⊗id) ∘ (((id⊗σ)⊗id) ∘ (α⇒⊗id)) into (inner-R ⊗ id_D)
                   (≈-Term-trans
                     (refl⟩∘⟨ (≈-Term-trans (≈-Term-sym ⊗-∘-dist)
                         (⊗-resp-≈ ≈-Term-refl idˡ)))
                     (≈-Term-trans (≈-Term-sym ⊗-∘-dist)
                       (⊗-resp-≈ ≈-Term-refl idˡ))) ⟩∘⟨refl))) ⟩
      NF-R {A} {B} {C} {D} ∎

  --------------------------------------------------------------------------------
  -- RHS path: RHS-expanded reduces to the same NF-R via R-A … R-E.

  -- RHS after expanding σ-blocks (middle via id⊗σ-block-expand).
  RHS-expanded
    : ∀ {A B C D : ObjTerm}
    → HomTerm (A ⊗₀ (B ⊗₀ (C ⊗₀ D))) (C ⊗₀ (B ⊗₀ (A ⊗₀ D)))
  RHS-expanded {A} {B} {C} {D}
    = (α⇒ {A = C} {B = B} {C = A ⊗₀ D}
        ∘ (σ {A = B} {B = C} ⊗₁ id {A = A ⊗₀ D})
        ∘ α⇐ {A = B} {B = C} {C = A ⊗₀ D})
    ∘ ((id {A = B} ⊗₁ α⇒ {A = C} {B = A} {C = D})
        ∘ (id ⊗₁ (σ {A = A} {B = C} ⊗₁ id {A = D}))
        ∘ (id ⊗₁ α⇐ {A = A} {B = C} {C = D}))
    ∘ (α⇒ {A = B} {B = A} {C = C ⊗₀ D}
        ∘ (σ {A = A} {B = B} ⊗₁ id {A = C ⊗₀ D})
        ∘ α⇐ {A = A} {B = B} {C = C ⊗₀ D})

  RHS-to-expanded
    : ∀ {A B C D : ObjTerm}
    → σ-block {A = B} {B = C} {C = A ⊗₀ D}
        ∘ (id {A = B} ⊗₁ σ-block {A = A} {B = C} {C = D})
        ∘ σ-block {A = A} {B = B} {C = C ⊗₀ D}
      ≈Term RHS-expanded {A} {B} {C} {D}
  RHS-to-expanded =
    refl⟩∘⟨ (id⊗σ-block-expand ⟩∘⟨refl)

  -- Helper lemma: middleX ≈ inner-R.  Apply hexagon at the inner triple,
  -- cancel α⇐∘α⇒≈id, then σ-comm to re-bracket.
  middleX-eq-inner-R
    : ∀ {A B C : ObjTerm}
    → (σ {A = B} {B = C} ⊗₁ id {A = A})
        ∘ α⇐ {A = B} {B = C} {C = A}
        ∘ (id {A = B} ⊗₁ σ {A = A} {B = C})
        ∘ α⇒ {A = B} {B = A} {C = C}
        ∘ (σ {A = A} {B = B} ⊗₁ id {A = C})
      ≈Term
      σ {A = A} {B = C ⊗₀ B}
        ∘ (id {A = A} ⊗₁ σ {A = B} {B = C})
        ∘ α⇒ {A = A} {B = B} {C = C}
  middleX-eq-inner-R {A} {B} {C} =
    ≈-Term-trans
      (refl⟩∘⟨ (refl⟩∘⟨ hexagon))
      (≈-Term-trans
        (refl⟩∘⟨ (≈-Term-trans (≈-Term-sym assoc)
            (≈-Term-trans (α⇐∘α⇒≈id ⟩∘⟨refl)
              idˡ)))
        (≈-Term-trans
          (≈-Term-sym assoc)
          (≈-Term-trans
            ((≈-Term-sym σ∘[f⊗g]≈[g⊗f]∘σ) ⟩∘⟨refl)
            assoc)))

  -- RHS-expanded reduces to NF-R via the 5-step chain R-A … R-E:
  --   R-A: 4 assoc rotations into a flat 9-element right-associated chain.
  --   R-B: α⇐∘id⊗α⇒-rewrite at r3-r4, pentagon-flip-right at r6-r7.
  --   R-C: α⇐-comm to push r5, then cancel α⇐_{B,A⊗C,D} ∘ α⇒_{B,A⊗C,D} = id.
  --   R-D: (sym) α-comm at r2∘α⇒, α⇐-comm at α⇐_{B⊗A,C,D}∘r8.
  --   R-E: the 5 (X ⊗ id_D) pieces merge to (middleX ⊗ id_D) = (inner-R ⊗ id_D).
  RHS-to-NF-R : ∀ {A B C D : ObjTerm}
              → RHS-expanded {A} {B} {C} {D} ≈Term NF-R {A} {B} {C} {D}
  RHS-to-NF-R {A} {B} {C} {D} = begin
      RHS-expanded {A} {B} {C} {D}
        -- R-A: 4 assoc rotations (as step-A).
        ≈⟨ ≈-Term-trans assoc
             (≈-Term-trans (refl⟩∘⟨ assoc)
               (≈-Term-trans (refl⟩∘⟨ (refl⟩∘⟨ (refl⟩∘⟨ assoc)))
                 (refl⟩∘⟨ (refl⟩∘⟨ (refl⟩∘⟨ (refl⟩∘⟨ assoc)))))) ⟩
      (α⇒ {A = C} {B = B} {C = A ⊗₀ D})
        ∘ (σ {A = B} {B = C} ⊗₁ id {A = A ⊗₀ D})
        ∘ (α⇐ {A = B} {B = C} {C = A ⊗₀ D})
        ∘ (id {A = B} ⊗₁ α⇒ {A = C} {B = A} {C = D})
        ∘ (id ⊗₁ (σ {A = A} {B = C} ⊗₁ id {A = D}))
        ∘ (id ⊗₁ α⇐ {A = A} {B = C} {C = D})
        ∘ (α⇒ {A = B} {B = A} {C = C ⊗₀ D})
        ∘ (σ {A = A} {B = B} ⊗₁ id {A = C ⊗₀ D})
        ∘ (α⇐ {A = A} {B = B} {C = C ⊗₀ D})
        ≈⟨ refl⟩∘⟨                   -- under r1
             (refl⟩∘⟨                -- under r2
               (≈-Term-trans
                 (≈-Term-trans (≈-Term-sym assoc)
                   (≈-Term-trans (α⇐∘id⊗α⇒-rewrite ⟩∘⟨refl)
                     (≈-Term-trans assoc
                       (refl⟩∘⟨ assoc))))
                 -- navigate 4 levels to r6 ∘ r7, apply pentagon-flip-right
                 (refl⟩∘⟨    -- under α⇒_{B⊗C,A,D}
                   (refl⟩∘⟨  -- under (α⇐_{B,C,A}⊗id_D)
                     (refl⟩∘⟨  -- under α⇐_{B,C⊗A,D}
                       (refl⟩∘⟨  -- under r5
                         (≈-Term-trans (≈-Term-sym assoc)
                           (≈-Term-trans (pentagon-flip-right ⟩∘⟨refl)
                             (≈-Term-trans assoc
                               (refl⟩∘⟨ assoc)))))))))) ⟩
      (α⇒ {A = C} {B = B} {C = A ⊗₀ D})
        ∘ (σ {A = B} {B = C} ⊗₁ id {A = A ⊗₀ D})
        ∘ (α⇒ {A = B ⊗₀ C} {B = A} {C = D})
        ∘ (α⇐ {A = B} {B = C} {C = A} ⊗₁ id {A = D})
        ∘ (α⇐ {A = B} {B = C ⊗₀ A} {C = D})
        ∘ (id ⊗₁ (σ {A = A} {B = C} ⊗₁ id {A = D}))
        ∘ (α⇒ {A = B} {B = A ⊗₀ C} {C = D})
        ∘ (α⇒ {A = B} {B = A} {C = C} ⊗₁ id {A = D})
        ∘ (α⇐ {A = B ⊗₀ A} {B = C} {C = D})
        ∘ (σ {A = A} {B = B} ⊗₁ id {A = C ⊗₀ D})
        ∘ (α⇐ {A = A} {B = B} {C = C ⊗₀ D})
        ≈⟨ refl⟩∘⟨  -- under r1
             (refl⟩∘⟨  -- under r2
               (refl⟩∘⟨  -- under α⇒_{B⊗C,A,D}
                 (refl⟩∘⟨  -- under (α⇐_{B,C,A}⊗id_D)
                   (≈-Term-trans (≈-Term-sym assoc)
                     (≈-Term-trans (α⇐-comm ⟩∘⟨refl)
                       (≈-Term-trans assoc
                         (refl⟩∘⟨ (≈-Term-trans (≈-Term-sym assoc)
                             (≈-Term-trans (α⇐∘α⇒≈id ⟩∘⟨refl)
                               idˡ))))))))) ⟩
      (α⇒ {A = C} {B = B} {C = A ⊗₀ D})
        ∘ (σ {A = B} {B = C} ⊗₁ id {A = A ⊗₀ D})
        ∘ (α⇒ {A = B ⊗₀ C} {B = A} {C = D})
        ∘ (α⇐ {A = B} {B = C} {C = A} ⊗₁ id {A = D})
        ∘ ((id {A = B} ⊗₁ σ {A = A} {B = C}) ⊗₁ id {A = D})
        ∘ (α⇒ {A = B} {B = A} {C = C} ⊗₁ id {A = D})
        ∘ (α⇐ {A = B ⊗₀ A} {B = C} {C = D})
        ∘ (σ {A = A} {B = B} ⊗₁ id {A = C ⊗₀ D})
        ∘ (α⇐ {A = A} {B = B} {C = C ⊗₀ D})
        ≈⟨ refl⟩∘⟨              -- under r1
             (≈-Term-trans
               -- rewrite (a): r2 ∘ (α⇒ ∘ Y) → α⇒_{C⊗B,A,D} ∘ (((σ⊗id_A)⊗id_D) ∘ Y)
               (≈-Term-trans ((⊗-resp-≈ ≈-Term-refl (≈-Term-sym id⊗id≈id)) ⟩∘⟨refl)
                 (≈-Term-trans (≈-Term-sym assoc)
                   (≈-Term-trans ((≈-Term-sym α-comm) ⟩∘⟨refl)
                     assoc)))
               -- rewrite (b): navigate 5 levels, α⇐_{B⊗A,C,D} ∘ (r8 ∘ r9) →
               -- ((σ_{A,B}⊗id_C)⊗id_D) ∘ (α⇐_{A⊗B,C,D} ∘ r9)
               (refl⟩∘⟨ (refl⟩∘⟨ (refl⟩∘⟨ (refl⟩∘⟨ (refl⟩∘⟨ (≈-Term-trans (≈-Term-sym assoc)
                           (≈-Term-trans ((≈-Term-trans (refl⟩∘⟨ (⊗-resp-≈ ≈-Term-refl (≈-Term-sym id⊗id≈id)))
                               α⇐-comm) ⟩∘⟨refl)
                             assoc)))))))
               ) ⟩
      (α⇒ {A = C} {B = B} {C = A ⊗₀ D})
        ∘ (α⇒ {A = C ⊗₀ B} {B = A} {C = D})
        ∘ ((σ {A = B} {B = C} ⊗₁ id {A = A}) ⊗₁ id {A = D})
        ∘ (α⇐ {A = B} {B = C} {C = A} ⊗₁ id {A = D})
        ∘ ((id {A = B} ⊗₁ σ {A = A} {B = C}) ⊗₁ id {A = D})
        ∘ (α⇒ {A = B} {B = A} {C = C} ⊗₁ id {A = D})
        ∘ ((σ {A = A} {B = B} ⊗₁ id {A = C}) ⊗₁ id {A = D})
        ∘ (α⇐ {A = A ⊗₀ B} {B = C} {C = D})
        ∘ (α⇐ {A = A} {B = B} {C = C ⊗₀ D})
        -- R-E: group the 5 middle (X ⊗ id_D) pieces into (middleX ⊗ id_D)
        -- (each merge: sym ⊗-∘-dist + idˡ inside ⊗), then middleX-eq-inner-R.
        ≈⟨ refl⟩∘⟨  -- under α⇒_{C,B,A⊗D}
             (refl⟩∘⟨  -- under α⇒_{C⊗B,A,D}
               (≈-Term-trans
                 -- flatten p3 ∘ … ∘ p7 to a left-grouped prefix ∘ Y
                 (≈-Term-trans
                   (refl⟩∘⟨ (refl⟩∘⟨ (refl⟩∘⟨ (≈-Term-sym assoc))))
                   (≈-Term-trans
                     (refl⟩∘⟨ (refl⟩∘⟨ (≈-Term-sym assoc)))
                     (≈-Term-trans
                       (refl⟩∘⟨ (≈-Term-sym assoc))
                       (≈-Term-sym assoc))))
                 -- merge the prefix into (middleX ⊗ id_D), then middleX-eq-inner-R
                 ((≈-Term-trans
                     (refl⟩∘⟨ (refl⟩∘⟨ (refl⟩∘⟨ (≈-Term-trans (≈-Term-sym ⊗-∘-dist)
                             (⊗-resp-≈ ≈-Term-refl idˡ)))))
                     (≈-Term-trans
                       (refl⟩∘⟨ (refl⟩∘⟨ (≈-Term-trans (≈-Term-sym ⊗-∘-dist)
                             (⊗-resp-≈ ≈-Term-refl idˡ))))
                       (≈-Term-trans
                         (refl⟩∘⟨ (≈-Term-trans (≈-Term-sym ⊗-∘-dist)
                             (⊗-resp-≈ ≈-Term-refl idˡ)))
                         (≈-Term-trans
                           (≈-Term-trans (≈-Term-sym ⊗-∘-dist)
                             (⊗-resp-≈ ≈-Term-refl idˡ))
                           (⊗-resp-≈ middleX-eq-inner-R ≈-Term-refl))))) ⟩∘⟨refl))) ⟩
      NF-R {A} {B} {C} {D} ∎

  σ-block-hexagon-helper
    : ∀ {A B C D : ObjTerm}
    → (id {A = C} ⊗₁ σ-block {A = A} {B = B} {C = D})
        ∘ σ-block {A = A} {B = C} {C = B ⊗₀ D}
        ∘ (id {A = A} ⊗₁ σ-block {A = B} {B = C} {C = D})
      ≈Term
      σ-block {A = B} {B = C} {C = A ⊗₀ D}
        ∘ (id {A = B} ⊗₁ σ-block {A = A} {B = C} {C = D})
        ∘ σ-block {A = A} {B = B} {C = C ⊗₀ D}
  σ-block-hexagon-helper =
    ≈-Term-trans LHS-to-expanded
      (≈-Term-trans LHS-to-NF-R
        (≈-Term-trans (≈-Term-sym RHS-to-NF-R)
          (≈-Term-sym RHS-to-expanded)))

σ-block-hexagon
  : ∀ {A B C D : ObjTerm}
  → (id {A = C} ⊗₁ σ-block {A = A} {B = B} {C = D})
      ∘ σ-block {A = A} {B = C} {C = B ⊗₀ D}
      ∘ (id {A = A} ⊗₁ σ-block {A = B} {B = C} {C = D})
    ≈Term
    σ-block {A = B} {B = C} {C = A ⊗₀ D}
      ∘ (id {A = B} ⊗₁ σ-block {A = A} {B = C} {C = D})
      ∘ σ-block {A = A} {B = B} {C = C ⊗₀ D}
σ-block-hexagon = σ-block-hexagon-helper
