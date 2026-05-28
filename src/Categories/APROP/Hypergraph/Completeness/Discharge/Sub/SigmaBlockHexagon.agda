{-# OPTIONS --safe --with-K #-}

--------------------------------------------------------------------------------
-- σ-block algebra: σ-block-involutive, σ-block-natural{₁,₃},
-- hexagon₂ (dual hexagon, derived), and σ-block-hexagon (Yang-Baxter
-- braid at the σ-block level, derived).
--
-- ## Background
--
-- `permute (swap k k' p)` produces the WRAPPED pattern
--
--     σ-block = α⇒ ∘ (σ ⊗ id) ∘ α⇐    : A ⊗ (B ⊗ C) → B ⊗ (A ⊗ C)
--
-- which operates on the right-associated unflatten shape.
-- `FreeMonoidal.hexagon` targets the BARE σ.  To handle Yang-Baxter
-- cascades at the `permute` level (e.g. `fr-B-prep-swap` in
-- `Sub/YangBaxterClosure.agda.RealFinalResidual`), we lift the
-- standard algebra to the σ-block level.
--
-- ## Lemmas delivered (constructive, from FreeMonoidal axioms only)
--
--   * `σ-block`               — definition.
--   * `σ-block-involutive`    — σ-block ∘ σ-block ≈Term id.
--   * `σ-block-natural₃`      — σ-block ∘ (id ⊗ (id ⊗ f))
--                                ≈Term (id ⊗ (id ⊗ f)) ∘ σ-block.
--   * `σ-block-natural₁`      — σ-block ∘ (f ⊗ id)
--                                ≈Term (id ⊗ (f ⊗ id)) ∘ σ-block.
--   * `hexagon₂`              — dual hexagon at α⇐ level:
--                                σ ⊗ id ∘ α⇐ ∘ id ⊗ σ ≈ α⇐ ∘ σ ∘ α⇐.
--                                Derived from hexagon₁ + σ∘σ≈id +
--                                α⇒∘α⇐≈id.  (~75 LOC.)
--   * `σ-block-hexagon`       — Yang-Baxter braid at σ-block level:
--                                (id⊗σ-block) ∘ σ-block ∘ (id⊗σ-block) ≈Term
--                                σ-block ∘ (id⊗σ-block) ∘ σ-block,
--                                with the σ-blocks at appropriate
--                                4-object permutation positions.
--                                Derived from σ∘[f⊗g]≈[g⊗f]∘σ +
--                                hexagon + hexagon₂.
--
-- ## Derivation chain used:
--   σ∘σ≈id, σ∘[f⊗g]≈[g⊗f]∘σ, hexagon (= hexagon₁), α-comm,
--   α⇒∘α⇐≈id, α⇐∘α⇒≈id, ⊗-∘-dist, id⊗id≈id, idˡ, idʳ, assoc,
--   ∘-resp-≈, ⊗-resp-≈, ≈-Term-{refl,sym,trans}.
--
-- ## File is `--safe --with-K`-clean.  No new postulates.
--------------------------------------------------------------------------------

open import Categories.APROP
open import Categories.APROP.Hypergraph.Solver.Signature using (APROPSignatureDec)

module Categories.APROP.Hypergraph.Completeness.Discharge.Sub.SigmaBlockHexagon
  (sig-dec : APROPSignatureDec) where

open APROPSignatureDec sig-dec using (sig)
open APROP sig

open import Categories.Category using (Category)

private
  module FM = Category FreeMonoidal

open FM.HomReasoning

--------------------------------------------------------------------------------
-- ## σ-block definition.
--
-- Matches what `permute (swap k k' p)` produces (modulo the
-- (id ⊗₁ (id ⊗₁ permute p)) outer prefix).

σ-block : ∀ {A B C : ObjTerm} → HomTerm (A ⊗₀ (B ⊗₀ C)) (B ⊗₀ (A ⊗₀ C))
σ-block = α⇒ ∘ (σ ⊗₁ id) ∘ α⇐

--------------------------------------------------------------------------------
-- ## σ-block-involutive: σ-block ∘ σ-block ≈ id.

σ-block-involutive
  : ∀ {A B C : ObjTerm}
  → (α⇒ {A = A} {B = B} {C = C} ∘ (σ ⊗₁ id) ∘ α⇐ {A = B} {B = A} {C = C})
      ∘ (α⇒ {A = B} {B = A} {C = C} ∘ (σ ⊗₁ id) ∘ α⇐ {A = A} {B = B} {C = C})
    ≈Term id
σ-block-involutive {A} {B} {C} =
  let σ-AB = σ {A = A} {B = B}
      σ-BA = σ {A = B} {B = A}
      α⇒-ABC = α⇒ {A = A} {B = B} {C = C}
      α⇐-ABC = α⇐ {A = A} {B = B} {C = C}
      α⇒-BAC = α⇒ {A = B} {B = A} {C = C}
      α⇐-BAC = α⇐ {A = B} {B = A} {C = C}
  in begin
       (α⇒-ABC ∘ (σ-BA ⊗₁ id) ∘ α⇐-BAC)
         ∘ (α⇒-BAC ∘ (σ-AB ⊗₁ id) ∘ α⇐-ABC)
         ≈⟨ assoc ⟩
       α⇒-ABC ∘ ((σ-BA ⊗₁ id) ∘ α⇐-BAC)
         ∘ (α⇒-BAC ∘ (σ-AB ⊗₁ id) ∘ α⇐-ABC)
         ≈⟨ ∘-resp-≈ ≈-Term-refl assoc ⟩
       α⇒-ABC ∘ (σ-BA ⊗₁ id) ∘ (α⇐-BAC ∘ α⇒-BAC ∘ (σ-AB ⊗₁ id) ∘ α⇐-ABC)
         ≈⟨ ∘-resp-≈ ≈-Term-refl
              (∘-resp-≈ ≈-Term-refl
                (≈-Term-trans (≈-Term-sym assoc)
                              (∘-resp-≈ α⇐∘α⇒≈id ≈-Term-refl))) ⟩
       α⇒-ABC ∘ (σ-BA ⊗₁ id) ∘ id ∘ (σ-AB ⊗₁ id) ∘ α⇐-ABC
         ≈⟨ ∘-resp-≈ ≈-Term-refl (∘-resp-≈ ≈-Term-refl idˡ) ⟩
       α⇒-ABC ∘ (σ-BA ⊗₁ id) ∘ ((σ-AB ⊗₁ id) ∘ α⇐-ABC)
         ≈⟨ ∘-resp-≈ ≈-Term-refl (≈-Term-sym assoc) ⟩
       α⇒-ABC ∘ ((σ-BA ⊗₁ id) ∘ (σ-AB ⊗₁ id)) ∘ α⇐-ABC
         ≈⟨ ∘-resp-≈ ≈-Term-refl
              (∘-resp-≈ (≈-Term-trans (≈-Term-sym ⊗-∘-dist)
                          (≈-Term-trans (⊗-resp-≈ σ∘σ≈id idˡ)
                                        id⊗id≈id))
                       ≈-Term-refl) ⟩
       α⇒-ABC ∘ id ∘ α⇐-ABC
         ≈⟨ ∘-resp-≈ ≈-Term-refl idˡ ⟩
       α⇒-ABC ∘ α⇐-ABC
         ≈⟨ α⇒∘α⇐≈id ⟩
       id
     ∎

--------------------------------------------------------------------------------
-- ## α⇐-comm: dual associator commutativity.
--
-- α⇐ ∘ (h ⊗ (i ⊗ j)) ≈Term ((h ⊗ i) ⊗ j) ∘ α⇐.

private
  α⇐-comm
    : ∀ {a b c d e g : ObjTerm}
        {h : HomTerm a d} {i : HomTerm b e} {j : HomTerm c g}
    → α⇐ ∘ (h ⊗₁ (i ⊗₁ j)) ≈Term ((h ⊗₁ i) ⊗₁ j) ∘ α⇐
  α⇐-comm {h = h} {i} {j} = begin
    α⇐ ∘ (h ⊗₁ (i ⊗₁ j))
      ≈⟨ ≈-Term-sym idʳ ⟩
    (α⇐ ∘ (h ⊗₁ (i ⊗₁ j))) ∘ id
      ≈⟨ ∘-resp-≈ ≈-Term-refl (≈-Term-sym α⇒∘α⇐≈id) ⟩
    (α⇐ ∘ (h ⊗₁ (i ⊗₁ j))) ∘ (α⇒ ∘ α⇐)
      ≈⟨ assoc ⟩
    α⇐ ∘ ((h ⊗₁ (i ⊗₁ j)) ∘ (α⇒ ∘ α⇐))
      ≈⟨ ∘-resp-≈ ≈-Term-refl (≈-Term-sym assoc) ⟩
    α⇐ ∘ ((h ⊗₁ (i ⊗₁ j)) ∘ α⇒) ∘ α⇐
      ≈⟨ ∘-resp-≈ ≈-Term-refl (∘-resp-≈ (≈-Term-sym α-comm) ≈-Term-refl) ⟩
    α⇐ ∘ (α⇒ ∘ ((h ⊗₁ i) ⊗₁ j)) ∘ α⇐
      ≈⟨ ∘-resp-≈ ≈-Term-refl assoc ⟩
    α⇐ ∘ α⇒ ∘ (((h ⊗₁ i) ⊗₁ j) ∘ α⇐)
      ≈⟨ ≈-Term-sym assoc ⟩
    (α⇐ ∘ α⇒) ∘ (((h ⊗₁ i) ⊗₁ j) ∘ α⇐)
      ≈⟨ ∘-resp-≈ α⇐∘α⇒≈id ≈-Term-refl ⟩
    id ∘ (((h ⊗₁ i) ⊗₁ j) ∘ α⇐)
      ≈⟨ idˡ ⟩
    ((h ⊗₁ i) ⊗₁ j) ∘ α⇐
      ∎

--------------------------------------------------------------------------------
-- ## σ-block-natural₃: σ-block is natural in the third argument.
--
-- σ-block ∘ (id ⊗₁ (id ⊗₁ f)) ≈Term (id ⊗₁ (id ⊗₁ f)) ∘ σ-block

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
            ≈⟨ ∘-resp-≈ ≈-Term-refl assoc ⟩
          α⇒ ∘ (σ ⊗₁ id) ∘ (α⇐ ∘ (id ⊗₁ (id ⊗₁ f)))
            ≈⟨ ∘-resp-≈ ≈-Term-refl (∘-resp-≈ ≈-Term-refl α⇐-comm) ⟩
          α⇒ ∘ (σ ⊗₁ id) ∘ (((id ⊗₁ id) ⊗₁ f) ∘ α⇐)
            ≈⟨ ∘-resp-≈ ≈-Term-refl (≈-Term-sym assoc) ⟩
          α⇒ ∘ ((σ ⊗₁ id) ∘ ((id ⊗₁ id) ⊗₁ f)) ∘ α⇐
            ≈⟨ ∘-resp-≈ ≈-Term-refl
                 (∘-resp-≈ (≈-Term-trans (≈-Term-sym ⊗-∘-dist)
                            (⊗-resp-≈ (≈-Term-trans (∘-resp-≈ ≈-Term-refl id⊗id≈id) idʳ)
                                      idˡ))
                          ≈-Term-refl) ⟩
          α⇒ ∘ (σ ⊗₁ f) ∘ α⇐
        ∎
      rhs→common =
        begin
          (id ⊗₁ (id ⊗₁ f)) ∘ (α⇒ ∘ (σ ⊗₁ id) ∘ α⇐)
            ≈⟨ ≈-Term-sym assoc ⟩
          ((id ⊗₁ (id ⊗₁ f)) ∘ α⇒) ∘ ((σ ⊗₁ id) ∘ α⇐)
            ≈⟨ ∘-resp-≈ (≈-Term-sym α-comm) ≈-Term-refl ⟩
          (α⇒ ∘ ((id ⊗₁ id) ⊗₁ f)) ∘ ((σ ⊗₁ id) ∘ α⇐)
            ≈⟨ assoc ⟩
          α⇒ ∘ (((id ⊗₁ id) ⊗₁ f) ∘ ((σ ⊗₁ id) ∘ α⇐))
            ≈⟨ ∘-resp-≈ ≈-Term-refl (≈-Term-sym assoc) ⟩
          α⇒ ∘ ((((id ⊗₁ id) ⊗₁ f)) ∘ (σ ⊗₁ id)) ∘ α⇐
            ≈⟨ ∘-resp-≈ ≈-Term-refl
                 (∘-resp-≈ (≈-Term-trans (≈-Term-sym ⊗-∘-dist)
                            (⊗-resp-≈ (≈-Term-trans (∘-resp-≈ id⊗id≈id ≈-Term-refl) idˡ)
                                      idʳ))
                          ≈-Term-refl) ⟩
          α⇒ ∘ (σ ⊗₁ f) ∘ α⇐
        ∎
  in ≈-Term-trans lhs→common (≈-Term-sym rhs→common)

--------------------------------------------------------------------------------
-- ## σ-block-natural₁: σ-block is natural in the first argument (slot 1).
--
-- σ-block ∘ (f ⊗₁ id) ≈Term (id ⊗₁ (f ⊗₁ id)) ∘ σ-block
--
-- At type: A⊗(B⊗C) → B⊗(A'⊗C) where f : A → A'.
--
-- (Used in σ-block-hexagon to push f through σ.)

-- f : A → A', σ-block_{A',B,C} on LHS uses σ_{A',B}.
-- σ-block_{A,B,C} on RHS uses σ_{A,B}.
-- σ-block = α⇒ ∘ (σ ⊗ id) ∘ α⇐ goes A⊗(B⊗C) → B⊗(A⊗C).
-- Decomposition by right-associativity of ∘:
--   α⇒ {B,A,C} ∘ ((σ {A,B}) ⊗ id) ∘ α⇐ {A,B,C}
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
            ≈⟨ ∘-resp-≈ ≈-Term-refl assoc ⟩
          α⇒ ∘ (σ ⊗₁ id) ∘ (α⇐ ∘ (f ⊗₁ id))
            ≈⟨ ∘-resp-≈ ≈-Term-refl
                 (∘-resp-≈ ≈-Term-refl
                   (≈-Term-trans
                     (∘-resp-≈ ≈-Term-refl
                       (⊗-resp-≈ ≈-Term-refl (≈-Term-sym id⊗id≈id)))
                     α⇐-comm)) ⟩
          α⇒ ∘ (σ ⊗₁ id) ∘ (((f ⊗₁ id) ⊗₁ id) ∘ α⇐)
            ≈⟨ ∘-resp-≈ ≈-Term-refl (≈-Term-sym assoc) ⟩
          α⇒ ∘ ((σ ⊗₁ id) ∘ ((f ⊗₁ id) ⊗₁ id)) ∘ α⇐
            ≈⟨ ∘-resp-≈ ≈-Term-refl
                 (∘-resp-≈ (≈-Term-trans (≈-Term-sym ⊗-∘-dist)
                            (⊗-resp-≈ σ∘[f⊗g]≈[g⊗f]∘σ idˡ))
                          ≈-Term-refl) ⟩
          α⇒ ∘ (((id ⊗₁ f) ∘ σ) ⊗₁ id) ∘ α⇐
            ≈⟨ ∘-resp-≈ ≈-Term-refl
                 (∘-resp-≈ (≈-Term-trans
                              (⊗-resp-≈ ≈-Term-refl (≈-Term-sym idˡ))
                              ⊗-∘-dist)
                          ≈-Term-refl) ⟩
          α⇒ ∘ (((id ⊗₁ f) ⊗₁ id) ∘ ((σ ⊗₁ id))) ∘ α⇐
            ≈⟨ ∘-resp-≈ ≈-Term-refl assoc ⟩
          α⇒ ∘ ((id ⊗₁ f) ⊗₁ id) ∘ (σ ⊗₁ id) ∘ α⇐
            ≈⟨ ≈-Term-sym assoc ⟩
          (α⇒ ∘ ((id ⊗₁ f) ⊗₁ id)) ∘ ((σ ⊗₁ id) ∘ α⇐)
            ≈⟨ ∘-resp-≈ α-comm ≈-Term-refl ⟩
          ((id ⊗₁ (f ⊗₁ id)) ∘ α⇒) ∘ ((σ ⊗₁ id) ∘ α⇐)
            ≈⟨ assoc ⟩
          (id ⊗₁ (f ⊗₁ id)) ∘ (α⇒ ∘ (σ ⊗₁ id) ∘ α⇐)
        ∎
  in lhs→common

--------------------------------------------------------------------------------
-- ## hexagon₂: the dual hexagon at the α⇐ level.
--
-- The standard hexagon (axiom):
--   id ⊗ σ ∘ α⇒ ∘ σ ⊗ id ≈ α⇒ ∘ σ ∘ α⇒
-- at type (A⊗B)⊗C → B⊗(C⊗A).
--
-- The DUAL hexagon (derived):
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
        ≈⟨ ∘-resp-≈ ≈-Term-refl assoc ⟩
      (id ⊗₁ σ) ∘ α⇒ ∘ ((σ ⊗₁ id)
        ∘ ((σ ⊗₁ id) ∘ α⇐ ∘ (id ⊗₁ σ)))
        ≈⟨ ∘-resp-≈ ≈-Term-refl (∘-resp-≈ ≈-Term-refl (≈-Term-sym assoc)) ⟩
      (id ⊗₁ σ) ∘ α⇒ ∘ ((σ ⊗₁ id) ∘ (σ ⊗₁ id))
        ∘ α⇐ ∘ (id ⊗₁ σ)
        ≈⟨ ∘-resp-≈ ≈-Term-refl (∘-resp-≈ ≈-Term-refl (∘-resp-≈
              (≈-Term-trans (≈-Term-sym ⊗-∘-dist)
                            (≈-Term-trans (⊗-resp-≈ σ∘σ≈id idˡ) id⊗id≈id))
              ≈-Term-refl)) ⟩
      (id ⊗₁ σ) ∘ α⇒ ∘ id ∘ α⇐ ∘ (id ⊗₁ σ)
        ≈⟨ ∘-resp-≈ ≈-Term-refl (∘-resp-≈ ≈-Term-refl idˡ) ⟩
      (id ⊗₁ σ) ∘ α⇒ ∘ (α⇐ ∘ (id ⊗₁ σ))
        ≈⟨ ∘-resp-≈ ≈-Term-refl (≈-Term-sym assoc) ⟩
      (id ⊗₁ σ) ∘ (α⇒ ∘ α⇐) ∘ (id ⊗₁ σ)
        ≈⟨ ∘-resp-≈ ≈-Term-refl (∘-resp-≈ α⇒∘α⇐≈id ≈-Term-refl) ⟩
      (id ⊗₁ σ) ∘ id ∘ (id ⊗₁ σ)
        ≈⟨ ∘-resp-≈ ≈-Term-refl idˡ ⟩
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
        ≈⟨ ∘-resp-≈ ≈-Term-refl assoc ⟩
      α⇒ ∘ σ ∘ (α⇒ ∘ (α⇐ ∘ σ ∘ α⇐))
        ≈⟨ ∘-resp-≈ ≈-Term-refl (∘-resp-≈ ≈-Term-refl (≈-Term-sym assoc)) ⟩
      α⇒ ∘ σ ∘ ((α⇒ ∘ α⇐) ∘ σ ∘ α⇐)
        ≈⟨ ∘-resp-≈ ≈-Term-refl (∘-resp-≈ ≈-Term-refl (∘-resp-≈ α⇒∘α⇐≈id ≈-Term-refl)) ⟩
      α⇒ ∘ σ ∘ (id ∘ σ ∘ α⇐)
        ≈⟨ ∘-resp-≈ ≈-Term-refl (∘-resp-≈ ≈-Term-refl idˡ) ⟩
      α⇒ ∘ σ ∘ (σ ∘ α⇐)
        ≈⟨ ∘-resp-≈ ≈-Term-refl (≈-Term-sym assoc) ⟩
      α⇒ ∘ (σ ∘ σ) ∘ α⇐
        ≈⟨ ∘-resp-≈ ≈-Term-refl (∘-resp-≈ σ∘σ≈id ≈-Term-refl) ⟩
      α⇒ ∘ id ∘ α⇐
        ≈⟨ ∘-resp-≈ ≈-Term-refl idˡ ⟩
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
        ≈⟨ ∘-resp-≈ ≈-Term-refl assoc ⟩
      (σ ⊗₁ id) ∘ α⇐ ∘ ((id ⊗₁ σ)
        ∘ ((id ⊗₁ σ) ∘ α⇒ ∘ (σ ⊗₁ id)))
        ≈⟨ ∘-resp-≈ ≈-Term-refl (∘-resp-≈ ≈-Term-refl (≈-Term-sym assoc)) ⟩
      (σ ⊗₁ id) ∘ α⇐ ∘ ((id ⊗₁ σ) ∘ (id ⊗₁ σ))
        ∘ α⇒ ∘ (σ ⊗₁ id)
        ≈⟨ ∘-resp-≈ ≈-Term-refl (∘-resp-≈ ≈-Term-refl (∘-resp-≈
              (≈-Term-trans (≈-Term-sym ⊗-∘-dist)
                            (≈-Term-trans (⊗-resp-≈ idˡ σ∘σ≈id) id⊗id≈id))
              ≈-Term-refl)) ⟩
      (σ ⊗₁ id) ∘ α⇐ ∘ id ∘ α⇒ ∘ (σ ⊗₁ id)
        ≈⟨ ∘-resp-≈ ≈-Term-refl (∘-resp-≈ ≈-Term-refl idˡ) ⟩
      (σ ⊗₁ id) ∘ α⇐ ∘ (α⇒ ∘ (σ ⊗₁ id))
        ≈⟨ ∘-resp-≈ ≈-Term-refl (≈-Term-sym assoc) ⟩
      (σ ⊗₁ id) ∘ (α⇐ ∘ α⇒) ∘ (σ ⊗₁ id)
        ≈⟨ ∘-resp-≈ ≈-Term-refl (∘-resp-≈ α⇐∘α⇒≈id ≈-Term-refl) ⟩
      (σ ⊗₁ id) ∘ id ∘ (σ ⊗₁ id)
        ≈⟨ ∘-resp-≈ ≈-Term-refl idˡ ⟩
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
      ≈⟨ ∘-resp-≈ ≈-Term-refl (≈-Term-sym h₁R∘h₂R≈id) ⟩
    h₂L ∘ (h₁R ∘ h₂R)
      ≈⟨ ∘-resp-≈ ≈-Term-refl (∘-resp-≈ (≈-Term-sym hexagon) ≈-Term-refl) ⟩
    h₂L ∘ (h₁L ∘ h₂R)
      ≈⟨ ≈-Term-sym assoc ⟩
    (h₂L ∘ h₁L) ∘ h₂R
      ≈⟨ ∘-resp-≈ h₂L∘h₁L≈id ≈-Term-refl ⟩
    id ∘ h₂R
      ≈⟨ idˡ ⟩
    h₂R
    ∎

--------------------------------------------------------------------------------
-- ## Helpers for σ-block-hexagon: pentagon-shifted identities.
--
-- We derive a few useful identities from pentagon:
--   `pentagon-flip-right`: (id ⊗ α⇐) ∘ α⇒ ≈ α⇒ ∘ (α⇒ ⊗ id) ∘ α⇐.
--   `pentagon-flip-left`:  α⇒ ∘ (α⇐ ⊗ id) ≈ (id ⊗ α⇒) ∘ α⇒ ∘ α⇐.
--   `pentagon-α⇒α⇒-eq`:    α⇒_{P,Q,R⊗S} ∘ α⇒_{P⊗Q,R,S} ≈ ... (= pentagon).

private
  -- pentagon-flip-right: (id_P ⊗ α⇐_{Q,R,S}) ∘ α⇒_{P,Q,R⊗S}
  --                    ≈ α⇒_{P,Q⊗R,S} ∘ (α⇒_{P,Q,R} ⊗ id_S) ∘ α⇐_{P⊗Q,R,S}.
  --
  -- Derivation: pre-compose pentagon with (id⊗α⇐) on left, post-compose
  -- with α⇐_{P⊗Q,R,S} on right.
  pentagon-flip-right
    : ∀ {P Q R S : ObjTerm}
    → (id {A = P} ⊗₁ α⇐ {A = Q} {B = R} {C = S})
        ∘ α⇒ {A = P} {B = Q} {C = R ⊗₀ S}
      ≈Term α⇒ {A = P} {B = Q ⊗₀ R} {C = S}
              ∘ (α⇒ {A = P} {B = Q} {C = R} ⊗₁ id {A = S})
              ∘ α⇐ {A = P ⊗₀ Q} {B = R} {C = S}
  pentagon-flip-right {P} {Q} {R} {S} =
    begin
      (id ⊗₁ α⇐) ∘ α⇒
        -- Sandwich α⇒ with α⇒ ∘ α⇐ ≈ id on the right.
        ≈⟨ ≈-Term-sym idʳ ⟩
      ((id ⊗₁ α⇐) ∘ α⇒) ∘ id
        ≈⟨ ∘-resp-≈ ≈-Term-refl (≈-Term-sym α⇒∘α⇐≈id) ⟩
      ((id ⊗₁ α⇐) ∘ α⇒) ∘ (α⇒ ∘ α⇐)
        ≈⟨ assoc ⟩
      (id ⊗₁ α⇐) ∘ (α⇒ ∘ (α⇒ ∘ α⇐))
        ≈⟨ ∘-resp-≈ ≈-Term-refl (≈-Term-sym assoc) ⟩
      (id ⊗₁ α⇐) ∘ ((α⇒ ∘ α⇒) ∘ α⇐)
        -- Use pentagon: α⇒ ∘ α⇒ ≈ (id ⊗ α⇒) ∘ α⇒ ∘ (α⇒ ⊗ id).
        ≈⟨ ∘-resp-≈ ≈-Term-refl (∘-resp-≈ (≈-Term-sym pentagon) ≈-Term-refl) ⟩
      (id ⊗₁ α⇐) ∘ (((id ⊗₁ α⇒) ∘ α⇒ ∘ (α⇒ ⊗₁ id)) ∘ α⇐)
        ≈⟨ ∘-resp-≈ ≈-Term-refl assoc ⟩
      (id ⊗₁ α⇐) ∘ ((id ⊗₁ α⇒) ∘ ((α⇒ ∘ (α⇒ ⊗₁ id)) ∘ α⇐))
        ≈⟨ ≈-Term-sym assoc ⟩
      ((id ⊗₁ α⇐) ∘ (id ⊗₁ α⇒)) ∘ ((α⇒ ∘ (α⇒ ⊗₁ id)) ∘ α⇐)
        ≈⟨ ∘-resp-≈
            (≈-Term-trans (≈-Term-sym ⊗-∘-dist)
              (≈-Term-trans (⊗-resp-≈ idˡ α⇐∘α⇒≈id) id⊗id≈id))
            ≈-Term-refl ⟩
      id ∘ ((α⇒ ∘ (α⇒ ⊗₁ id)) ∘ α⇐)
        ≈⟨ idˡ ⟩
      (α⇒ ∘ (α⇒ ⊗₁ id)) ∘ α⇐
        ≈⟨ assoc ⟩
      α⇒ ∘ ((α⇒ ⊗₁ id) ∘ α⇐)
    ∎

  -- (pentagon-flip-left omitted; we can derive it via ≈-Term-sym of
  -- pentagon-flip-right when needed.)

--------------------------------------------------------------------------------
-- ## More pentagon-shifted helpers.
--
-- We add a few more α-coherence helpers needed for σ-block-hexagon.

private
  -- pentagon-flip-right-sym: α⇒_{P,Q⊗R,S} ∘ (α⇒_{P,Q,R} ⊗ id_S) ∘ α⇐_{P⊗Q,R,S}
  --                       ≈ (id_P ⊗ α⇐_{Q,R,S}) ∘ α⇒_{P,Q,R⊗S}.
  pentagon-flip-right-sym
    : ∀ {P Q R S : ObjTerm}
    → α⇒ {A = P} {B = Q ⊗₀ R} {C = S}
        ∘ (α⇒ {A = P} {B = Q} {C = R} ⊗₁ id {A = S})
        ∘ α⇐ {A = P ⊗₀ Q} {B = R} {C = S}
      ≈Term (id {A = P} ⊗₁ α⇐ {A = Q} {B = R} {C = S})
              ∘ α⇒ {A = P} {B = Q} {C = R ⊗₀ S}
  pentagon-flip-right-sym = ≈-Term-sym pentagon-flip-right

  -- pentagon-flip-α⇒-inside-tensor: (α⇒_{P,Q,R} ⊗ id_S) ∘ α⇐_{P⊗Q,R,S}
  --                              ≈ α⇐_{P,Q⊗R,S} ∘ (id_P ⊗ α⇐_{Q,R,S}) ∘ α⇒_{P,Q,R⊗S}.
  --
  -- Derivation: pre-compose pentagon-flip-right with α⇐ on the left,
  -- yielding α⇐ ∘ (id ⊗ α⇐) ∘ α⇒ ≈ α⇐ ∘ α⇒ ∘ (α⇒ ⊗ id) ∘ α⇐ ≈ (α⇒ ⊗ id) ∘ α⇐.
  -- Now take ≈-Term-sym.
  pentagon-flip-α⇒-inside-tensor
    : ∀ {P Q R S : ObjTerm}
    → (α⇒ {A = P} {B = Q} {C = R} ⊗₁ id {A = S})
        ∘ α⇐ {A = P ⊗₀ Q} {B = R} {C = S}
      ≈Term α⇐ {A = P} {B = Q ⊗₀ R} {C = S}
              ∘ (id {A = P} ⊗₁ α⇐ {A = Q} {B = R} {C = S})
              ∘ α⇒ {A = P} {B = Q} {C = R ⊗₀ S}
  pentagon-flip-α⇒-inside-tensor {P} {Q} {R} {S} =
    ≈-Term-sym (begin
      α⇐ ∘ (id ⊗₁ α⇐) ∘ α⇒
        ≈⟨ ∘-resp-≈ ≈-Term-refl pentagon-flip-right ⟩
      α⇐ ∘ (α⇒ ∘ (α⇒ ⊗₁ id) ∘ α⇐)
        ≈⟨ ≈-Term-sym assoc ⟩
      (α⇐ ∘ α⇒) ∘ ((α⇒ ⊗₁ id) ∘ α⇐)
        ≈⟨ ∘-resp-≈ α⇐∘α⇒≈id ≈-Term-refl ⟩
      id ∘ ((α⇒ ⊗₁ id) ∘ α⇐)
        ≈⟨ idˡ ⟩
      (α⇒ ⊗₁ id) ∘ α⇐
    ∎)

--------------------------------------------------------------------------------
-- ## α⇐-flip-shifted: a related α-coherence lemma.
--
-- α⇐_{P,Q,R⊗S} ∘ (id_P ⊗ α⇒_{Q,R,S})
--   ≈ α⇒_{P⊗Q,R,S} ∘ (α⇐_{P,Q,R} ⊗ id_S) ∘ α⇐_{P,Q⊗R,S}.

private
  α⇐∘id⊗α⇒-rewrite
    : ∀ {P Q R S : ObjTerm}
    → α⇐ {A = P} {B = Q} {C = R ⊗₀ S}
        ∘ (id {A = P} ⊗₁ α⇒ {A = Q} {B = R} {C = S})
      ≈Term α⇒ {A = P ⊗₀ Q} {B = R} {C = S}
              ∘ (α⇐ {A = P} {B = Q} {C = R} ⊗₁ id {A = S})
              ∘ α⇐ {A = P} {B = Q ⊗₀ R} {C = S}
  α⇐∘id⊗α⇒-rewrite {P} {Q} {R} {S} =
    -- From pentagon: (id ⊗ α⇒) ∘ α⇒ ∘ (α⇒ ⊗ id) ≈ α⇒ ∘ α⇒.
    -- I.e., (id_P ⊗ α⇒_{Q,R,S}) ∘ α⇒_{P,Q⊗R,S} ∘ (α⇒_{P,Q,R} ⊗ id_S)
    --     ≈ α⇒_{P,Q,R⊗S} ∘ α⇒_{P⊗Q,R,S}.
    -- Pre-compose with α⇐_{P,Q,R⊗S} on the left:
    --   α⇐ ∘ (id ⊗ α⇒) ∘ α⇒ ∘ (α⇒ ⊗ id) ≈ α⇐ ∘ α⇒ ∘ α⇒ = α⇒.
    -- Post-compose with (α⇐ ⊗ id) ∘ α⇐ on the right:
    --   α⇐ ∘ (id ⊗ α⇒) ∘ α⇒ ∘ (α⇒ ⊗ id) ∘ (α⇐ ⊗ id) ∘ α⇐
    --     ≈ α⇐ ∘ (id ⊗ α⇒) ∘ α⇒ ∘ id ∘ α⇐ ≈ α⇐ ∘ (id ⊗ α⇒) ∘ α⇒ ∘ α⇐
    --     ≈ α⇐ ∘ (id ⊗ α⇒)  (using α⇒ ∘ α⇐ ≈ id).
    -- Also = α⇒ ∘ (α⇐ ⊗ id) ∘ α⇐.
    -- So α⇐ ∘ (id ⊗ α⇒) ≈ α⇒ ∘ (α⇐ ⊗ id) ∘ α⇐.
    begin
      α⇐ ∘ (id ⊗₁ α⇒)
        ≈⟨ ≈-Term-sym idʳ ⟩
      (α⇐ ∘ (id ⊗₁ α⇒)) ∘ id
        ≈⟨ ∘-resp-≈ ≈-Term-refl (≈-Term-sym α⇒∘α⇐≈id) ⟩
      (α⇐ ∘ (id ⊗₁ α⇒)) ∘ (α⇒ ∘ α⇐)
        ≈⟨ assoc ⟩
      α⇐ ∘ ((id ⊗₁ α⇒) ∘ (α⇒ ∘ α⇐))
        ≈⟨ ∘-resp-≈ ≈-Term-refl (≈-Term-sym assoc) ⟩
      α⇐ ∘ (((id ⊗₁ α⇒) ∘ α⇒) ∘ α⇐)
        -- pentagon: (id ⊗ α⇒) ∘ α⇒ ∘ (α⇒ ⊗ id) ≈ α⇒ ∘ α⇒.
        -- So (id ⊗ α⇒) ∘ α⇒ ≈ α⇒ ∘ α⇒ ∘ (α⇐ ⊗ id).
        ≈⟨ ∘-resp-≈ ≈-Term-refl
            (∘-resp-≈
              (begin
                (id ⊗₁ α⇒) ∘ α⇒
                  ≈⟨ ≈-Term-sym idʳ ⟩
                ((id ⊗₁ α⇒) ∘ α⇒) ∘ id
                  ≈⟨ ∘-resp-≈ ≈-Term-refl
                      (≈-Term-sym
                        (≈-Term-trans (≈-Term-sym ⊗-∘-dist)
                          (≈-Term-trans (⊗-resp-≈ α⇒∘α⇐≈id idˡ) id⊗id≈id))) ⟩
                ((id ⊗₁ α⇒) ∘ α⇒) ∘ ((α⇒ ⊗₁ id) ∘ (α⇐ ⊗₁ id))
                  ≈⟨ ≈-Term-sym assoc ⟩
                (((id ⊗₁ α⇒) ∘ α⇒) ∘ (α⇒ ⊗₁ id)) ∘ (α⇐ ⊗₁ id)
                  ≈⟨ ∘-resp-≈ assoc ≈-Term-refl ⟩
                ((id ⊗₁ α⇒) ∘ (α⇒ ∘ (α⇒ ⊗₁ id))) ∘ (α⇐ ⊗₁ id)
                  ≈⟨ ∘-resp-≈ (≈-Term-sym assoc) ≈-Term-refl ⟩
                (((id ⊗₁ α⇒) ∘ α⇒) ∘ (α⇒ ⊗₁ id)) ∘ (α⇐ ⊗₁ id)
                  ≈⟨ ∘-resp-≈ assoc ≈-Term-refl ⟩
                ((id ⊗₁ α⇒) ∘ α⇒ ∘ (α⇒ ⊗₁ id)) ∘ (α⇐ ⊗₁ id)
                  ≈⟨ ∘-resp-≈ pentagon ≈-Term-refl ⟩
                (α⇒ ∘ α⇒) ∘ (α⇐ ⊗₁ id)
                  ≈⟨ assoc ⟩
                α⇒ ∘ (α⇒ ∘ (α⇐ ⊗₁ id))
              ∎)
              ≈-Term-refl) ⟩
      α⇐ ∘ ((α⇒ ∘ (α⇒ ∘ (α⇐ ⊗₁ id))) ∘ α⇐)
        ≈⟨ ∘-resp-≈ ≈-Term-refl assoc ⟩
      α⇐ ∘ (α⇒ ∘ ((α⇒ ∘ (α⇐ ⊗₁ id)) ∘ α⇐))
        ≈⟨ ≈-Term-sym assoc ⟩
      (α⇐ ∘ α⇒) ∘ ((α⇒ ∘ (α⇐ ⊗₁ id)) ∘ α⇐)
        ≈⟨ ∘-resp-≈ α⇐∘α⇒≈id ≈-Term-refl ⟩
      id ∘ ((α⇒ ∘ (α⇐ ⊗₁ id)) ∘ α⇐)
        ≈⟨ idˡ ⟩
      (α⇒ ∘ (α⇐ ⊗₁ id)) ∘ α⇐
        ≈⟨ assoc ⟩
      α⇒ ∘ ((α⇐ ⊗₁ id) ∘ α⇐)
    ∎

--------------------------------------------------------------------------------
-- ## σ-block-hexagon: Yang-Baxter braid at the σ-block level.
--
-- Statement (4-object braid):
--   (id_C ⊗ σ-block_{A,B,D}) ∘ σ-block_{A,C,B⊗D} ∘ (id_A ⊗ σ-block_{B,C,D})
--     ≈Term σ-block_{B,C,A⊗D} ∘ (id_B ⊗ σ-block_{A,C,D}) ∘ σ-block_{A,B,C⊗D}
--
-- at type A ⊗ (B ⊗ (C ⊗ D)) → C ⊗ (B ⊗ (A ⊗ D)).
--
-- ## Both sides implement the permutation (A,B,C,D) → (C,B,A,D),
-- specifically the transposition of A and C with B and D fixed.
-- Each side is a sequence of 3 elementary transpositions of adjacent
-- positions:
--   LHS: swap-pos-2-3, swap-pos-1-2, swap-pos-2-3.
--   RHS: swap-pos-1-2, swap-pos-2-3, swap-pos-1-2.
-- The equality is the well-known Yang-Baxter braid relation
-- s_2 s_1 s_2 = s_1 s_2 s_1 in the symmetric group.
--
-- ## Derivation status
--
-- Our progress so far includes the full FREEMONOIDAL infrastructure
-- needed for this proof:
--   * pentagon-flip-right (and its three siblings) for shifting α⇒/α⇐
--     past id-tensored α's;
--   * the bare hexagon and hexagon₂;
--   * σ-block-natural₁/₃ for pushing morphisms through σ-blocks.
--
-- The actual proof requires a calculation chain of approximately
-- 200-400 equational steps:
--   1. Expand each σ-block into α⇒ ∘ (σ ⊗ id) ∘ α⇐.
--   2. Use ⊗-∘-dist to distribute (id ⊗ σ-block) over the chain.
--   3. Apply pentagon-flip-right at the boundaries between σ-blocks
--      (where (id_X ⊗ α⇐_{Y,Z,W}) meets α⇒_{X,Y,Z⊗W}).
--   4. Apply α⇐∘id⊗α⇒-rewrite at the other boundaries.
--   5. Carry the (σ ⊗ id) factors through using σ∘[f⊗g]≈[g⊗f]∘σ.
--   6. Apply the bare hexagon (or hexagon₂) at the strategic CENTER
--      of the chain to swap two adjacent σ's.
--   7. Reverse all α-coherence manipulations on the OTHER side to
--      arrive at RHS.
--
-- This proof has not been completed in the present session. The
-- pentagon-flip helpers above (~150 LOC of new lemmas) constitute
-- non-trivial progress: they reduce the proof of σ-block-hexagon
-- from a multi-hexagon-application chain to a single-hexagon chain,
-- once the boundaries between σ-blocks are correctly normalised.
--
-- See `Sub/BPrepSwapClosure.agda` for how this lemma would be used
-- to close `rfr-B-prep-swap`.
--------------------------------------------------------------------------------

--------------------------------------------------------------------------------
-- ## Tail-only hexagon: bare hexagon ⊗ id_W.
--
-- The bare hexagon:
--
--   id ⊗ σ ∘ α⇒ ∘ σ ⊗ id ≈Term α⇒ ∘ σ ∘ α⇒.
--
-- Tensored with id_W on both sides yields:
--
--   ((id ⊗ σ) ⊗ id_W) ∘ (α⇒ ⊗ id_W) ∘ ((σ ⊗ id) ⊗ id_W)
--     ≈ (α⇒ ⊗ id_W) ∘ (σ ⊗ id_W) ∘ (α⇒ ⊗ id_W).

private
  -- Bare hexagon explicitly typed.  At objects A, B, C:
  --   id_B ⊗ σ_{A,C} ∘ α⇒_{B,A,C} ∘ σ_{A,B} ⊗ id_C
  --     ≈ α⇒_{B,C,A} ∘ σ_{A,B⊗C} ∘ α⇒_{A,B,C}.
  -- (input (A⊗B)⊗C, output B⊗(C⊗A).)

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
        ≈⟨ ∘-resp-≈ ≈-Term-refl
             (≈-Term-trans (≈-Term-sym ⊗-∘-dist)
               (⊗-resp-≈ ≈-Term-refl idˡ)) ⟩
      ((id ⊗₁ σ) ⊗₁ id) ∘ ((α⇒ ∘ (σ ⊗₁ id)) ⊗₁ id)
        ≈⟨ ≈-Term-trans (≈-Term-sym ⊗-∘-dist)
             (⊗-resp-≈ ≈-Term-refl idˡ) ⟩
      ((id ⊗₁ σ) ∘ α⇒ ∘ (σ ⊗₁ id)) ⊗₁ id
        ≈⟨ ⊗-resp-≈ hexagon ≈-Term-refl ⟩
      (α⇒ ∘ σ ∘ α⇒) ⊗₁ id
        ≈⟨ ≈-Term-trans (⊗-resp-≈ ≈-Term-refl (≈-Term-sym idˡ)) ⊗-∘-dist ⟩
      (α⇒ ⊗₁ id) ∘ ((σ ∘ α⇒) ⊗₁ id)
        ≈⟨ ∘-resp-≈ ≈-Term-refl
             (≈-Term-trans (⊗-resp-≈ ≈-Term-refl (≈-Term-sym idˡ)) ⊗-∘-dist) ⟩
      (α⇒ ⊗₁ id) ∘ (σ ⊗₁ id) ∘ (α⇒ ⊗₁ id)
    ∎

--------------------------------------------------------------------------------
-- ## σ-block-hexagon, full 4-object Yang-Baxter braid at the σ-block level.
--
-- Statement: for A, B, C, D : ObjTerm at type
-- `A ⊗ (B ⊗ (C ⊗ D)) → C ⊗ (B ⊗ (A ⊗ D))`,
--
--   (id_C ⊗ σ-block_{A,B,D}) ∘ σ-block_{A,C,B⊗D} ∘ (id_A ⊗ σ-block_{B,C,D})
--     ≈Term σ-block_{B,C,A⊗D} ∘ (id_B ⊗ σ-block_{A,C,D}) ∘ σ-block_{A,B,C⊗D}.
--
-- ### Proof outline
--
-- Both sides are computed by composing 3 transpositions in the
-- symmetric group S₄ (acting on (A,B,C,D) with D fixed).  The equation
-- is s₂s₁s₂ = s₁s₂s₁ in S₃ (since D is fixed).
--
-- Both sides reduce, after carrying the various `α⇒/α⇐` factors around
-- σ⊗id, to a common form of the shape
--
--   α⇒_{..} ⊗ id_D ∘ (canonical 3-σ middle) ⊗ id_D ∘ α⇐_{..} ⊗ id_D
--
-- where the "canonical 3-σ middle" is precisely `(id⊗σ ∘ α⇒ ∘ σ⊗id)`
-- or `(α⇒ ∘ σ ∘ α⇒)`, both equal by the bare hexagon.
--
-- The proof uses `hexagon-with-tail` for the core swap, and pentagon-
-- coherence rewrites to slide α's between left-associated and right-
-- associated views.

--------------------------------------------------------------------------------
-- ## σ⊗id-collapse-middle: middle reduction lemma.
--
-- For the central α⇐∘(σ⊗id)∘α⇒ chunk:
--
--   α⇐_{C⊗A,B,D} ∘ (σ_{A,C} ⊗ id_{B⊗D}) ∘ α⇒_{A⊗C,B,D}
--     ≈ ((σ_{A,C} ⊗ id_B) ⊗ id_D)
--
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
        ≈⟨ ∘-resp-≈ ≈-Term-refl
             (∘-resp-≈ (⊗-resp-≈ ≈-Term-refl (≈-Term-sym id⊗id≈id)) ≈-Term-refl) ⟩
      α⇐ ∘ (σ ⊗₁ (id ⊗₁ id)) ∘ α⇒
        ≈⟨ ≈-Term-sym assoc ⟩
      (α⇐ ∘ (σ ⊗₁ (id ⊗₁ id))) ∘ α⇒
        ≈⟨ ∘-resp-≈ α⇐-comm ≈-Term-refl ⟩
      (((σ ⊗₁ id) ⊗₁ id) ∘ α⇐) ∘ α⇒
        ≈⟨ assoc ⟩
      ((σ ⊗₁ id) ⊗₁ id) ∘ (α⇐ ∘ α⇒)
        ≈⟨ ∘-resp-≈ ≈-Term-refl α⇐∘α⇒≈id ⟩
      ((σ ⊗₁ id) ⊗₁ id) ∘ id
        ≈⟨ idʳ ⟩
      ((σ ⊗₁ id) ⊗₁ id)
    ∎

--------------------------------------------------------------------------------
-- ## σ-block-hexagon, full 4-object Yang-Baxter braid at the σ-block level.
--
-- ### Proof status: SIMPLER VARIANT DERIVED.
--
-- We deliver a constructive SIMPLER VARIANT that captures the
-- algebraic core: the bare hexagon `tensored with id_D`, exposing
-- the σ-block hexagon as the bare hexagon "lifted" by a passive
-- trailing object.  This is `hexagon-with-tail` (already proved).
--
-- The full 4-object σ-block-hexagon equation, as stated below, is
-- the bare-hexagon-with-tail `(α⇒ ∘ σ ∘ α⇒) ⊗ id_D = (id⊗σ ∘ α⇒ ∘ σ⊗id) ⊗ id_D`
-- conjugated by α⇒/α⇐ towers on both ends.  The conjugation work is
-- mechanical but voluminous (~250-400 LOC of equational reasoning
-- per side).  We leave it as a future-work deliverable.
--
-- Specifically, the simpler variant we prove constructively here is:
--
--   σ-block-hexagon-core (DERIVED below):
--     `((id ⊗ σ) ⊗ id_D) ∘ (α⇒ ⊗ id_D) ∘ ((σ ⊗ id) ⊗ id_D)
--       ≈Term (α⇒ ⊗ id_D) ∘ (σ ⊗ id_D) ∘ (α⇒ ⊗ id_D)`
--
-- and this is precisely `hexagon-with-tail`.
--
-- The full σ-block-hexagon = hexagon-with-tail conjugated by:
--   * LHS-conjugate: pentagon-tower wrapping (σ-block expansions +
--     α-coherence rewrites) on both ends.
--   * RHS-conjugate: dual tower (with α⇐ instead of α⇒, mirror-image
--     pentagon-coherence rewrites).
--
-- These conjugates cancel symmetrically (by α⇒∘α⇐≈id and α⇐∘α⇒≈id
-- repeatedly), reducing σ-block-hexagon to hexagon-with-tail.
--
-- ### What's delivered constructively:
--   1. `hexagon-with-tail` (the algebraic core): bare hexagon ⊗ id_D.
--   2. `σ⊗id-collapse-middle` (key α-collapse lemma).
--   3. `pentagon-flip-right`, `α⇐∘id⊗α⇒-rewrite`, `pentagon-flip-α⇒-inside-tensor`
--      (all α-coherence helpers needed for the conjugate cancellations).
--   4. `σ-block-natural₁`, `σ-block-natural₃` (used in the conjugate work).
--   5. `σ-block-involutive`, `hexagon₂` (used in alternative discharge
--      paths).
--
-- The full σ-block-hexagon = `hexagon-with-tail` + conjugation work.
-- The conjugation work alone is ~300 LOC of careful pentagon/α-comm
-- chaining.  We do not inline it here.

σ-block-hexagon-core
  : ∀ {A B C D : ObjTerm}
  → (((id {A = B} ⊗₁ σ {A = A} {B = C}) ⊗₁ id {A = D})
      ∘ (α⇒ {A = B} {B = A} {C = C} ⊗₁ id {A = D})
      ∘ ((σ {A = A} {B = B} ⊗₁ id {A = C}) ⊗₁ id {A = D}))
    ≈Term ((α⇒ {A = B} {B = C} {C = A} ⊗₁ id {A = D})
            ∘ (σ {A = A} {B = B ⊗₀ C} ⊗₁ id {A = D})
            ∘ (α⇒ {A = A} {B = B} {C = C} ⊗₁ id {A = D}))
σ-block-hexagon-core = hexagon-with-tail

--------------------------------------------------------------------------------
-- ## Pentagon-stack identities used in σ-block-hexagon.
--
-- The two "stacking" identities below are derived from pentagon.  They
-- show how to convert between α⇐ ∘ (id ⊗ α⇐) and (α⇒ ⊗ id) ∘ α⇐ ∘ α⇐:
--
--   α⇐_{P,Q⊗R,S} ∘ (id_P ⊗ α⇐_{Q,R,S})
--     ≈ (α⇒_{P,Q,R} ⊗ id_S) ∘ α⇐_{P⊗Q,R,S} ∘ α⇐_{P,Q,R⊗S}.

private
  -- Pentagon-inverse: derived directly from pentagon-flip-right.
  --   From pentagon-flip-right: (id ⊗ α⇐) ∘ α⇒ ≈ α⇒ ∘ (α⇒ ⊗ id) ∘ α⇐.
  --   Reading right-to-left: α⇐ ∘ ((id ⊗ α⇐) ∘ α⇒) ∘ (α⇐ ⊗ id) ∘ α⇐
  --                        ≈ α⇐ ∘ α⇒ ∘ ... = ... → simplifies.
  --
  -- We need: α⇐ ∘ (id ⊗ α⇐) ≈ (α⇒ ⊗ id) ∘ α⇐ ∘ α⇐.
  --
  -- Take pentagon-flip-right and post-compose with α⇐:
  --   (id ⊗ α⇐) ∘ α⇒ ∘ α⇐ ≈ α⇒ ∘ (α⇒ ⊗ id) ∘ α⇐ ∘ α⇐
  --   (id ⊗ α⇐) ∘ id ≈ α⇒ ∘ (α⇒ ⊗ id) ∘ α⇐ ∘ α⇐
  --   (id ⊗ α⇐) ≈ α⇒ ∘ (α⇒ ⊗ id) ∘ α⇐ ∘ α⇐.
  -- Pre-compose with α⇐:
  --   α⇐ ∘ (id ⊗ α⇐) ≈ α⇐ ∘ α⇒ ∘ (α⇒ ⊗ id) ∘ α⇐ ∘ α⇐
  --                  ≈ (α⇒ ⊗ id) ∘ α⇐ ∘ α⇐.

  α⇐-stack-from-pentagon
    : ∀ {P Q R S : ObjTerm}
    → α⇐ {A = P} {B = Q ⊗₀ R} {C = S}
        ∘ (id {A = P} ⊗₁ α⇐ {A = Q} {B = R} {C = S})
      ≈Term (α⇒ {A = P} {B = Q} {C = R} ⊗₁ id {A = S})
              ∘ α⇐ {A = P ⊗₀ Q} {B = R} {C = S}
              ∘ α⇐ {A = P} {B = Q} {C = R ⊗₀ S}
  α⇐-stack-from-pentagon {P} {Q} {R} {S} =
    begin
      α⇐ ∘ (id ⊗₁ α⇐)
        ≈⟨ ≈-Term-sym idʳ ⟩
      (α⇐ ∘ (id ⊗₁ α⇐)) ∘ id
        ≈⟨ ∘-resp-≈ ≈-Term-refl (≈-Term-sym α⇒∘α⇐≈id) ⟩
      (α⇐ ∘ (id ⊗₁ α⇐)) ∘ (α⇒ ∘ α⇐)
        ≈⟨ ≈-Term-sym assoc ⟩
      ((α⇐ ∘ (id ⊗₁ α⇐)) ∘ α⇒) ∘ α⇐
        ≈⟨ ∘-resp-≈ assoc ≈-Term-refl ⟩
      (α⇐ ∘ ((id ⊗₁ α⇐) ∘ α⇒)) ∘ α⇐
        ≈⟨ ∘-resp-≈ (∘-resp-≈ ≈-Term-refl pentagon-flip-right) ≈-Term-refl ⟩
      (α⇐ ∘ (α⇒ ∘ (α⇒ ⊗₁ id) ∘ α⇐)) ∘ α⇐
        ≈⟨ ∘-resp-≈ (≈-Term-sym assoc) ≈-Term-refl ⟩
      ((α⇐ ∘ α⇒) ∘ (α⇒ ⊗₁ id) ∘ α⇐) ∘ α⇐
        ≈⟨ ∘-resp-≈ (∘-resp-≈ α⇐∘α⇒≈id ≈-Term-refl) ≈-Term-refl ⟩
      (id ∘ (α⇒ ⊗₁ id) ∘ α⇐) ∘ α⇐
        ≈⟨ ∘-resp-≈ idˡ ≈-Term-refl ⟩
      ((α⇒ ⊗₁ id) ∘ α⇐) ∘ α⇐
        ≈⟨ assoc ⟩
      (α⇒ ⊗₁ id) ∘ α⇐ ∘ α⇐
    ∎

--------------------------------------------------------------------------------
-- ## σ-block-hexagon: 4-object Yang-Baxter braid (constructive proof).
--
-- The proof reduces both LHS and RHS to a common inner-form via
-- pentagon-coherence rewrites and the bare hexagon at the σ-level.
--
-- Both sides reduce to:
--
--   common = α⇒_{C,B,A⊗D} ∘ α⇒_{C⊗B,A,D}
--          ∘ [inner ⊗ id_D]
--          ∘ α⇐_{A⊗B,C,D} ∘ α⇐_{A,B,C⊗D}
--
-- where `inner : (A⊗B)⊗C → (C⊗B)⊗A` is the symmetric-monoidal
-- "reverse" permutation in 3 letters.
--
-- We have two equivalent forms of inner (related by hexagon₁):
--
--   inner-L = α⇐_{C,B,A} ∘ (id_C ⊗ σ_{A,B}) ∘ σ_{A⊗B,C}
--   inner-R = σ_{A,C⊗B} ∘ (id_A ⊗ σ_{B,C}) ∘ α⇒_{A,B,C}.

--------------------------------------------------------------------------------
-- ## Helper: σ_{A⊗B,C} expansion via hexagon₂.
--
-- hexagon₂ {X = A} {Y = B} {Z = C}:
--   (σ_{A,C} ⊗ id_B) ∘ α⇐_{A,C,B} ∘ (id_A ⊗ σ_{B,C})
--     ≈ α⇐_{C,A,B} ∘ σ_{A⊗B,C} ∘ α⇐_{A,B,C}
--
-- Rearranged (pre-mul by α⇒_{C,A,B}, post-mul by α⇒_{A,B,C}):
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
        -- Sandwich σ = id ∘ σ ∘ id, with id = α⇒ ∘ α⇐ and id = α⇐ ∘ α⇒.
        ≈⟨ ≈-Term-sym idˡ ⟩
      id ∘ σ
        ≈⟨ ∘-resp-≈ (≈-Term-sym α⇒∘α⇐≈id) ≈-Term-refl ⟩
      (α⇒ ∘ α⇐) ∘ σ
        ≈⟨ assoc ⟩
      α⇒ ∘ (α⇐ ∘ σ)
        ≈⟨ ∘-resp-≈ ≈-Term-refl (≈-Term-sym idʳ) ⟩
      α⇒ ∘ ((α⇐ ∘ σ) ∘ id)
        ≈⟨ ∘-resp-≈ ≈-Term-refl (∘-resp-≈ ≈-Term-refl (≈-Term-sym α⇐∘α⇒≈id)) ⟩
      α⇒ ∘ ((α⇐ ∘ σ) ∘ (α⇐ ∘ α⇒))
        -- Re-associate: (α⇐ ∘ σ) ∘ (α⇐ ∘ α⇒) = (α⇐ ∘ σ ∘ α⇐) ∘ α⇒.
        ≈⟨ ∘-resp-≈ ≈-Term-refl
             (≈-Term-trans (≈-Term-sym assoc)
               (∘-resp-≈ assoc ≈-Term-refl)) ⟩
      α⇒ ∘ ((α⇐ ∘ (σ ∘ α⇐)) ∘ α⇒)
        ≈⟨ ∘-resp-≈ ≈-Term-refl (∘-resp-≈ (≈-Term-sym assoc) ≈-Term-refl) ⟩
      α⇒ ∘ (((α⇐ ∘ σ) ∘ α⇐) ∘ α⇒)
        -- The center α⇐ ∘ σ ∘ α⇐ = α⇐ ∘ σ_{A⊗B,C} ∘ α⇐_{A,B,C} (we're at right level).
        -- By hexagon₂ (sym): α⇐ ∘ σ ∘ α⇐ ≈ (σ ⊗ id) ∘ α⇐ ∘ (id ⊗ σ).
        ≈⟨ ∘-resp-≈ ≈-Term-refl
             (∘-resp-≈
               (≈-Term-trans assoc (≈-Term-sym hexagon₂))
               ≈-Term-refl) ⟩
      α⇒ ∘ (((σ ⊗₁ id) ∘ α⇐ ∘ (id ⊗₁ σ)) ∘ α⇒)
        -- Re-associate to final form.
        ≈⟨ ∘-resp-≈ ≈-Term-refl assoc ⟩
      α⇒ ∘ ((σ ⊗₁ id) ∘ ((α⇐ ∘ (id ⊗₁ σ)) ∘ α⇒))
        ≈⟨ ∘-resp-≈ ≈-Term-refl (∘-resp-≈ ≈-Term-refl assoc) ⟩
      α⇒ ∘ ((σ ⊗₁ id) ∘ (α⇐ ∘ ((id ⊗₁ σ) ∘ α⇒)))
        ≈⟨ ∘-resp-≈ ≈-Term-refl (∘-resp-≈ ≈-Term-refl
             (∘-resp-≈ ≈-Term-refl ≈-Term-refl)) ⟩
      α⇒ ∘ (σ ⊗₁ id) ∘ α⇐ ∘ (id ⊗₁ σ) ∘ α⇒
    ∎

--------------------------------------------------------------------------------
-- ## Helper: inner-eq.
--
-- inner-L = α⇐_{C,B,A} ∘ (id_C ⊗ σ_{A,B}) ∘ σ_{A⊗B,C}
-- inner-R = σ_{A,C⊗B} ∘ (id_A ⊗ σ_{B,C}) ∘ α⇒_{A,B,C}
--
-- Proof: expand σ_{A⊗B,C} via σ-A⊗B-expand, then apply hexagon₁ at
-- the center (id ⊗ σ_{A,B}) ∘ α⇒_{C,A,B} ∘ (σ_{A,C} ⊗ id_B) = α⇒_{C,B,A} ∘ σ_{A,C⊗B} ∘ α⇒_{A,C,B},
-- then cancel α⇐∘α⇒ and α⇒∘α⇐.

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
        -- Expand σ_{A⊗B,C} via σ-A⊗B-expand.
        ≈⟨ ∘-resp-≈ ≈-Term-refl (∘-resp-≈ ≈-Term-refl σ-A⊗B-expand) ⟩
      α⇐ ∘ (id ⊗₁ σ) ∘ (α⇒ ∘ (σ ⊗₁ id) ∘ α⇐ ∘ (id ⊗₁ σ) ∘ α⇒)
        -- Strategy: reassociate the inner big chunk to expose
        -- ((id ⊗ σ) ∘ α⇒ ∘ (σ ⊗ id)) for hexagon.
        --
        -- Use ≈-Term-trans steps via re-association.  The big chunk
        -- right-assoc is α⇒ ∘ ((σ⊗id) ∘ (α⇐ ∘ ((id⊗σ) ∘ α⇒))).
        --
        -- We can compute the answer differently: use assoc twice to
        -- "absorb" the first two terms of σ-expand into the (id⊗σ) prefix.
        ≈⟨ ≈-Term-sym assoc ⟩
      (α⇐ ∘ (id ⊗₁ σ)) ∘ (α⇒ ∘ (σ ⊗₁ id) ∘ α⇐ ∘ (id ⊗₁ σ) ∘ α⇒)
        ≈⟨ ∘-resp-≈ ≈-Term-refl (≈-Term-sym assoc) ⟩
      (α⇐ ∘ (id ⊗₁ σ)) ∘ ((α⇒ ∘ (σ ⊗₁ id)) ∘ α⇐ ∘ (id ⊗₁ σ) ∘ α⇒)
        ≈⟨ ≈-Term-sym assoc ⟩
      ((α⇐ ∘ (id ⊗₁ σ)) ∘ (α⇒ ∘ (σ ⊗₁ id))) ∘ α⇐ ∘ (id ⊗₁ σ) ∘ α⇒
        ≈⟨ ∘-resp-≈ assoc ≈-Term-refl ⟩
      (α⇐ ∘ ((id ⊗₁ σ) ∘ (α⇒ ∘ (σ ⊗₁ id)))) ∘ α⇐ ∘ (id ⊗₁ σ) ∘ α⇒
        ≈⟨ ∘-resp-≈ (∘-resp-≈ ≈-Term-refl (≈-Term-sym assoc)) ≈-Term-refl ⟩
      (α⇐ ∘ (((id ⊗₁ σ) ∘ α⇒) ∘ (σ ⊗₁ id))) ∘ α⇐ ∘ (id ⊗₁ σ) ∘ α⇒
        ≈⟨ ∘-resp-≈ (∘-resp-≈ ≈-Term-refl assoc) ≈-Term-refl ⟩
      (α⇐ ∘ ((id ⊗₁ σ) ∘ α⇒ ∘ (σ ⊗₁ id))) ∘ α⇐ ∘ (id ⊗₁ σ) ∘ α⇒
        -- Apply hexagon: (id ⊗ σ) ∘ α⇒ ∘ (σ ⊗ id) ≈ α⇒ ∘ σ ∘ α⇒.
        ≈⟨ ∘-resp-≈ (∘-resp-≈ ≈-Term-refl hexagon) ≈-Term-refl ⟩
      (α⇐ ∘ (α⇒ ∘ σ ∘ α⇒)) ∘ α⇐ ∘ (id ⊗₁ σ) ∘ α⇒
        -- Reassoc: α⇐ ∘ α⇒ = id.
        ≈⟨ ∘-resp-≈ (≈-Term-sym assoc) ≈-Term-refl ⟩
      ((α⇐ ∘ α⇒) ∘ σ ∘ α⇒) ∘ α⇐ ∘ (id ⊗₁ σ) ∘ α⇒
        ≈⟨ ∘-resp-≈ (∘-resp-≈ α⇐∘α⇒≈id ≈-Term-refl) ≈-Term-refl ⟩
      (id ∘ σ ∘ α⇒) ∘ α⇐ ∘ (id ⊗₁ σ) ∘ α⇒
        ≈⟨ ∘-resp-≈ idˡ ≈-Term-refl ⟩
      (σ ∘ α⇒) ∘ α⇐ ∘ (id ⊗₁ σ) ∘ α⇒
        -- Reassoc and cancel α⇒ ∘ α⇐ = id.
        ≈⟨ assoc ⟩
      σ ∘ (α⇒ ∘ α⇐ ∘ (id ⊗₁ σ) ∘ α⇒)
        ≈⟨ ∘-resp-≈ ≈-Term-refl (≈-Term-sym assoc) ⟩
      σ ∘ ((α⇒ ∘ α⇐) ∘ (id ⊗₁ σ) ∘ α⇒)
        ≈⟨ ∘-resp-≈ ≈-Term-refl (∘-resp-≈ α⇒∘α⇐≈id ≈-Term-refl) ⟩
      σ ∘ (id ∘ (id ⊗₁ σ) ∘ α⇒)
        ≈⟨ ∘-resp-≈ ≈-Term-refl idˡ ⟩
      σ ∘ ((id ⊗₁ σ) ∘ α⇒)
        ≈⟨ ≈-Term-sym assoc ⟩
      (σ ∘ (id ⊗₁ σ)) ∘ α⇒
        ≈⟨ assoc ⟩
      σ ∘ (id ⊗₁ σ) ∘ α⇒
    ∎

--------------------------------------------------------------------------------
-- ## Helpers: inner-L, inner-R, NF-L, NF-R.
--
-- The "common normal form" for σ-block-hexagon LHS and RHS.

private
  inner-L : ∀ {A B C : ObjTerm} → HomTerm ((A ⊗₀ B) ⊗₀ C) ((C ⊗₀ B) ⊗₀ A)
  inner-L {A} {B} {C} = α⇐ {A = C} {B = B} {C = A}
                      ∘ (id {A = C} ⊗₁ σ {A = A} {B = B})
                      ∘ σ {A = A ⊗₀ B} {B = C}

  inner-R : ∀ {A B C : ObjTerm} → HomTerm ((A ⊗₀ B) ⊗₀ C) ((C ⊗₀ B) ⊗₀ A)
  inner-R {A} {B} {C} = σ {A = A} {B = C ⊗₀ B}
                      ∘ (id {A = A} ⊗₁ σ {A = B} {B = C})
                      ∘ α⇒ {A = A} {B = B} {C = C}

  NF-L : ∀ {A B C D : ObjTerm}
       → HomTerm (A ⊗₀ (B ⊗₀ (C ⊗₀ D))) (C ⊗₀ (B ⊗₀ (A ⊗₀ D)))
  NF-L {A} {B} {C} {D}
    = α⇒ {A = C} {B = B} {C = A ⊗₀ D}
    ∘ α⇒ {A = C ⊗₀ B} {B = A} {C = D}
    ∘ (inner-L {A} {B} {C} ⊗₁ id {A = D})
    ∘ α⇐ {A = A ⊗₀ B} {B = C} {C = D}
    ∘ α⇐ {A = A} {B = B} {C = C ⊗₀ D}

  NF-R : ∀ {A B C D : ObjTerm}
       → HomTerm (A ⊗₀ (B ⊗₀ (C ⊗₀ D))) (C ⊗₀ (B ⊗₀ (A ⊗₀ D)))
  NF-R {A} {B} {C} {D}
    = α⇒ {A = C} {B = B} {C = A ⊗₀ D}
    ∘ α⇒ {A = C ⊗₀ B} {B = A} {C = D}
    ∘ (inner-R {A} {B} {C} ⊗₁ id {A = D})
    ∘ α⇐ {A = A ⊗₀ B} {B = C} {C = D}
    ∘ α⇐ {A = A} {B = B} {C = C ⊗₀ D}

  NF-L-eq-NF-R : ∀ {A B C D : ObjTerm}
               → NF-L {A} {B} {C} {D} ≈Term NF-R {A} {B} {C} {D}
  NF-L-eq-NF-R = ∘-resp-≈ ≈-Term-refl
                   (∘-resp-≈ ≈-Term-refl
                     (∘-resp-≈ (⊗-resp-≈ inner-eq ≈-Term-refl)
                                ≈-Term-refl))

  -- Helper: id ⊗ (f ∘ g) ≈ (id ⊗ f) ∘ (id ⊗ g).
  id⊗-dist
    : ∀ {X Y₁ Y₂ Y₃ : ObjTerm}
        {f : HomTerm Y₂ Y₃} {g : HomTerm Y₁ Y₂}
    → id {A = X} ⊗₁ (f ∘ g) ≈Term (id ⊗₁ f) ∘ (id ⊗₁ g)
  id⊗-dist = ≈-Term-trans (⊗-resp-≈ (≈-Term-sym idˡ) ≈-Term-refl) ⊗-∘-dist

  -- Helper: f ⊗ id ≈ ... (analogous, but used less often).
  ⊗id-dist
    : ∀ {Y₁ Y₂ Y₃ X : ObjTerm}
        {f : HomTerm Y₂ Y₃} {g : HomTerm Y₁ Y₂}
    → (f ∘ g) ⊗₁ id {A = X} ≈Term (f ⊗₁ id) ∘ (g ⊗₁ id)
  ⊗id-dist = ≈-Term-trans (⊗-resp-≈ ≈-Term-refl (≈-Term-sym idˡ)) ⊗-∘-dist

  -- Pre-LHS expansion: rewrite (id ⊗ σ-block) as three (id ⊗ ?) factors.
  id⊗σ-block-expand
    : ∀ {X A B C : ObjTerm}
    → id {A = X} ⊗₁ σ-block {A = A} {B = B} {C = C}
      ≈Term (id {A = X} ⊗₁ α⇒ {A = B} {B = A} {C = C})
              ∘ (id ⊗₁ (σ {A = A} {B = B} ⊗₁ id {A = C}))
              ∘ (id ⊗₁ α⇐ {A = A} {B = B} {C = C})
  id⊗σ-block-expand =
    ≈-Term-trans id⊗-dist (∘-resp-≈ ≈-Term-refl id⊗-dist)

--------------------------------------------------------------------------------
-- ## σ-block-hexagon: 4-object Yang-Baxter braid.
--
-- Statement:
--   (id_C ⊗ σ-block_{A,B,D}) ∘ σ-block_{A,C,B⊗D} ∘ (id_A ⊗ σ-block_{B,C,D})
--     ≈ σ-block_{B,C,A⊗D} ∘ (id_B ⊗ σ-block_{A,C,D}) ∘ σ-block_{A,B,C⊗D}
--
-- at type A ⊗ (B ⊗ (C ⊗ D)) → C ⊗ (B ⊗ (A ⊗ D)).
--
-- ### Proof strategy
--
-- Both LHS and RHS reduce to a common normal form via 9 rewrite steps.
-- The two NFs differ only in the inner permutation form (inner-L vs
-- inner-R), related by `inner-eq` (using hexagon₁ + σ-A⊗B-expand).

-- The LHS-to-NF reduction (private helper).
-- This is a ~150-LOC chain of pentagon + hexagon₂ rewrites.

private
  -- Intermediate form after expanding σ-block definitions and applying
  -- id⊗σ-block-expand.
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

  -- LHS = LHS-expanded (just unfolds σ-block via id⊗σ-block-expand on each side).
  LHS-to-expanded
    : ∀ {A B C D : ObjTerm}
    → (id {A = C} ⊗₁ σ-block {A = A} {B = B} {C = D})
        ∘ σ-block {A = A} {B = C} {C = B ⊗₀ D}
        ∘ (id {A = A} ⊗₁ σ-block {A = B} {B = C} {C = D})
      ≈Term LHS-expanded {A} {B} {C} {D}
  LHS-to-expanded =
    ∘-resp-≈ id⊗σ-block-expand
      (∘-resp-≈ ≈-Term-refl id⊗σ-block-expand)

--------------------------------------------------------------------------------
-- ## LHS-to-NF proof strategy (not yet inlined).
--
-- The reduction `LHS-expanded ≈ NF-R` is a mechanical chain of ~9 steps:
--
--   Step A: re-associate LHS-expanded (= (P)∘(Q)∘(R) with 3-piece groups)
--           into a single right-associated chain of 7 morphisms with
--           boundaries `(id_C ⊗ α⇐_{A,B,D}) ∘ α⇒_{C,A,B⊗D}` (between P and Q)
--           and `α⇐_{A,C,B⊗D} ∘ (id_A ⊗ α⇒_{C,B,D})` (between Q and R)
--           exposed as 2-piece sub-compositions.
--   Step B: apply `pentagon-flip-right` to the P-Q boundary, and
--           `α⇐∘id⊗α⇒-rewrite` to the Q-R boundary.
--   Step C: re-associate to group `α⇐ ∘ (σ ⊗ id_{B⊗D}) ∘ α⇒` in the middle.
--   Step D: apply `σ⊗id-collapse-middle`, collapsing the middle to
--           `((σ ⊗ id_B) ⊗ id_D)`.
--   Step E: apply `α-comm` (sym) and `α⇐-comm` to push (id ⊗ (σ ⊗ id_D))
--           past α⇒ and α⇐ on both sides, converting them to ((id ⊗ σ) ⊗ id).
--   Step F: factor out `(... ⊗ id_D)` and apply `hexagon` at the inner
--           `(id_C ⊗ σ) ∘ α⇒ ∘ (σ ⊗ id_B)`, collapsing 5 inner pieces to 3.
--   Step G: apply `pentagon` at the top boundary
--           `(id_C ⊗ α⇒) ∘ α⇒ ∘ (α⇒ ⊗ id_D) → α⇒ ∘ α⇒`.
--   Step H: apply `α⇐-stack-from-pentagon` (sym) at the bottom boundary
--           `α⇐ ∘ (id ⊗ α⇐) → (α⇒ ⊗ id) ∘ α⇐ ∘ α⇐`.
--   Step I: factor the 3 middle `(X ⊗ id_D)` pieces into a single
--           `((X₁ ∘ X₂ ∘ X₃) ⊗ id_D) = (inner-R ⊗ id_D)`.
--
-- Result: LHS-expanded ≈ NF-R = α⇒ ∘ α⇒ ∘ (inner-R ⊗ id) ∘ α⇐ ∘ α⇐.
-- Then `LHS ≈ LHS-expanded ≈ NF-R ≈ NF-L` via LHS-to-expanded, the chain
-- above, and sym(NF-L-eq-NF-R).
--
-- The inline proof is left as follow-up work; total LOC estimate: 250-400
-- given the careful manual re-association needed for each step.
--
-- This is the only remaining gap to constructively derive σ-block-hexagon
-- (Yang-Baxter braid at the σ-block level) from FreeMonoidal axioms alone.

private
  -- Step A: re-associate the 9-element chain.
  -- Convert LHS-expanded (which has 3 grouped triples) into a flat
  -- right-associated chain of 9 morphisms.
  step-A : ∀ {A B C D : ObjTerm}
    → LHS-expanded {A} {B} {C} {D}
      ≈Term
      (id {A = C} ⊗₁ α⇒ {A = B} {B = A} {C = D})
        ∘ (id ⊗₁ (σ {A = A} {B = B} ⊗₁ id {A = D}))
        ∘ (id ⊗₁ α⇐ {A = A} {B = B} {C = D})
        ∘ (α⇒ {A = C} {B = A} {C = B ⊗₀ D})
        ∘ (σ {A = A} {B = C} ⊗₁ id {A = B ⊗₀ D})
        ∘ (α⇐ {A = A} {B = C} {C = B ⊗₀ D})
        ∘ (id {A = A} ⊗₁ α⇒ {A = C} {B = B} {C = D})
        ∘ (id ⊗₁ (σ {A = B} {B = C} ⊗₁ id {A = D}))
        ∘ (id ⊗₁ α⇐ {A = B} {B = C} {C = D})
  step-A {A} {B} {C} {D} =
    -- LHS = (a1 ∘ (a2 ∘ a3)) ∘ ((b1 ∘ (b2 ∘ b3)) ∘ (c1 ∘ (c2 ∘ c3)))
    -- Target = a1 ∘ (a2 ∘ (a3 ∘ (b1 ∘ (b2 ∘ (b3 ∘ (c1 ∘ (c2 ∘ c3)))))))
    --
    -- Strategy:
    --   assoc1: (a1 ∘ (a2 ∘ a3)) ∘ X  ≈  a1 ∘ ((a2 ∘ a3) ∘ X)
    --   assoc2: a1 ∘ ((a2 ∘ a3) ∘ X)  ≈  a1 ∘ (a2 ∘ (a3 ∘ X))
    --   assoc3: a1 ∘ (a2 ∘ (a3 ∘ ((b1 ∘ (b2 ∘ b3)) ∘ Y)))  ≈  a1 ∘ (a2 ∘ (a3 ∘ (b1 ∘ ((b2 ∘ b3) ∘ Y))))
    --   assoc4: a1 ∘ (a2 ∘ (a3 ∘ (b1 ∘ ((b2 ∘ b3) ∘ Y))))  ≈  a1 ∘ (a2 ∘ (a3 ∘ (b1 ∘ (b2 ∘ (b3 ∘ Y)))))
    ≈-Term-trans assoc
      (≈-Term-trans (∘-resp-≈ ≈-Term-refl assoc)
        (≈-Term-trans (∘-resp-≈ ≈-Term-refl
                         (∘-resp-≈ ≈-Term-refl
                           (∘-resp-≈ ≈-Term-refl assoc)))
          (∘-resp-≈ ≈-Term-refl
             (∘-resp-≈ ≈-Term-refl
               (∘-resp-≈ ≈-Term-refl
                 (∘-resp-≈ ≈-Term-refl assoc))))))

  -- Step B: apply pentagon-flip-right at the e3-e4 boundary
  -- (id_C ⊗ α⇐_{A,B,D}) ∘ α⇒_{C,A,B⊗D} → α⇒_{C,A⊗B,D} ∘ (α⇒_{C,A,B} ⊗ id_D) ∘ α⇐_{C⊗A,B,D}.
  -- AND apply α⇐∘id⊗α⇒-rewrite at the e6-e7 boundary
  -- α⇐_{A,C,B⊗D} ∘ (id_A ⊗ α⇒_{C,B,D}) → α⇒_{A⊗C,B,D} ∘ (α⇐_{A,C,B} ⊗ id_D) ∘ α⇐_{A,C⊗B,D}.
  step-B : ∀ {A B C D : ObjTerm}
    →   (id {A = C} ⊗₁ α⇒ {A = B} {B = A} {C = D})
        ∘ (id ⊗₁ (σ {A = A} {B = B} ⊗₁ id {A = D}))
        ∘ (id ⊗₁ α⇐ {A = A} {B = B} {C = D})
        ∘ (α⇒ {A = C} {B = A} {C = B ⊗₀ D})
        ∘ (σ {A = A} {B = C} ⊗₁ id {A = B ⊗₀ D})
        ∘ (α⇐ {A = A} {B = C} {C = B ⊗₀ D})
        ∘ (id {A = A} ⊗₁ α⇒ {A = C} {B = B} {C = D})
        ∘ (id ⊗₁ (σ {A = B} {B = C} ⊗₁ id {A = D}))
        ∘ (id ⊗₁ α⇐ {A = B} {B = C} {C = D})
      ≈Term
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
  step-B {A} {B} {C} {D} =
    -- Rewrite at e3-e4 (under e1 ∘ e2): replace (id_C ⊗ α⇐) ∘ α⇒ with
    -- α⇒ ∘ (α⇒ ⊗ id) ∘ α⇐ using pentagon-flip-right.
    -- Rewrite at e6-e7 (further inside): replace α⇐ ∘ (id_A ⊗ α⇒) with
    -- α⇒ ∘ (α⇐ ⊗ id) ∘ α⇐ using α⇐∘id⊗α⇒-rewrite.
    ∘-resp-≈ ≈-Term-refl                  -- under e1
      (∘-resp-≈ ≈-Term-refl              -- under e2
        (≈-Term-trans
          (≈-Term-trans (≈-Term-sym assoc)   -- e3 ∘ (e4 ∘ Y) → (e3 ∘ e4) ∘ Y
            (≈-Term-trans (∘-resp-≈ pentagon-flip-right ≈-Term-refl)  -- (e3 ∘ e4) → p1 ∘ (p2 ∘ p3)
              (≈-Term-trans assoc                  -- (p1 ∘ (p2 ∘ p3)) ∘ Y → p1 ∘ ((p2 ∘ p3) ∘ Y)
                (∘-resp-≈ ≈-Term-refl assoc))))    -- p1 ∘ ((p2 ∘ p3) ∘ Y) → p1 ∘ (p2 ∘ (p3 ∘ Y))
          (∘-resp-≈ ≈-Term-refl            -- under p1
            (∘-resp-≈ ≈-Term-refl          -- under p2
              (∘-resp-≈ ≈-Term-refl        -- under p3
                (∘-resp-≈ ≈-Term-refl      -- under e5
                  (≈-Term-trans (≈-Term-sym assoc)  -- e6 ∘ (e7 ∘ Z) → (e6 ∘ e7) ∘ Z
                    (≈-Term-trans (∘-resp-≈ α⇐∘id⊗α⇒-rewrite ≈-Term-refl)
                      (≈-Term-trans assoc
                        (∘-resp-≈ ≈-Term-refl assoc))))))))))

  -- Step C: re-associate to group p3 ∘ e5 ∘ q1 = α⇐_{C⊗A,B,D} ∘ (σ⊗id) ∘ α⇒_{A⊗C,B,D}
  -- as a 3-element composition to apply σ⊗id-collapse-middle.
  -- Before: ... ∘ p2 ∘ (p3 ∘ (e5 ∘ (q1 ∘ Y)))
  -- After:  ... ∘ p2 ∘ ((p3 ∘ (e5 ∘ q1)) ∘ Y)
  --                       --------------
  --                       this is α⇐ ∘ (σ ⊗ id) ∘ α⇒
  step-C : ∀ {A B C D : ObjTerm}
    →   (id {A = C} ⊗₁ α⇒ {A = B} {B = A} {C = D})
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
      ≈Term
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
  step-C {A} {B} {C} {D} =
    -- Move under e1, e2, p1, p2. Then:
    -- p3 ∘ (e5 ∘ (q1 ∘ Y)) → p3 ∘ ((e5 ∘ q1) ∘ Y) → (p3 ∘ (e5 ∘ q1)) ∘ Y
    ∘-resp-≈ ≈-Term-refl       -- under e1
      (∘-resp-≈ ≈-Term-refl   -- under e2
        (∘-resp-≈ ≈-Term-refl -- under p1
          (∘-resp-≈ ≈-Term-refl -- under p2
            (≈-Term-trans
              (∘-resp-≈ ≈-Term-refl (≈-Term-sym assoc))  -- p3 ∘ (e5 ∘ (q1 ∘ Y)) → p3 ∘ ((e5 ∘ q1) ∘ Y)
              (≈-Term-sym assoc)))))                       -- p3 ∘ ((e5 ∘ q1) ∘ Y) → (p3 ∘ (e5 ∘ q1)) ∘ Y

  -- Step D: collapse the middle α⇐ ∘ (σ⊗id) ∘ α⇒ → ((σ⊗id_B) ⊗ id_D)
  -- using σ⊗id-collapse-middle.
  step-D : ∀ {A B C D : ObjTerm}
    →   (id {A = C} ⊗₁ α⇒ {A = B} {B = A} {C = D})
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
      ≈Term
        (id {A = C} ⊗₁ α⇒ {A = B} {B = A} {C = D})
        ∘ (id ⊗₁ (σ {A = A} {B = B} ⊗₁ id {A = D}))
        ∘ (α⇒ {A = C} {B = A ⊗₀ B} {C = D})
        ∘ (α⇒ {A = C} {B = A} {C = B} ⊗₁ id {A = D})
        ∘ (((σ {A = A} {B = C} ⊗₁ id {A = B}) ⊗₁ id {A = D})
            ∘ (α⇐ {A = A} {B = C} {C = B} ⊗₁ id {A = D})
            ∘ (α⇐ {A = A} {B = C ⊗₀ B} {C = D})
            ∘ (id ⊗₁ (σ {A = B} {B = C} ⊗₁ id {A = D}))
            ∘ (id ⊗₁ α⇐ {A = B} {B = C} {C = D}))
  step-D {A} {B} {C} {D} =
    ∘-resp-≈ ≈-Term-refl
      (∘-resp-≈ ≈-Term-refl
        (∘-resp-≈ ≈-Term-refl
          (∘-resp-≈ ≈-Term-refl
            (∘-resp-≈ σ⊗id-collapse-middle ≈-Term-refl))))

  -- Step E: push e2 = (id_C ⊗ (σ_{A,B} ⊗ id_D)) past p1 = α⇒_{C,A⊗B,D}
  --         to convert e2 to ((id_C ⊗ σ_{A,B}) ⊗ id_D), placing α⇒ in front.
  -- Use α-comm: α⇒ ∘ ((f ⊗ g) ⊗ h) ≈ (f ⊗ (g ⊗ h)) ∘ α⇒.
  -- So (f ⊗ (g ⊗ h)) ∘ α⇒ ≈ α⇒ ∘ ((f ⊗ g) ⊗ h), i.e., sym α-comm
  -- with f = id_C, g = σ_{A,B}, h = id_D.
  --
  -- Also push e8 = (id_A ⊗ (σ_{B,C} ⊗ id_D)) past q3 (left), converting
  -- e8 to ((id_A ⊗ σ_{B,C}) ⊗ id_D), placing α⇐_{A,B⊗C,D} after.
  -- Use α⇐-comm: α⇐ ∘ (h ⊗ (i ⊗ j)) ≈ ((h ⊗ i) ⊗ j) ∘ α⇐.
  -- So q3 ∘ e8 = α⇐ ∘ (id_A ⊗ (σ_{B,C} ⊗ id_D)) ≈ ((id_A ⊗ σ_{B,C}) ⊗ id_D) ∘ α⇐.
  step-E : ∀ {A B C D : ObjTerm}
    →   (id {A = C} ⊗₁ α⇒ {A = B} {B = A} {C = D})
        ∘ (id ⊗₁ (σ {A = A} {B = B} ⊗₁ id {A = D}))
        ∘ (α⇒ {A = C} {B = A ⊗₀ B} {C = D})
        ∘ (α⇒ {A = C} {B = A} {C = B} ⊗₁ id {A = D})
        ∘ (((σ {A = A} {B = C} ⊗₁ id {A = B}) ⊗₁ id {A = D})
            ∘ (α⇐ {A = A} {B = C} {C = B} ⊗₁ id {A = D})
            ∘ (α⇐ {A = A} {B = C ⊗₀ B} {C = D})
            ∘ (id ⊗₁ (σ {A = B} {B = C} ⊗₁ id {A = D}))
            ∘ (id ⊗₁ α⇐ {A = B} {B = C} {C = D}))
      ≈Term
        (id {A = C} ⊗₁ α⇒ {A = B} {B = A} {C = D})
        ∘ (α⇒ {A = C} {B = B ⊗₀ A} {C = D})
        ∘ ((id {A = C} ⊗₁ σ {A = A} {B = B}) ⊗₁ id {A = D})
        ∘ (α⇒ {A = C} {B = A} {C = B} ⊗₁ id {A = D})
        ∘ ((σ {A = A} {B = C} ⊗₁ id {A = B}) ⊗₁ id {A = D})
        ∘ (α⇐ {A = A} {B = C} {C = B} ⊗₁ id {A = D})
        ∘ ((id {A = A} ⊗₁ σ {A = B} {B = C}) ⊗₁ id {A = D})
        ∘ (α⇐ {A = A} {B = B ⊗₀ C} {C = D})
        ∘ (id {A = A} ⊗₁ α⇐ {A = B} {B = C} {C = D})
  step-E {A} {B} {C} {D} =
    -- Compose two rewrites:
    --   (a) push e2 past p1: e2 ∘ (p1 ∘ Y) → α⇒ ∘ (e2_shifted ∘ Y)
    --   (b) push e8 past q3: q3 ∘ (e8 ∘ e9) → e8_shifted ∘ (α⇐ ∘ e9)
    ∘-resp-≈ ≈-Term-refl                  -- under e1
      (≈-Term-trans                       -- rewrite (a) on outer position
        (≈-Term-trans (≈-Term-sym assoc)   -- e2 ∘ (p1 ∘ Y) → (e2 ∘ p1) ∘ Y
          (≈-Term-trans (∘-resp-≈ (≈-Term-sym α-comm) ≈-Term-refl)  -- e2 ∘ p1 → α⇒ ∘ e2_shifted
            (≈-Term-trans assoc           -- (α⇒ ∘ e2_shifted) ∘ Y → α⇒ ∘ (e2_shifted ∘ Y)
              ≈-Term-refl)))
        -- After (a): α⇒ ∘ (e2_shifted ∘ (p2 ∘ (middle ∘ (q2 ∘ (q3 ∘ (e8 ∘ e9))))))
        -- Navigate: α⇒, e2_shifted, p2, middle, q2 -- that's 5 levels.
        (∘-resp-≈ ≈-Term-refl  -- under α⇒
          (∘-resp-≈ ≈-Term-refl  -- under e2_shifted
            (∘-resp-≈ ≈-Term-refl  -- under p2
              (∘-resp-≈ ≈-Term-refl  -- under middle
                (∘-resp-≈ ≈-Term-refl  -- under q2
                  (≈-Term-trans (≈-Term-sym assoc)  -- q3 ∘ (e8 ∘ e9) → (q3 ∘ e8) ∘ e9
                    (≈-Term-trans (∘-resp-≈ α⇐-comm ≈-Term-refl)  -- q3 ∘ e8 → e8_shifted ∘ α⇐
                      assoc))))))                  -- (e8_shifted ∘ α⇐) ∘ e9 → e8_shifted ∘ (α⇐ ∘ e9)
        ))

  -- Step F: apply hexagon-with-tail to pieces 3,4,5 (the (id⊗σ)⊗id, α⇒⊗id, (σ⊗id)⊗id),
  -- then cancel (α⇒_{A,C,B} ⊗ id_D) ∘ (α⇐_{A,C,B} ⊗ id_D) = id.
  step-F : ∀ {A B C D : ObjTerm}
    →   (id {A = C} ⊗₁ α⇒ {A = B} {B = A} {C = D})
        ∘ (α⇒ {A = C} {B = B ⊗₀ A} {C = D})
        ∘ ((id {A = C} ⊗₁ σ {A = A} {B = B}) ⊗₁ id {A = D})
        ∘ (α⇒ {A = C} {B = A} {C = B} ⊗₁ id {A = D})
        ∘ ((σ {A = A} {B = C} ⊗₁ id {A = B}) ⊗₁ id {A = D})
        ∘ (α⇐ {A = A} {B = C} {C = B} ⊗₁ id {A = D})
        ∘ ((id {A = A} ⊗₁ σ {A = B} {B = C}) ⊗₁ id {A = D})
        ∘ (α⇐ {A = A} {B = B ⊗₀ C} {C = D})
        ∘ (id {A = A} ⊗₁ α⇐ {A = B} {B = C} {C = D})
      ≈Term
        (id {A = C} ⊗₁ α⇒ {A = B} {B = A} {C = D})
        ∘ (α⇒ {A = C} {B = B ⊗₀ A} {C = D})
        ∘ (α⇒ {A = C} {B = B} {C = A} ⊗₁ id {A = D})
        ∘ (σ {A = A} {B = C ⊗₀ B} ⊗₁ id {A = D})
        ∘ ((id {A = A} ⊗₁ σ {A = B} {B = C}) ⊗₁ id {A = D})
        ∘ (α⇐ {A = A} {B = B ⊗₀ C} {C = D})
        ∘ (id {A = A} ⊗₁ α⇐ {A = B} {B = C} {C = D})
  step-F {A} {B} {C} {D} =
    -- Navigate under e1 ∘ α⇒. Then handle piece3 ∘ piece4 ∘ piece5 ∘ ... ∘ piece7 ∘ α⇐ ∘ e9.
    -- Group + hexagon-with-tail + cancel α⇒⊗id ∘ α⇐⊗id.
    ∘-resp-≈ ≈-Term-refl                       -- under e1
      (∘-resp-≈ ≈-Term-refl                   -- under α⇒
        (≈-Term-trans
          -- Phase 1: rearrange piece3 ∘ (piece4 ∘ (piece5 ∘ Y)) → (piece3 ∘ piece4 ∘ piece5) ∘ Y
          (≈-Term-trans
            (∘-resp-≈ ≈-Term-refl (≈-Term-sym assoc))
            (≈-Term-sym assoc))
          -- Phase 2: rewrite prefix + cancel α⇒⊗id ∘ α⇐⊗id = id
          (≈-Term-trans
            (∘-resp-≈ (hexagon-with-tail {A = A} {B = C} {C = B} {W = D}) ≈-Term-refl)
            (≈-Term-trans assoc
              (∘-resp-≈ ≈-Term-refl
                (≈-Term-trans assoc
                  (∘-resp-≈ ≈-Term-refl
                    (≈-Term-trans (≈-Term-sym assoc)
                      (≈-Term-trans
                        (∘-resp-≈
                          (≈-Term-trans (≈-Term-sym ⊗-∘-dist)
                            (≈-Term-trans (⊗-resp-≈ α⇒∘α⇐≈id idˡ) id⊗id≈id))
                          ≈-Term-refl)
                        idˡ)))))))))

  -- Step G: apply pentagon at the top boundary.
  -- (id_C ⊗ α⇒_{B,A,D}) ∘ α⇒_{C,B⊗A,D} ∘ (α⇒_{C,B,A} ⊗ id_D) → α⇒_{C,B,A⊗D} ∘ α⇒_{C⊗B,A,D}
  step-G : ∀ {A B C D : ObjTerm}
    →   (id {A = C} ⊗₁ α⇒ {A = B} {B = A} {C = D})
        ∘ (α⇒ {A = C} {B = B ⊗₀ A} {C = D})
        ∘ (α⇒ {A = C} {B = B} {C = A} ⊗₁ id {A = D})
        ∘ (σ {A = A} {B = C ⊗₀ B} ⊗₁ id {A = D})
        ∘ ((id {A = A} ⊗₁ σ {A = B} {B = C}) ⊗₁ id {A = D})
        ∘ (α⇐ {A = A} {B = B ⊗₀ C} {C = D})
        ∘ (id {A = A} ⊗₁ α⇐ {A = B} {B = C} {C = D})
      ≈Term
        (α⇒ {A = C} {B = B} {C = A ⊗₀ D})
        ∘ (α⇒ {A = C ⊗₀ B} {B = A} {C = D})
        ∘ (σ {A = A} {B = C ⊗₀ B} ⊗₁ id {A = D})
        ∘ ((id {A = A} ⊗₁ σ {A = B} {B = C}) ⊗₁ id {A = D})
        ∘ (α⇐ {A = A} {B = B ⊗₀ C} {C = D})
        ∘ (id {A = A} ⊗₁ α⇐ {A = B} {B = C} {C = D})
  step-G {A} {B} {C} {D} =
    -- Group top 3 together (piece1 ∘ piece2 ∘ piece3), apply pentagon, distribute.
    -- piece1 ∘ (piece2 ∘ (piece3 ∘ Y)) → (piece1 ∘ piece2 ∘ piece3) ∘ Y → (α⇒ ∘ α⇒) ∘ Y → α⇒ ∘ (α⇒ ∘ Y)
    ≈-Term-trans
      (≈-Term-trans (∘-resp-≈ ≈-Term-refl (≈-Term-sym assoc))   -- piece1 ∘ (piece2 ∘ (piece3 ∘ Y)) → piece1 ∘ ((piece2 ∘ piece3) ∘ Y)
        (≈-Term-sym assoc))                                       -- → (piece1 ∘ (piece2 ∘ piece3)) ∘ Y
      (≈-Term-trans (∘-resp-≈ pentagon ≈-Term-refl)              -- (piece1 ∘ piece2 ∘ piece3) → α⇒ ∘ α⇒
        assoc)                                                   -- (α⇒ ∘ α⇒) ∘ Y → α⇒ ∘ (α⇒ ∘ Y)

  -- Step H: apply α⇐-stack-from-pentagon at the bottom boundary.
  -- α⇐_{A,B⊗C,D} ∘ (id_A ⊗ α⇐_{B,C,D}) → (α⇒_{A,B,C} ⊗ id_D) ∘ α⇐_{A⊗B,C,D} ∘ α⇐_{A,B,C⊗D}
  step-H : ∀ {A B C D : ObjTerm}
    →   (α⇒ {A = C} {B = B} {C = A ⊗₀ D})
        ∘ (α⇒ {A = C ⊗₀ B} {B = A} {C = D})
        ∘ (σ {A = A} {B = C ⊗₀ B} ⊗₁ id {A = D})
        ∘ ((id {A = A} ⊗₁ σ {A = B} {B = C}) ⊗₁ id {A = D})
        ∘ (α⇐ {A = A} {B = B ⊗₀ C} {C = D})
        ∘ (id {A = A} ⊗₁ α⇐ {A = B} {B = C} {C = D})
      ≈Term
        (α⇒ {A = C} {B = B} {C = A ⊗₀ D})
        ∘ (α⇒ {A = C ⊗₀ B} {B = A} {C = D})
        ∘ (σ {A = A} {B = C ⊗₀ B} ⊗₁ id {A = D})
        ∘ ((id {A = A} ⊗₁ σ {A = B} {B = C}) ⊗₁ id {A = D})
        ∘ (α⇒ {A = A} {B = B} {C = C} ⊗₁ id {A = D})
        ∘ (α⇐ {A = A ⊗₀ B} {B = C} {C = D})
        ∘ (α⇐ {A = A} {B = B} {C = C ⊗₀ D})
  step-H {A} {B} {C} {D} =
    -- Navigate under α⇒, α⇒, σ⊗id, (id⊗σ)⊗id (4 levels), then apply α⇐-stack-from-pentagon.
    ∘-resp-≈ ≈-Term-refl    -- under α⇒_{C,B,A⊗D}
      (∘-resp-≈ ≈-Term-refl  -- under α⇒_{C⊗B,A,D}
        (∘-resp-≈ ≈-Term-refl  -- under σ⊗id
          (∘-resp-≈ ≈-Term-refl  -- under (id⊗σ)⊗id
            α⇐-stack-from-pentagon)))

  -- Step I: factor the 3 (X ⊗ id_D) pieces into a single (inner-R ⊗ id_D).
  -- (σ_{A,C⊗B} ⊗ id_D) ∘ ((id_A ⊗ σ_{B,C}) ⊗ id_D) ∘ (α⇒_{A,B,C} ⊗ id_D)
  --   ≈ ((σ_{A,C⊗B} ∘ (id_A ⊗ σ_{B,C}) ∘ α⇒_{A,B,C}) ⊗ id_D)
  --   ≡ (inner-R ⊗ id_D)
  step-I : ∀ {A B C D : ObjTerm}
    →   (α⇒ {A = C} {B = B} {C = A ⊗₀ D})
        ∘ (α⇒ {A = C ⊗₀ B} {B = A} {C = D})
        ∘ (σ {A = A} {B = C ⊗₀ B} ⊗₁ id {A = D})
        ∘ ((id {A = A} ⊗₁ σ {A = B} {B = C}) ⊗₁ id {A = D})
        ∘ (α⇒ {A = A} {B = B} {C = C} ⊗₁ id {A = D})
        ∘ (α⇐ {A = A ⊗₀ B} {B = C} {C = D})
        ∘ (α⇐ {A = A} {B = B} {C = C ⊗₀ D})
      ≈Term NF-R {A} {B} {C} {D}
  step-I {A} {B} {C} {D} =
    -- Navigate under α⇒, α⇒. Then merge 3 (X⊗id_D) pieces.
    -- p3 ∘ (p4 ∘ (p5 ∘ Y)) → ((p3 ∘ p4 ∘ p5) ∘ Y) → ((merged) ∘ Y)
    --
    -- Merge p3 ∘ p4: (σ⊗id) ∘ ((id⊗σ)⊗id) → ((σ ∘ (id⊗σ)) ⊗ (id ∘ id)) → ((σ ∘ (id⊗σ)) ⊗ id)
    -- Merge with p5: ((σ ∘ (id⊗σ)) ⊗ id) ∘ (α⇒ ⊗ id) → ((σ ∘ (id⊗σ) ∘ α⇒) ⊗ (id ∘ id))
    --                                                  → ((σ ∘ (id⊗σ) ∘ α⇒) ⊗ id) = (inner-R ⊗ id)
    ∘-resp-≈ ≈-Term-refl  -- under α⇒_{C,B,A⊗D}
      (∘-resp-≈ ≈-Term-refl  -- under α⇒_{C⊗B,A,D}
        (≈-Term-trans
          (≈-Term-trans (∘-resp-≈ ≈-Term-refl (≈-Term-sym assoc))  -- p3 ∘ (p4 ∘ (p5 ∘ Y)) → p3 ∘ ((p4 ∘ p5) ∘ Y)
            (≈-Term-sym assoc))                                     -- → (p3 ∘ (p4 ∘ p5)) ∘ Y
          (∘-resp-≈
            -- Now: (p3 ∘ (p4 ∘ p5)) = (σ⊗id) ∘ (((id⊗σ)⊗id) ∘ (α⇒⊗id))
            -- We want this to equal (inner-R ⊗ id_D) where inner-R = σ ∘ (id⊗σ) ∘ α⇒.
            -- Strategy: combine the inner ⊗-pair first.
            (≈-Term-trans
              -- p4 ∘ p5: ((id⊗σ)⊗id) ∘ (α⇒⊗id) ≈ ((id⊗σ ∘ α⇒) ⊗ (id ∘ id))
              -- Apply ⊗-∘-dist sym to (p4 ∘ p5).
              (∘-resp-≈ ≈-Term-refl
                (≈-Term-trans (≈-Term-sym ⊗-∘-dist)
                  (⊗-resp-≈ ≈-Term-refl idˡ)))
              -- Now have: (σ⊗id) ∘ (((id⊗σ) ∘ α⇒) ⊗ id)
              -- Apply ⊗-∘-dist sym again.
              (≈-Term-trans (≈-Term-sym ⊗-∘-dist)
                (⊗-resp-≈ ≈-Term-refl idˡ)))
            ≈-Term-refl)))

  -- LHS-to-NF-R: compose all 9 steps to derive LHS-expanded ≈ NF-R.
  LHS-to-NF-R : ∀ {A B C D : ObjTerm}
              → LHS-expanded {A} {B} {C} {D} ≈Term NF-R {A} {B} {C} {D}
  LHS-to-NF-R =
    ≈-Term-trans step-A
      (≈-Term-trans step-B
        (≈-Term-trans step-C
          (≈-Term-trans step-D
            (≈-Term-trans step-E
              (≈-Term-trans step-F
                (≈-Term-trans step-G
                  (≈-Term-trans step-H step-I)))))))

  --------------------------------------------------------------------------------
  -- ## RHS-expanded and RHS-to-NF-L.
  --
  -- For RHS = σ-block_{B,C,A⊗D} ∘ (id_B ⊗ σ-block_{A,C,D}) ∘ σ-block_{A,B,C⊗D}
  --
  -- After expansion of σ-blocks (outer two via inline, middle via id⊗σ-block-expand):
  --
  --   RHS-expanded
  --     = (α⇒_{C,B,A⊗D} ∘ (σ_{B,C} ⊗ id_{A⊗D}) ∘ α⇐_{B,C,A⊗D})
  --       ∘ ((id_B ⊗ α⇒_{C,A,D}) ∘ (id_B ⊗ (σ_{A,C} ⊗ id_D)) ∘ (id_B ⊗ α⇐_{A,C,D}))
  --       ∘ (α⇒_{B,A,C⊗D} ∘ (σ_{A,B} ⊗ id_{C⊗D}) ∘ α⇐_{A,B,C⊗D})

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

  -- RHS = RHS-expanded (just unfolds the middle σ-block via id⊗σ-block-expand).
  RHS-to-expanded
    : ∀ {A B C D : ObjTerm}
    → σ-block {A = B} {B = C} {C = A ⊗₀ D}
        ∘ (id {A = B} ⊗₁ σ-block {A = A} {B = C} {C = D})
        ∘ σ-block {A = A} {B = B} {C = C ⊗₀ D}
      ≈Term RHS-expanded {A} {B} {C} {D}
  RHS-to-expanded =
    ∘-resp-≈ ≈-Term-refl
      (∘-resp-≈ id⊗σ-block-expand ≈-Term-refl)

  -- RHS path step R-A: re-associate RHS-expanded into a 9-element flat
  -- right-associated chain.
  step-R-A : ∀ {A B C D : ObjTerm}
    → RHS-expanded {A} {B} {C} {D}
      ≈Term
      (α⇒ {A = C} {B = B} {C = A ⊗₀ D})
        ∘ (σ {A = B} {B = C} ⊗₁ id {A = A ⊗₀ D})
        ∘ (α⇐ {A = B} {B = C} {C = A ⊗₀ D})
        ∘ (id {A = B} ⊗₁ α⇒ {A = C} {B = A} {C = D})
        ∘ (id ⊗₁ (σ {A = A} {B = C} ⊗₁ id {A = D}))
        ∘ (id ⊗₁ α⇐ {A = A} {B = C} {C = D})
        ∘ (α⇒ {A = B} {B = A} {C = C ⊗₀ D})
        ∘ (σ {A = A} {B = B} ⊗₁ id {A = C ⊗₀ D})
        ∘ (α⇐ {A = A} {B = B} {C = C ⊗₀ D})
  step-R-A {A} {B} {C} {D} =
    -- Same pattern as step-A: 4 assoc rotations.
    ≈-Term-trans assoc
      (≈-Term-trans (∘-resp-≈ ≈-Term-refl assoc)
        (≈-Term-trans (∘-resp-≈ ≈-Term-refl
                         (∘-resp-≈ ≈-Term-refl
                           (∘-resp-≈ ≈-Term-refl assoc)))
          (∘-resp-≈ ≈-Term-refl
             (∘-resp-≈ ≈-Term-refl
               (∘-resp-≈ ≈-Term-refl
                 (∘-resp-≈ ≈-Term-refl assoc))))))

  -- Step R-B: apply α⇐∘id⊗α⇒-rewrite at r3-r4 boundary,
  -- and pentagon-flip-right at r6-r7 boundary.
  --
  -- r3 ∘ r4 = α⇐_{B,C,A⊗D} ∘ (id_B ⊗ α⇒_{C,A,D}) →
  --   α⇒_{B⊗C,A,D} ∘ (α⇐_{B,C,A} ⊗ id_D) ∘ α⇐_{B,C⊗A,D}
  -- r6 ∘ r7 = (id_B ⊗ α⇐_{A,C,D}) ∘ α⇒_{B,A,C⊗D} →
  --   α⇒_{B,A⊗C,D} ∘ (α⇒_{B,A,C} ⊗ id_D) ∘ α⇐_{B⊗A,C,D}
  step-R-B : ∀ {A B C D : ObjTerm}
    →   (α⇒ {A = C} {B = B} {C = A ⊗₀ D})
        ∘ (σ {A = B} {B = C} ⊗₁ id {A = A ⊗₀ D})
        ∘ (α⇐ {A = B} {B = C} {C = A ⊗₀ D})
        ∘ (id {A = B} ⊗₁ α⇒ {A = C} {B = A} {C = D})
        ∘ (id ⊗₁ (σ {A = A} {B = C} ⊗₁ id {A = D}))
        ∘ (id ⊗₁ α⇐ {A = A} {B = C} {C = D})
        ∘ (α⇒ {A = B} {B = A} {C = C ⊗₀ D})
        ∘ (σ {A = A} {B = B} ⊗₁ id {A = C ⊗₀ D})
        ∘ (α⇐ {A = A} {B = B} {C = C ⊗₀ D})
      ≈Term
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
  step-R-B {A} {B} {C} {D} =
    -- Navigate under r1 and r2 to reach r3 ∘ r4 ∘ ... Apply α⇐∘id⊗α⇒-rewrite.
    -- Then navigate further to r6 ∘ r7 and apply pentagon-flip-right.
    ∘-resp-≈ ≈-Term-refl                   -- under r1
      (∘-resp-≈ ≈-Term-refl                -- under r2
        (≈-Term-trans
          (≈-Term-trans (≈-Term-sym assoc)  -- r3 ∘ (r4 ∘ Y) → (r3 ∘ r4) ∘ Y
            (≈-Term-trans (∘-resp-≈ α⇐∘id⊗α⇒-rewrite ≈-Term-refl)
              (≈-Term-trans assoc           -- (a ∘ (b ∘ c)) ∘ Y → a ∘ ((b ∘ c) ∘ Y)
                (∘-resp-≈ ≈-Term-refl assoc))))  -- a ∘ ((b ∘ c) ∘ Y) → a ∘ (b ∘ (c ∘ Y))
          -- Now: α⇒_{B⊗C,A,D} ∘ ((α⇐_{B,C,A}⊗id_D) ∘ (α⇐_{B,C⊗A,D} ∘ (r5 ∘ (r6 ∘ ...))))
          -- Navigate under α⇒_{B⊗C,A,D}, (α⇐_{B,C,A}⊗id_D), α⇐_{B,C⊗A,D}, r5 (4 levels)
          -- to reach r6 ∘ (r7 ∘ ...). Apply pentagon-flip-right.
          (∘-resp-≈ ≈-Term-refl    -- under α⇒_{B⊗C,A,D}
            (∘-resp-≈ ≈-Term-refl  -- under (α⇐_{B,C,A}⊗id_D)
              (∘-resp-≈ ≈-Term-refl  -- under α⇐_{B,C⊗A,D}
                (∘-resp-≈ ≈-Term-refl  -- under r5
                  (≈-Term-trans (≈-Term-sym assoc)  -- r6 ∘ (r7 ∘ Y) → (r6 ∘ r7) ∘ Y
                    (≈-Term-trans (∘-resp-≈ pentagon-flip-right ≈-Term-refl)
                      (≈-Term-trans assoc
                        (∘-resp-≈ ≈-Term-refl assoc))))))))))

  -- Step R-C: apply α⇐-comm to push r5 past α⇐_{B,C⊗A,D}, AND cancel
  -- α⇐_{B,A⊗C,D} ∘ α⇒_{B,A⊗C,D} = id.
  --
  -- α⇐_{B,C⊗A,D} ∘ (id_B ⊗ (σ_{A,C} ⊗ id_D))
  --   = α⇐ ∘ (id_B ⊗ (σ_{A,C} ⊗ id_D))     (h=id_B, i=σ_{A,C}, j=id_D)
  --   ≈ ((id_B ⊗ σ_{A,C}) ⊗ id_D) ∘ α⇐_{B,A⊗C,D}    by α⇐-comm
  --
  -- Then α⇐_{B,A⊗C,D} ∘ α⇒_{B,A⊗C,D} = id (cancel).
  step-R-C : ∀ {A B C D : ObjTerm}
    →   (α⇒ {A = C} {B = B} {C = A ⊗₀ D})
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
      ≈Term
        (α⇒ {A = C} {B = B} {C = A ⊗₀ D})
        ∘ (σ {A = B} {B = C} ⊗₁ id {A = A ⊗₀ D})
        ∘ (α⇒ {A = B ⊗₀ C} {B = A} {C = D})
        ∘ (α⇐ {A = B} {B = C} {C = A} ⊗₁ id {A = D})
        ∘ ((id {A = B} ⊗₁ σ {A = A} {B = C}) ⊗₁ id {A = D})
        ∘ (α⇒ {A = B} {B = A} {C = C} ⊗₁ id {A = D})
        ∘ (α⇐ {A = B ⊗₀ A} {B = C} {C = D})
        ∘ (σ {A = A} {B = B} ⊗₁ id {A = C ⊗₀ D})
        ∘ (α⇐ {A = A} {B = B} {C = C ⊗₀ D})
  step-R-C {A} {B} {C} {D} =
    ∘-resp-≈ ≈-Term-refl  -- under r1
      (∘-resp-≈ ≈-Term-refl  -- under r2
        (∘-resp-≈ ≈-Term-refl  -- under α⇒_{B⊗C,A,D}
          (∘-resp-≈ ≈-Term-refl  -- under (α⇐_{B,C,A}⊗id_D)
            (≈-Term-trans (≈-Term-sym assoc)  -- α⇐ ∘ (r5 ∘ X) → (α⇐ ∘ r5) ∘ X
              (≈-Term-trans (∘-resp-≈ α⇐-comm ≈-Term-refl)  -- α⇐ ∘ r5 → r5_shifted ∘ α⇐'
                (≈-Term-trans assoc                          -- (r5' ∘ α⇐') ∘ X → r5' ∘ (α⇐' ∘ X)
                  (∘-resp-≈ ≈-Term-refl                      -- under r5_shifted
                    (≈-Term-trans (≈-Term-sym assoc)         -- α⇐' ∘ (α⇒' ∘ Y) → (α⇐' ∘ α⇒') ∘ Y
                      (≈-Term-trans (∘-resp-≈ α⇐∘α⇒≈id ≈-Term-refl)
                        idˡ)))))))))

  -- Step R-D: apply α-comm (sym) at r2 ∘ α⇒_{B⊗C,A,D} boundary, and
  -- α⇐-comm at α⇐_{B⊗A,C,D} ∘ r8 boundary.
  step-R-D : ∀ {A B C D : ObjTerm}
    →   (α⇒ {A = C} {B = B} {C = A ⊗₀ D})
        ∘ (σ {A = B} {B = C} ⊗₁ id {A = A ⊗₀ D})
        ∘ (α⇒ {A = B ⊗₀ C} {B = A} {C = D})
        ∘ (α⇐ {A = B} {B = C} {C = A} ⊗₁ id {A = D})
        ∘ ((id {A = B} ⊗₁ σ {A = A} {B = C}) ⊗₁ id {A = D})
        ∘ (α⇒ {A = B} {B = A} {C = C} ⊗₁ id {A = D})
        ∘ (α⇐ {A = B ⊗₀ A} {B = C} {C = D})
        ∘ (σ {A = A} {B = B} ⊗₁ id {A = C ⊗₀ D})
        ∘ (α⇐ {A = A} {B = B} {C = C ⊗₀ D})
      ≈Term
        (α⇒ {A = C} {B = B} {C = A ⊗₀ D})
        ∘ (α⇒ {A = C ⊗₀ B} {B = A} {C = D})
        ∘ ((σ {A = B} {B = C} ⊗₁ id {A = A}) ⊗₁ id {A = D})
        ∘ (α⇐ {A = B} {B = C} {C = A} ⊗₁ id {A = D})
        ∘ ((id {A = B} ⊗₁ σ {A = A} {B = C}) ⊗₁ id {A = D})
        ∘ (α⇒ {A = B} {B = A} {C = C} ⊗₁ id {A = D})
        ∘ ((σ {A = A} {B = B} ⊗₁ id {A = C}) ⊗₁ id {A = D})
        ∘ (α⇐ {A = A ⊗₀ B} {B = C} {C = D})
        ∘ (α⇐ {A = A} {B = B} {C = C ⊗₀ D})
  step-R-D {A} {B} {C} {D} =
    -- Rewrite (a): r2 ∘ (α⇒ ∘ Y) → α⇒_{C⊗B,A,D} ∘ (((σ⊗id_A)⊗id_D) ∘ Y)
    -- Rewrite (b): α⇐_{B⊗A,C,D} ∘ (r8 ∘ r9) → ((σ_{A,B}⊗id_C)⊗id_D) ∘ (α⇐_{A⊗B,C,D} ∘ r9)
    ∘-resp-≈ ≈-Term-refl              -- under r1
      (≈-Term-trans
        -- Rewrite (a):
        --   r2 ∘ (α⇒ ∘ Y)
        --   = (σ_{B,C} ⊗ id_{A⊗D}) ∘ (α⇒ ∘ Y)
        --   ≈ (σ_{B,C} ⊗ (id_A ⊗ id_D)) ∘ (α⇒ ∘ Y)        via id⊗id≈id
        --   ≈ ((σ_{B,C} ⊗ (id_A ⊗ id_D)) ∘ α⇒) ∘ Y         via sym assoc
        --   ≈ (α⇒_{C⊗B,A,D} ∘ ((σ_{B,C}⊗id_A)⊗id_D)) ∘ Y   via sym α-comm
        --   ≈ α⇒_{C⊗B,A,D} ∘ (((σ_{B,C}⊗id_A)⊗id_D) ∘ Y)   via assoc
        (≈-Term-trans (∘-resp-≈
          (⊗-resp-≈ ≈-Term-refl (≈-Term-sym id⊗id≈id))  -- σ ⊗ id_{A⊗D} → σ ⊗ (id_A ⊗ id_D)
          ≈-Term-refl)
          (≈-Term-trans (≈-Term-sym assoc)
            (≈-Term-trans (∘-resp-≈ (≈-Term-sym α-comm) ≈-Term-refl)
              assoc)))
        -- Now after rewrite (a): α⇒_{C⊗B,A,D} ∘ (((σ_{B,C}⊗id_A)⊗id_D) ∘ inner)
        -- where inner = (α⇐_{B,C,A}⊗id_D) ∘ ... ∘ α⇐_{B⊗A,C,D} ∘ r8 ∘ r9
        -- Navigate under α⇒_{C⊗B,A,D}, ((σ_{B,C}⊗id_A)⊗id_D), (α⇐_{B,C,A}⊗id_D),
        -- ((id_B⊗σ_{A,C})⊗id_D), (α⇒_{B,A,C}⊗id_D) -- that's 5 levels.
        (∘-resp-≈ ≈-Term-refl   -- under α⇒_{C⊗B,A,D}
          (∘-resp-≈ ≈-Term-refl  -- under ((σ_{B,C}⊗id_A)⊗id_D)
            (∘-resp-≈ ≈-Term-refl  -- under (α⇐_{B,C,A}⊗id_D)
              (∘-resp-≈ ≈-Term-refl  -- under ((id_B⊗σ_{A,C})⊗id_D)
                (∘-resp-≈ ≈-Term-refl  -- under (α⇒_{B,A,C}⊗id_D)
                  -- Now at: α⇐_{B⊗A,C,D} ∘ (r8 ∘ r9)
                  -- Rewrite (b):
                  --   α⇐ ∘ (r8 ∘ r9)
                  --   ≈ (α⇐ ∘ r8) ∘ r9                                    via sym assoc
                  --   ≈ (α⇐ ∘ (σ_{A,B} ⊗ id_{C⊗D})) ∘ r9
                  --   ≈ (α⇐ ∘ (σ_{A,B} ⊗ (id_C ⊗ id_D))) ∘ r9             via id⊗id≈id sym
                  --   ≈ (((σ_{A,B}⊗id_C)⊗id_D) ∘ α⇐_{A⊗B,C,D}) ∘ r9       via α⇐-comm
                  --   ≈ ((σ_{A,B}⊗id_C)⊗id_D) ∘ (α⇐_{A⊗B,C,D} ∘ r9)        via assoc
                  (≈-Term-trans (≈-Term-sym assoc)
                    (≈-Term-trans (∘-resp-≈
                      (≈-Term-trans (∘-resp-≈ ≈-Term-refl
                        (⊗-resp-≈ ≈-Term-refl (≈-Term-sym id⊗id≈id)))  -- σ⊗id_{C⊗D} → σ⊗(id_C⊗id_D)
                        α⇐-comm)
                      ≈-Term-refl)
                      assoc)))))))
        )

  -- Helper lemma: middleX ≈ inner-R.
  -- middleX = (σ_{B,C} ⊗ id_A) ∘ α⇐_{B,C,A} ∘ (id_B ⊗ σ_{A,C}) ∘ α⇒_{B,A,C} ∘ (σ_{A,B} ⊗ id_C)
  -- inner-R = σ_{A,C⊗B} ∘ (id_A ⊗ σ_{B,C}) ∘ α⇒_{A,B,C}
  --
  -- Proof:
  --   middleX = (σ_{B,C} ⊗ id_A) ∘ α⇐_{B,C,A} ∘ ((id_B ⊗ σ_{A,C}) ∘ α⇒_{B,A,C} ∘ (σ_{A,B} ⊗ id_C))
  --           = (σ_{B,C} ⊗ id_A) ∘ α⇐_{B,C,A} ∘ (α⇒_{B,C,A} ∘ σ_{A,B⊗C} ∘ α⇒_{A,B,C})    [hexagon]
  --           = (σ_{B,C} ⊗ id_A) ∘ (α⇐ ∘ α⇒) ∘ σ_{A,B⊗C} ∘ α⇒_{A,B,C}
  --           = (σ_{B,C} ⊗ id_A) ∘ σ_{A,B⊗C} ∘ α⇒_{A,B,C}                                 [α⇐∘α⇒≈id]
  --           = σ_{A,C⊗B} ∘ (id_A ⊗ σ_{B,C}) ∘ α⇒_{A,B,C}                                 [σ-comm]
  --           = inner-R
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
    -- Apply hexagon: (id⊗σ) ∘ α⇒ ∘ (σ⊗id) → α⇒ ∘ σ ∘ α⇒.
    -- Then we have (σ⊗id) ∘ (α⇐ ∘ (α⇒ ∘ σ ∘ α⇒))
    -- Re-associate: α⇐ ∘ (α⇒ ∘ σ ∘ α⇒) → (α⇐ ∘ α⇒) ∘ (σ ∘ α⇒) → id ∘ (σ ∘ α⇒) → σ ∘ α⇒.
    -- Then we have (σ⊗id) ∘ (σ ∘ α⇒) → ((σ⊗id) ∘ σ) ∘ α⇒ → (σ ∘ (id⊗σ)) ∘ α⇒ → σ ∘ ((id⊗σ) ∘ α⇒).
    ≈-Term-trans
      (∘-resp-≈ ≈-Term-refl  -- under (σ ⊗ id)
        (∘-resp-≈ ≈-Term-refl  -- under α⇐
          hexagon))                 -- apply hexagon directly
      (≈-Term-trans
        (∘-resp-≈ ≈-Term-refl  -- under (σ ⊗ id)
          (≈-Term-trans (≈-Term-sym assoc)        -- α⇐ ∘ (α⇒ ∘ X) → (α⇐ ∘ α⇒) ∘ X
            (≈-Term-trans (∘-resp-≈ α⇐∘α⇒≈id ≈-Term-refl)
              idˡ)))                              -- id ∘ X → X = σ ∘ α⇒
        (≈-Term-trans
          (≈-Term-sym assoc)                      -- (σ⊗id) ∘ (σ ∘ α⇒) → ((σ⊗id) ∘ σ) ∘ α⇒
          (≈-Term-trans
            (∘-resp-≈ (≈-Term-sym σ∘[f⊗g]≈[g⊗f]∘σ) ≈-Term-refl)
            assoc)))

  -- Step R-E: combine the 5 (X ⊗ id_D) pieces into a single (inner-R ⊗ id_D).
  --
  -- Pieces 1-5 of the chain (between α⇒_{C⊗B,A,D} and α⇐_{A⊗B,C,D}) compose to (middleX ⊗ id_D),
  -- which equals (inner-R ⊗ id_D) by middleX-eq-inner-R.
  step-R-E : ∀ {A B C D : ObjTerm}
    →   (α⇒ {A = C} {B = B} {C = A ⊗₀ D})
        ∘ (α⇒ {A = C ⊗₀ B} {B = A} {C = D})
        ∘ ((σ {A = B} {B = C} ⊗₁ id {A = A}) ⊗₁ id {A = D})
        ∘ (α⇐ {A = B} {B = C} {C = A} ⊗₁ id {A = D})
        ∘ ((id {A = B} ⊗₁ σ {A = A} {B = C}) ⊗₁ id {A = D})
        ∘ (α⇒ {A = B} {B = A} {C = C} ⊗₁ id {A = D})
        ∘ ((σ {A = A} {B = B} ⊗₁ id {A = C}) ⊗₁ id {A = D})
        ∘ (α⇐ {A = A ⊗₀ B} {B = C} {C = D})
        ∘ (α⇐ {A = A} {B = B} {C = C ⊗₀ D})
      ≈Term NF-R {A} {B} {C} {D}
  step-R-E {A} {B} {C} {D} =
    -- Goal after R-D: chain has 5 ⊗-id pieces in middle (positions 3-7).
    -- Group + ⊗-∘-dist + middleX-eq-inner-R to reach (inner-R ⊗ id_D).
    -- NF-R has form: α⇒ ∘ α⇒ ∘ (inner-R ⊗ id_D) ∘ α⇐ ∘ α⇐.
    --
    -- Strategy: collapse pieces 3-4-5-6-7 to (middleX ⊗ id_D), then apply
    -- middleX-eq-inner-R to get (inner-R ⊗ id_D).
    ∘-resp-≈ ≈-Term-refl  -- under α⇒_{C,B,A⊗D}
      (∘-resp-≈ ≈-Term-refl  -- under α⇒_{C⊗B,A,D}
        -- Now operating on p3 ∘ p4 ∘ p5 ∘ p6 ∘ p7 ∘ α⇐ ∘ α⇐
        -- where p3 = ((σ⊗id)⊗id), p4 = (α⇐⊗id), p5 = ((id⊗σ)⊗id), p6 = (α⇒⊗id), p7 = ((σ⊗id)⊗id)
        -- Group p3 ∘ p4 first (via sym ⊗-∘-dist + idˡ to merge), then iteratively.
        --
        -- p3 ∘ p4 ≈ ((σ⊗id) ∘ α⇐) ⊗ (id ∘ id) ≈ ((σ⊗id) ∘ α⇐) ⊗ id    (sym ⊗-∘-dist + idˡ)
        -- (p3 ∘ p4) ∘ p5 ≈ (((σ⊗id) ∘ α⇐ ∘ (id⊗σ)) ⊗ id)
        -- ...
        --
        -- But we have right-assoc, so the chain is p3 ∘ (p4 ∘ (p5 ∘ (p6 ∘ (p7 ∘ (α⇐ ∘ α⇐))))).
        -- We need to "absorb" p4-p7 into p3's tensor argument step by step.
        --
        -- Specifically:
        --   p3 ∘ (p4 ∘ X) where X = p5 ∘ p6 ∘ p7 ∘ α⇐ ∘ α⇐.
        -- → (p3 ∘ p4) ∘ X
        -- → (p3-p4-merged) ∘ X
        -- → continue...
        --
        -- Each merge is: ⊗-∘-dist sym + idˡ inside ⊗.
        --
        -- After full merge, prefix = (middleX ⊗ id_D), then apply middleX-eq-inner-R.
        (≈-Term-trans
          -- Group all 5 pieces:
          --   p3 ∘ (p4 ∘ (p5 ∘ (p6 ∘ (p7 ∘ Y))))
          -- → p3 ∘ (p4 ∘ (p5 ∘ ((p6 ∘ p7) ∘ Y)))     [sym assoc inside]
          -- → p3 ∘ (p4 ∘ ((p5 ∘ p6 ∘ p7) ∘ Y))      [sym assoc]
          -- → p3 ∘ ((p4 ∘ p5 ∘ p6 ∘ p7) ∘ Y)        [sym assoc]
          -- → (p3 ∘ p4 ∘ p5 ∘ p6 ∘ p7) ∘ Y          [sym assoc]
          (≈-Term-trans
            (∘-resp-≈ ≈-Term-refl
              (∘-resp-≈ ≈-Term-refl
                (∘-resp-≈ ≈-Term-refl (≈-Term-sym assoc))))
            (≈-Term-trans
              (∘-resp-≈ ≈-Term-refl
                (∘-resp-≈ ≈-Term-refl (≈-Term-sym assoc)))
              (≈-Term-trans
                (∘-resp-≈ ≈-Term-refl (≈-Term-sym assoc))
                (≈-Term-sym assoc))))
          -- Now we have (p3 ∘ (p4 ∘ (p5 ∘ (p6 ∘ p7)))) ∘ Y where Y = α⇐ ∘ α⇐.
          -- Merge the prefix into (middleX ⊗ id_D), then apply middleX-eq-inner-R.
          (∘-resp-≈
            (≈-Term-trans
              -- Merge p3 ∘ (p4 ∘ (p5 ∘ (p6 ∘ p7)))
              -- = (σ⊗id)⊗id ∘ ((α⇐⊗id) ∘ ((id⊗σ)⊗id ∘ ((α⇒⊗id) ∘ ((σ⊗id)⊗id))))
              -- We merge step by step. Bottom-up:
              -- p6 ∘ p7: (α⇒⊗id) ∘ ((σ⊗id)⊗id) ≈ ((α⇒ ∘ (σ⊗id)) ⊗ (id ∘ id)) ≈ ((α⇒ ∘ (σ⊗id)) ⊗ id)
              -- p5 ∘ (p6 ∘ p7): ((id⊗σ)⊗id) ∘ ((α⇒ ∘ (σ⊗id)) ⊗ id) ≈ (((id⊗σ) ∘ α⇒ ∘ (σ⊗id)) ⊗ id)
              -- ...
              (∘-resp-≈ ≈-Term-refl
                (∘-resp-≈ ≈-Term-refl
                  (∘-resp-≈ ≈-Term-refl
                    (≈-Term-trans (≈-Term-sym ⊗-∘-dist)
                      (⊗-resp-≈ ≈-Term-refl idˡ)))))
              (≈-Term-trans
                (∘-resp-≈ ≈-Term-refl
                  (∘-resp-≈ ≈-Term-refl
                    (≈-Term-trans (≈-Term-sym ⊗-∘-dist)
                      (⊗-resp-≈ ≈-Term-refl idˡ))))
                (≈-Term-trans
                  (∘-resp-≈ ≈-Term-refl
                    (≈-Term-trans (≈-Term-sym ⊗-∘-dist)
                      (⊗-resp-≈ ≈-Term-refl idˡ)))
                  (≈-Term-trans
                    (≈-Term-trans (≈-Term-sym ⊗-∘-dist)
                      (⊗-resp-≈ ≈-Term-refl idˡ))
                    -- Now we have (middleX ⊗ id_D). Apply middleX-eq-inner-R.
                    (⊗-resp-≈ middleX-eq-inner-R ≈-Term-refl)))))
            ≈-Term-refl)))

  -- RHS-to-NF-R: compose R-A, R-B, R-C, R-D, R-E to derive RHS-expanded ≈ NF-R.
  RHS-to-NF-R : ∀ {A B C D : ObjTerm}
              → RHS-expanded {A} {B} {C} {D} ≈Term NF-R {A} {B} {C} {D}
  RHS-to-NF-R =
    ≈-Term-trans step-R-A
      (≈-Term-trans step-R-B
        (≈-Term-trans step-R-C
          (≈-Term-trans step-R-D step-R-E)))

  -- σ-block-hexagon-helper: the Yang-Baxter braid at the σ-block level (private).
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

-- Public re-export of σ-block-hexagon.
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

--------------------------------------------------------------------------------
-- ## Status (delivered)
--
-- This module provides constructively:
--   * `σ-block` definition.
--   * `σ-block-involutive` lemma.
--   * `σ-block-natural₃` lemma.
--   * `σ-block-natural₁` lemma.
--   * `hexagon₂` (DUAL hexagon at α⇐ level).
--   * `pentagon-flip-right` helper:
--       (id ⊗ α⇐) ∘ α⇒ ≈ α⇒ ∘ (α⇒ ⊗ id) ∘ α⇐.
--   * `pentagon-flip-α⇒-inside-tensor` helper:
--       (α⇒ ⊗ id) ∘ α⇐ ≈ α⇐ ∘ (id ⊗ α⇐) ∘ α⇒.
--   * `α⇐∘id⊗α⇒-rewrite` helper:
--       α⇐ ∘ (id ⊗ α⇒) ≈ α⇒ ∘ (α⇐ ⊗ id) ∘ α⇐.
--   * `σ⊗id-collapse-middle`: α⇐ ∘ (σ ⊗ id_{B⊗D}) ∘ α⇒ ≈ ((σ ⊗ id_B) ⊗ id_D).
--   * `hexagon-with-tail` helper:
--       bare hexagon tensored with id_W on the right.
--   * `α⇐-stack-from-pentagon`:
--       α⇐ ∘ (id ⊗ α⇐) ≈ (α⇒ ⊗ id) ∘ α⇐ ∘ α⇐.
--   * `σ-block-hexagon-core` (SIMPLER VARIANT, DERIVED):
--       the algebraic core of σ-block-hexagon, at the (σ⊗id_D) level.
--
-- ## New infrastructure for σ-block-hexagon (DELIVERED):
--   * `σ-A⊗B-expand` (private): σ_{A⊗B,C} ≈ α⇒ ∘ (σ_{A,C} ⊗ id) ∘ α⇐
--                              ∘ (id ⊗ σ_{B,C}) ∘ α⇒.
--                              Derived from hexagon₂.
--   * `inner-eq` (private): inner-L ≈ inner-R, where
--       inner-L = α⇐_{C,B,A} ∘ (id_C ⊗ σ_{A,B}) ∘ σ_{A⊗B,C}
--       inner-R = σ_{A,C⊗B} ∘ (id_A ⊗ σ_{B,C}) ∘ α⇒_{A,B,C}.
--                              The "core hexagon" identity between
--                              two equivalent normal forms of the
--                              3-letter reverse-permutation.
--   * `id⊗-dist`, `⊗id-dist`, `id⊗σ-block-expand` (private):
--                              distribute id-tensored compositions.
--   * `LHS-expanded`, `LHS-to-expanded` (private): expand σ-blocks
--                              to triple-α-σ-α forms.
--   * `inner-L`, `inner-R`, `NF-L`, `NF-R`, `NF-L-eq-NF-R` (private):
--                              the common normal-form data, with
--                              NF-L ≈ NF-R via inner-eq.
--
-- ## σ-block-hexagon main theorem: FULLY DERIVED CONSTRUCTIVELY.
--
-- The proof goes via a common normal form NF-R.  LHS-to-NF-R is a 9-step
-- chain (step-A through step-I).  RHS-to-NF-R is a 5-step chain
-- (step-R-A through step-R-E), shorter because the RHS structure
-- absorbs more rewrites at each step.  Both chains then combine to
-- yield σ-block-hexagon by transitive symmetry through NF-R.
--
-- All `--safe --with-K`-clean.  No new postulates.
--------------------------------------------------------------------------------
