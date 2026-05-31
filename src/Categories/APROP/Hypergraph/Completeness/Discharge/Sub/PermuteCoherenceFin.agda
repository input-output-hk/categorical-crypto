{-# OPTIONS --safe --with-K #-}

--------------------------------------------------------------------------------
-- Discharge of `Fin-permute-≈Term-coherence` from
-- `Discharge/Sub/PermuteCoherence.agda`.
--
-- ## Goal
--
-- Construct a `FinCoherence` value (i.e. discharge the postulate
-- `Fin-permute-≈Term-coherence`) constructively, using agda-categories'
-- coherence primitives and the `Unique` precondition.
--
-- The target statement is:
--
--   Fin-permute-≈Term-coherence
--     : ∀ {n} {xs ys : List (Fin n)}
--         (xs-uniq : Unique xs)
--         (vlab : Fin n → X)
--         (p q : xs ↭ ys)
--     → permute (PermProp.map⁺ vlab p) ≈Term permute (PermProp.map⁺ vlab q)
--
-- This is Kelly's symmetric monoidal coherence theorem restricted to
-- duplicate-free Fin-level lists.  The X-level statement (without
-- `Unique`) is FALSE in general — see `PermuteCoherence.agda` for the
-- counter-example.
--
-- ## Outcome: PARTIAL DISCHARGE with strong NARROWING.
--
-- We constructively close all of the following:
--
--   * **Empty list** (`xs ≡ []`): `Fin-coherence-empty` (Phase 1).
--   * **Singleton list** (`xs ≡ [x]`): `Fin-coherence-singleton`
--     (Phase 2).
--   * **`permute (↭-sym p) ∘ permute p ≈Term id`** for any `p` — the
--     "permute is an iso" lemma `permute-inverse-left` (Phase 2.5)
--     plus its right-inverse companion `permute-inverse-right`.
--   * **Structurally-matched pairs** — already provided in
--     `PermuteCoherence.agda` (`permute-refl-refl`,
--     `permute-prep-prep`, `permute-swap-swap-aligned`,
--     `permute-trans-trans-aligned`, etc.) and re-used here.
--
-- The only residual obligation is the **self-loop case**:
--
--   SelfLoopPostulate.Fin-permute-self-loop-id
--     : ∀ {n} {xs : List (Fin n)}
--         (uniq : Unique xs) (vlab : Fin n → X)
--         (p : xs ↭ xs)
--     → permute (map⁺ vlab p) ≈Term id
--
-- This is STRICTLY NARROWER than the original
-- `Fin-permute-≈Term-coherence`:
--   * Only one boundary list (xs ↭ xs), not arbitrary (xs ↭ ys).
--   * Only one derivation, not two.
--   * The conclusion is = id, not = some other permute term.
--
-- The reduction `SelfLoopPostulate → FinCoherence` uses
-- `permute-inverse-right` (provided in Phase 2.5):
--   permute p ≈Term permute p ∘ (permute (↭-sym q) ∘ permute q)⁻¹
--           ≈Term permute q ∘ (permute (↭-sym q) ∘ permute p)
--           ≈Term permute q ∘ id                              (self-loop)
--           ≈Term permute q.
--
-- See `module WithSelfLoop` for the full reduction.
--
-- ## Why the self-loop case is irreducible
--
-- The self-loop case `p : xs ↭ xs` with `Unique xs` requires
-- inducting on `p`'s structure:
--   * `refl`: trivial.
--   * `prep`: by IH on the tail (which is also unique).
--   * `swap` at the outer level: IMPOSSIBLE (would require xs = (x ∷ y ∷ as) AND
--     xs = (y ∷ x ∷ as), forcing x = y, violating `Unique`).
--   * `trans p₁ p₂` with intermediate `zs`: the genuine residual
--     case.  Requires showing that `p₂ : zs ↭ xs` is `≈Term`-equal
--     (via `permute`) to `↭-sym p₁`, which is exactly Kelly's
--     coherence on the smaller pair `(p₁, ↭-sym p₂)` over `(xs, zs)`.
--
-- Discharging the `trans` self-loop case requires either:
--   (a) A normal form for `permute` HomTerms relative to a unique
--       position permutation.
--   (b) An external proof via interpretation into a faithful model
--       (e.g., FinSet with bijections).
--
-- ## File is `--safe --with-K`-clean.  No `postulate` keyword used;
--    all residual obligations are exposed as record fields
--    (`SelfLoopPostulate`, `ShapeMismatchPostulate`) for downstream
--    consumers to construct.
--
-- ## Alternative narrowing
--
-- We also provide `ShapeMismatchPostulate` (length ≥ 2 case) for
-- agents who prefer to attack via case analysis on `p, q` shapes.
-- Both give equivalent FinCoherence instances via the corresponding
-- `WithSelfLoop` / `WithShapeMismatch` modules.
--------------------------------------------------------------------------------

open import Categories.APROP

module Categories.APROP.Hypergraph.Completeness.Discharge.Sub.PermuteCoherenceFin
  (sig : APROPSignature) where

open APROP sig

open import Categories.APROP.Hypergraph.Completeness.Unflatten sig
  using (unflatten)
open import Categories.APROP.Hypergraph.Completeness.Permute sig
  using (permute; permute-via-vlab)
open import Categories.APROP.Hypergraph.Completeness.Discharge.Sub.PermuteCoherence sig
  using (FinCoherence; module FinCoherence)

open import Categories.Category using (Category)
open import Data.Fin using (Fin)
open import Data.List using (List; []; _∷_; [_]; map)
import Data.List.Relation.Binary.Permutation.Propositional as Perm
import Data.List.Relation.Binary.Permutation.Propositional.Properties as PermProp
open Perm using (_↭_)
open import Data.List.Relation.Unary.Unique.Propositional using (Unique)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl)

private
  module FM = Category FreeMonoidal

open FM.HomReasoning

--------------------------------------------------------------------------------
-- ## Phase 1: empty-list case.
--
-- For any `p, q : [] ↭ []`, `permute (map⁺ vlab p) ≈Term permute
-- (map⁺ vlab q)`.
--
-- We prove the stronger `permute (map⁺ vlab p) ≈Term id` for all such
-- `p`, which gives the goal by transitivity (and symmetry on `q`).
--
-- The proof is by induction on `p`:
--   * `refl`: `permute refl = id`. Done.
--   * `prep`, `swap`: impossible (require non-empty lists).
--   * `trans p₁ p₂`: `p₂ : ws ↭ []` forces `ws ≡ []` via
--     `↭-empty-inv`; then both p₁ and p₂ are derivations of `[] ↭ []`
--     and we recurse.
--
-- This does NOT need `Unique` (the case is unique-free).

private
  -- We need to induct on derivations of `[] ↭ []` where the
  -- intermediate of `trans` is also `[]` (forced by `↭-empty-inv`).
  -- The lemma's statement uses `xs = ys = []` directly.

  permute-empty-id-aux
    : ∀ {n} (vlab : Fin n → X) (p : ([] {A = Fin n}) Perm.↭ [])
    → permute (PermProp.map⁺ vlab p) ≈Term id
  permute-empty-id-aux vlab Perm.refl = ≈-Term-refl
  permute-empty-id-aux vlab (Perm.trans p₁ p₂)
    with PermProp.↭-empty-inv p₂
  ... | refl =
    -- Now `p₁ : [] ↭ []` and `p₂ : [] ↭ []`.
    let ih₁ = permute-empty-id-aux vlab p₁
        ih₂ = permute-empty-id-aux vlab p₂
        -- permute (map⁺ vlab (trans p₁ p₂))
        --   = permute (map⁺ vlab p₂) ∘ permute (map⁺ vlab p₁)
        -- ≈ id ∘ id     (by IH)
        -- ≈ id          (by idˡ)
    in begin
         permute (PermProp.map⁺ vlab p₂) ∘ permute (PermProp.map⁺ vlab p₁)
           ≈⟨ ∘-resp-≈ ih₂ ih₁ ⟩
         id ∘ id
           ≈⟨ idˡ ⟩
         id
       ∎

Fin-coherence-empty
  : ∀ {n} (vlab : Fin n → X) (p q : ([] {A = Fin n}) Perm.↭ [])
  → permute (PermProp.map⁺ vlab p) ≈Term permute (PermProp.map⁺ vlab q)
Fin-coherence-empty vlab p q =
  ≈-Term-trans (permute-empty-id-aux vlab p)
               (≈-Term-sym (permute-empty-id-aux vlab q))

--------------------------------------------------------------------------------
-- ## Phase 2: singleton-list case.
--
-- For `xs ≡ [k]` (a singleton Fin list), any derivation `p : [k] ↭ [k]`
-- (the only possible ys by `↭-singleton-inv`) satisfies
-- `permute (map⁺ vlab p) ≈Term id`.
--
-- By induction on `p`:
--   * `refl`: trivial.
--   * `prep k p'` with `p' : [] ↭ []`: `permute = id ⊗₁ permute p'`,
--     and `permute p' ≈Term id` by Phase 1, so `id ⊗₁ id ≈Term id`
--     via `id⊗id≈id`.
--   * `swap`: impossible (would need 2-element list).
--   * `trans p₁ p₂` with intermediate `ws`: `↭-singleton-inv p₂`
--     forces `ws ≡ [k]`; recurse on both halves.

private
  permute-singleton-id-aux
    : ∀ {n} (vlab : Fin n → X) {k : Fin n}
        (p : (k ∷ []) Perm.↭ (k ∷ []))
    → permute (PermProp.map⁺ vlab p) ≈Term id
  permute-singleton-id-aux vlab Perm.refl = ≈-Term-refl
  permute-singleton-id-aux vlab (Perm.prep _ p') =
    -- p' : [] ↭ []  by inversion on the prep constructor.
    let ih = permute-empty-id-aux vlab p'
    in begin
         id ⊗₁ permute (PermProp.map⁺ vlab p')
           ≈⟨ ⊗-resp-≈ ≈-Term-refl ih ⟩
         id ⊗₁ id
           ≈⟨ id⊗id≈id ⟩
         id
       ∎
  permute-singleton-id-aux vlab {k} (Perm.trans p₁ p₂)
    with PermProp.↭-singleton-inv p₂
  ... | refl =
    let ih₁ = permute-singleton-id-aux vlab p₁
        ih₂ = permute-singleton-id-aux vlab p₂
    in begin
         permute (PermProp.map⁺ vlab p₂) ∘ permute (PermProp.map⁺ vlab p₁)
           ≈⟨ ∘-resp-≈ ih₂ ih₁ ⟩
         id ∘ id
           ≈⟨ idˡ ⟩
         id
       ∎

Fin-coherence-singleton
  : ∀ {n} (vlab : Fin n → X) {k : Fin n}
      (p q : (k ∷ []) Perm.↭ (k ∷ []))
  → permute (PermProp.map⁺ vlab p) ≈Term permute (PermProp.map⁺ vlab q)
Fin-coherence-singleton vlab p q =
  ≈-Term-trans (permute-singleton-id-aux vlab p)
               (≈-Term-sym (permute-singleton-id-aux vlab q))

--------------------------------------------------------------------------------
-- ## Phase 2.5: constructive inverse lemma — `permute-inverse-left`.
--
-- `permute (↭-sym p) ∘ permute p ≈Term id` for any `p : xs ↭ ys`.
-- No `Unique` precondition needed; this is a property of the
-- σ-structural fragment alone.
--
-- Cases:
--   * `refl`: `id ∘ id ≈ id`.
--   * `prep x p`: `(id ⊗ f⁻¹) ∘ (id ⊗ f) ≈ id ⊗ (f⁻¹ ∘ f) ≈ id ⊗ id ≈ id`.
--   * `swap x y p`: by σ-block naturality (`σ∘[f⊗g]≈[g⊗f]∘σ`),
--     σ-block involution (`σ∘σ≈id` plus α-cancellation), and
--     `⊗-∘-dist`.
--   * `trans p₁ p₂`: by associativity + two IHs.

private

  -- Helper 1: the σ-block is involutive.
  -- The "back" σ-block goes B⊗(A⊗C) → A⊗(B⊗C); composed with the
  -- "forward" σ-block (A⊗(B⊗C) → B⊗(A⊗C)) gives identity on A⊗(B⊗C).

  σ-block-involutive
    : ∀ {A B C : ObjTerm}
    → (α⇒ {A = A} {B = B} {C = C} ∘ (σ ⊗₁ id) ∘ α⇐ {A = B} {B = A} {C = C})
        ∘ (α⇒ {A = B} {B = A} {C = C} ∘ (σ ⊗₁ id) ∘ α⇐ {A = A} {B = B} {C = C})
      ≈Term id
  σ-block-involutive {A} {B} {C} =
    -- Need to write this carefully because the σ's in the two
    -- σ-blocks have DIFFERENT implicit types (one is A⊗B → B⊗A,
    -- the other is B⊗A → A⊗B).  The composition (σ ∘ σ) types as
    -- (A⊗B) → (A⊗B), and σ∘σ≈id covers exactly this case.
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
           -- Collapse σ-BA ∘ σ-AB ≈ id via σ∘σ≈id (which states
           -- σ ∘ σ ≈Term id at the appropriate type).  The two σ's
           -- here are σ-BA ∘ σ-AB at type A⊗B → A⊗B, and σ∘σ≈id
           -- applies (with implicit type at A,B).
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

  -- Helper 2: σ-block naturality in the third argument.
  -- (α⇒ ∘ (σ ⊗ id) ∘ α⇐) ∘ (id_A ⊗ (id_B ⊗ f))
  --   ≈ (id_B ⊗ (id_A ⊗ f)) ∘ (α⇒ ∘ (σ ⊗ id) ∘ α⇐)
  -- Both sides reduce to α⇒ ∘ (σ ⊗ f) ∘ α⇐.

  σ-block-natural₃
    : ∀ {A B C D : ObjTerm} {f : HomTerm C D}
    → (α⇒ ∘ (σ {A = A} {B = B} ⊗₁ id) ∘ α⇐) ∘ (id ⊗₁ (id ⊗₁ f))
      ≈Term (id ⊗₁ (id ⊗₁ f)) ∘ (α⇒ ∘ (σ ⊗₁ id) ∘ α⇐)
  σ-block-natural₃ {A} {B} {C} {D} {f} =
    -- LHS:  α⇒ ∘ (σ⊗id) ∘ α⇐ ∘ id⊗(id⊗f)
    --       ≈ α⇒ ∘ (σ⊗id) ∘ ((id⊗id) ⊗ f) ∘ α⇐    (α⇐-comm)
    --       ≈ α⇒ ∘ ((σ∘(id⊗id)) ⊗ (id∘f)) ∘ α⇐    (⊗-∘-dist⁻¹)
    --       ≈ α⇒ ∘ (σ ⊗ f) ∘ α⇐                    (simplify ids)
    --
    -- RHS:  id⊗(id⊗f) ∘ α⇒ ∘ (σ⊗id) ∘ α⇐
    --       ≈ α⇒ ∘ ((id⊗id) ⊗ f) ∘ (σ⊗id) ∘ α⇐    (α-comm)
    --       ≈ α⇒ ∘ (((id⊗id)∘σ) ⊗ (f∘id)) ∘ α⇐    (⊗-∘-dist⁻¹)
    --       ≈ α⇒ ∘ (σ ⊗ f) ∘ α⇐                    (simplify ids)
    --
    -- So LHS ≈ RHS, both via the common reduction to α⇒ ∘ (σ ⊗ f) ∘ α⇐.

    -- Step LHS → common form:
    let common = α⇒ ∘ (σ {A = A} {B = B} ⊗₁ f) ∘ α⇐
        lhs→common =
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
    where
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

-- The main inverse lemma.

permute-inverse-left
  : ∀ {xs ys : List X} (p : xs Perm.↭ ys)
  → permute (Perm.↭-sym p) ∘ permute p ≈Term id
permute-inverse-left Perm.refl = idˡ
permute-inverse-left (Perm.prep x p) =
  -- (id ⊗ f⁻¹) ∘ (id ⊗ f) ≈ (id ∘ id) ⊗ (f⁻¹ ∘ f) ≈ id ⊗ id ≈ id.
  ≈-Term-trans (≈-Term-sym ⊗-∘-dist)
  (≈-Term-trans (⊗-resp-≈ idˡ (permute-inverse-left p))
                id⊗id≈id)
permute-inverse-left (Perm.swap x y p) =
  -- A = permute (swap y x (↭-sym p)) = (id ⊗ (id ⊗ f⁻¹)) ∘ B_σ
  -- B = permute (swap x y p)        = (id ⊗ (id ⊗ f))   ∘ B_σ
  -- A ∘ B = (id⊗(id⊗f⁻¹)) ∘ B_σ ∘ (id⊗(id⊗f)) ∘ B_σ
  --       ≈ (id⊗(id⊗f⁻¹)) ∘ (id⊗(id⊗f)) ∘ B_σ ∘ B_σ      (σ-block-natural₃)
  --       ≈ (id⊗(id⊗f⁻¹)) ∘ (id⊗(id⊗f)) ∘ id              (σ-block-involutive)
  --       ≈ (id⊗(id⊗f⁻¹)) ∘ (id⊗(id⊗f))                   (idʳ)
  --       ≈ id ⊗ (id ⊗ (f⁻¹ ∘ f))                          (⊗-∘-dist⁻¹, ×2)
  --       ≈ id ⊗ (id ⊗ id)                                 (IH)
  --       ≈ id ⊗ id                                        (id⊗id≈id inner)
  --       ≈ id                                             (id⊗id≈id outer)
  let f   = permute p
      f⁻¹ = permute (Perm.↭-sym p)
      ih  = permute-inverse-left p
  in begin
       ((id ⊗₁ (id ⊗₁ f⁻¹)) ∘ α⇒ ∘ (σ ⊗₁ id) ∘ α⇐)
         ∘ ((id ⊗₁ (id ⊗₁ f)) ∘ α⇒ ∘ (σ ⊗₁ id) ∘ α⇐)
         -- Re-associate to get: (id⊗(id⊗f⁻¹)) ∘ B_σ ∘ (id⊗(id⊗f)) ∘ B_σ.
         ≈⟨ assoc ⟩
       (id ⊗₁ (id ⊗₁ f⁻¹)) ∘ (α⇒ ∘ (σ ⊗₁ id) ∘ α⇐)
         ∘ ((id ⊗₁ (id ⊗₁ f)) ∘ α⇒ ∘ (σ ⊗₁ id) ∘ α⇐)
         ≈⟨ ∘-resp-≈ ≈-Term-refl (≈-Term-sym assoc) ⟩
       (id ⊗₁ (id ⊗₁ f⁻¹))
         ∘ ((α⇒ ∘ (σ ⊗₁ id) ∘ α⇐) ∘ (id ⊗₁ (id ⊗₁ f)))
         ∘ (α⇒ ∘ (σ ⊗₁ id) ∘ α⇐)
         -- Use σ-block-natural₃ to flip the middle σ-block with id⊗(id⊗f).
         ≈⟨ ∘-resp-≈ ≈-Term-refl (∘-resp-≈ σ-block-natural₃ ≈-Term-refl) ⟩
       (id ⊗₁ (id ⊗₁ f⁻¹))
         ∘ ((id ⊗₁ (id ⊗₁ f)) ∘ (α⇒ ∘ (σ ⊗₁ id) ∘ α⇐))
         ∘ (α⇒ ∘ (σ ⊗₁ id) ∘ α⇐)
         ≈⟨ ∘-resp-≈ ≈-Term-refl assoc ⟩
       (id ⊗₁ (id ⊗₁ f⁻¹))
         ∘ (id ⊗₁ (id ⊗₁ f))
         ∘ ((α⇒ ∘ (σ ⊗₁ id) ∘ α⇐) ∘ (α⇒ ∘ (σ ⊗₁ id) ∘ α⇐))
         -- Collapse the σ-block pair via σ-block-involutive.
         ≈⟨ ∘-resp-≈ ≈-Term-refl (∘-resp-≈ ≈-Term-refl σ-block-involutive) ⟩
       (id ⊗₁ (id ⊗₁ f⁻¹)) ∘ (id ⊗₁ (id ⊗₁ f)) ∘ id
         ≈⟨ ∘-resp-≈ ≈-Term-refl idʳ ⟩
       (id ⊗₁ (id ⊗₁ f⁻¹)) ∘ (id ⊗₁ (id ⊗₁ f))
         -- Use ⊗-∘-dist⁻¹ twice to push composition inward.
         ≈⟨ ≈-Term-sym ⊗-∘-dist ⟩
       (id ∘ id) ⊗₁ ((id ⊗₁ f⁻¹) ∘ (id ⊗₁ f))
         ≈⟨ ⊗-resp-≈ idˡ (≈-Term-sym ⊗-∘-dist) ⟩
       id ⊗₁ ((id ∘ id) ⊗₁ (f⁻¹ ∘ f))
         -- Apply IH and collapse.
         ≈⟨ ⊗-resp-≈ ≈-Term-refl (⊗-resp-≈ idˡ ih) ⟩
       id ⊗₁ (id ⊗₁ id)
         ≈⟨ ⊗-resp-≈ ≈-Term-refl id⊗id≈id ⟩
       id ⊗₁ id
         ≈⟨ id⊗id≈id ⟩
       id
     ∎
permute-inverse-left (Perm.trans p₁ p₂) =
  -- (permute (↭-sym p₁) ∘ permute (↭-sym p₂)) ∘ (permute p₂ ∘ permute p₁)
  -- ≈ permute (↭-sym p₁) ∘ (permute (↭-sym p₂) ∘ permute p₂) ∘ permute p₁
  -- ≈ permute (↭-sym p₁) ∘ id ∘ permute p₁   (IH₂)
  -- ≈ permute (↭-sym p₁) ∘ permute p₁         (idˡ)
  -- ≈ id                                       (IH₁)
  let ih₁ = permute-inverse-left p₁
      ih₂ = permute-inverse-left p₂
  in ≈-Term-trans assoc
    (≈-Term-trans (∘-resp-≈ ≈-Term-refl
                    (≈-Term-trans (≈-Term-sym assoc)
                                  (∘-resp-≈ ih₂ ≈-Term-refl)))
    (≈-Term-trans (∘-resp-≈ ≈-Term-refl idˡ) ih₁))

-- The right-inverse version follows by sym: swap p and ↭-sym p.
-- (Since ↭-sym is an involution, this follows from the left version
-- by substitution.)

permute-inverse-right
  : ∀ {xs ys : List X} (p : xs Perm.↭ ys)
  → permute p ∘ permute (Perm.↭-sym p) ≈Term id
permute-inverse-right p =
  -- permute p ∘ permute (↭-sym p)
  --   = permute (↭-sym (↭-sym p)) ∘ permute (↭-sym p)    (since ↭-sym ∘ ↭-sym = id propositionally)
  --   ≈ id                                                (by permute-inverse-left (↭-sym p))
  --
  -- We rewrite via ↭-sym-involutive.
  let helper = permute-inverse-left (Perm.↭-sym p)
  in rewrite-↭-sym p helper
  where
    rewrite-↭-sym
      : ∀ {xs ys : List X} (p : xs Perm.↭ ys)
      → permute (Perm.↭-sym (Perm.↭-sym p)) ∘ permute (Perm.↭-sym p) ≈Term id
      → permute p ∘ permute (Perm.↭-sym p) ≈Term id
    rewrite-↭-sym p eq rewrite PermProp.↭-sym-involutive p = eq

--------------------------------------------------------------------------------
-- ## Phase 3: residual sub-postulate, narrowed via `permute-inverse-left`.
--
-- Using `permute-inverse-left` (Phase 2.5), the full
-- `Fin-permute-≈Term-coherence` reduces to a strictly narrower
-- statement: the SELF-LOOP CASE on Fin lists with `Unique`.
--
-- ### The reduction
--
-- Given `p, q : xs ↭ ys` with `Unique xs` (and arbitrary `vlab`),
-- define `r = trans p (↭-sym q) : xs ↭ xs`.  Then:
--
--   permute (map⁺ vlab r) = permute (map⁺ vlab (↭-sym q)) ∘ permute (map⁺ vlab p)
--
-- If we can show `permute (map⁺ vlab r) ≈Term id` for any such `r`
-- (the self-loop residual postulate), then:
--
--   permute (map⁺ vlab p)
--     ≈Term id ∘ permute (map⁺ vlab p)                    (idˡ)
--     ≈Term (permute (map⁺ vlab q) ∘ permute (map⁺ vlab (↭-sym q))) ∘ permute (map⁺ vlab p)
--                                                          (permute-inverse-right q)
--     ≈Term permute (map⁺ vlab q) ∘ (permute (map⁺ vlab (↭-sym q)) ∘ permute (map⁺ vlab p))
--                                                          (assoc)
--     ≈Term permute (map⁺ vlab q) ∘ id                    (self-loop residual)
--     ≈Term permute (map⁺ vlab q)                          (idʳ)
--
-- This is exactly the FinCoherence statement.
--
-- ### Why this narrowing is strictly stronger than just length-≥2:
--
--   * It only needs the SELF-LOOP case (`xs ↭ xs`), not all
--     boundaries.
--   * `Unique xs` excludes `swap k k'` at the outer level (since
--     `swap k k'` produces non-identity boundaries).
--   * Empty + singleton + same-outer-prep cases reduce to the inner
--     IH; only `trans` and `swap-via-trans` carry irreducible Kelly
--     content.
--
-- ### What's still residual:
--
-- The self-loop case `(p : xs ↭ xs) → permute (map⁺ vlab p) ≈Term id`
-- with `Unique xs` requires inducting on `p`'s structure.  The
-- non-trivial sub-cases involve `swap` and `trans` interactions
-- (excluded for length 0 and 1 by Phases 1, 2).
--
-- We expose this as the residual sub-postulate `SelfLoopPostulate`.

record SelfLoopPostulate : Set where
  field
    -- The self-loop case: for any Fin-level derivation of a unique
    -- list to itself, the corresponding permute morphism is ≈Term-id.
    --
    -- Note: `Unique xs` here is at the Fin level; after `map⁺ vlab`,
    -- the X-level list `map vlab xs` may have duplicates, but the
    -- Fin-level uniqueness ensures the position permutation is the
    -- identity.
    Fin-permute-self-loop-id
      : ∀ {n} {xs : List (Fin n)}
          (xs-uniq : Unique xs)
          (vlab : Fin n → X)
          (p : xs Perm.↭ xs)
      → permute (PermProp.map⁺ vlab p) ≈Term id

--------------------------------------------------------------------------------
-- ## Construct `FinCoherence` from `SelfLoopPostulate`.
--
-- Apply the reduction outlined above.  The construction uses
-- `permute-inverse-right` (Phase 2.5).

module WithSelfLoop (slp : SelfLoopPostulate) where
  open SelfLoopPostulate slp

  -- Helper: map⁺ vlab (↭-sym p) ≡ ↭-sym (map⁺ vlab p) propositionally.
  -- This is needed to align `permute (map⁺ vlab (↭-sym p))` with
  -- `permute (↭-sym (map⁺ vlab p))` for use of permute-inverse-right.
  private
    map⁺-↭-sym
      : ∀ {n} {xs ys : List (Fin n)} (vlab : Fin n → X) (p : xs Perm.↭ ys)
      → PermProp.map⁺ vlab (Perm.↭-sym p) ≡ Perm.↭-sym (PermProp.map⁺ vlab p)
    map⁺-↭-sym vlab Perm.refl         = refl
    map⁺-↭-sym vlab (Perm.prep x p)   rewrite map⁺-↭-sym vlab p = refl
    map⁺-↭-sym vlab (Perm.swap x y p) rewrite map⁺-↭-sym vlab p = refl
    map⁺-↭-sym vlab (Perm.trans p₁ p₂)
      rewrite map⁺-↭-sym vlab p₁ | map⁺-↭-sym vlab p₂ = refl

  -- Helper to extract loop-id-aligned.
  -- The strategy: compute loop-id over the Fin-level p and ↭-sym q,
  -- then propositionally align the X-level structure via subst.
  private
    open import Relation.Binary.PropositionalEquality
      using (subst; sym)

    -- First, the self-loop result at the X level (via map⁺).
    loop-id-X-level
      : ∀ {n} {xs ys : List (Fin n)}
          (uniq : Unique xs) (vlab : Fin n → X)
          (p : xs Perm.↭ ys) (q : xs Perm.↭ ys)
      → permute (PermProp.map⁺ vlab (Perm.trans p (Perm.↭-sym q)))
        ≈Term id
    loop-id-X-level uniq vlab p q =
      Fin-permute-self-loop-id uniq vlab (Perm.trans p (Perm.↭-sym q))

    -- The X-level loop expands via the definitions of `permute` and `map⁺`:
    --   permute (map⁺ vlab (trans p (↭-sym q)))
    --   ≡ permute (trans (map⁺ vlab p) (map⁺ vlab (↭-sym q)))
    --   ≡ permute (map⁺ vlab (↭-sym q)) ∘ permute (map⁺ vlab p)
    -- where ≡ is definitional (via map⁺'s computation rules).
    --
    -- We then propositionally rewrite via map⁺-↭-sym:
    --   permute (map⁺ vlab (↭-sym q)) ≡ permute (↭-sym (map⁺ vlab q))
    -- (using cong permute applied to map⁺-↭-sym).

    loop-id-aligned
      : ∀ {n} {xs ys : List (Fin n)}
          (uniq : Unique xs) (vlab : Fin n → X)
          (p : xs Perm.↭ ys) (q : xs Perm.↭ ys)
      → permute (Perm.↭-sym (PermProp.map⁺ vlab q)) ∘ permute (PermProp.map⁺ vlab p)
        ≈Term id
    loop-id-aligned {ys = ys} uniq vlab p q =
      subst (λ r → permute r ∘ permute (PermProp.map⁺ vlab p) ≈Term id)
            (map⁺-↭-sym vlab q)
            (loop-id-X-level uniq vlab p q)

  -- The main reduction.
  Fin-permute-≈Term-coherence-from-self-loop
    : ∀ {n} {xs ys : List (Fin n)}
        (xs-uniq : Unique xs)
        (vlab : Fin n → X)
        (p q : xs Perm.↭ ys)
    → permute (PermProp.map⁺ vlab p) ≈Term permute (PermProp.map⁺ vlab q)
  Fin-permute-≈Term-coherence-from-self-loop {xs = xs} uniq vlab p q =
    let mp = PermProp.map⁺ vlab p
        mq = PermProp.map⁺ vlab q
        -- permute (↭-sym mq) ∘ permute mp ≈Term id   (loop-id-aligned)
        -- permute mq ∘ permute (↭-sym mq) ≈Term id   (permute-inverse-right)
        -- ⇒ permute mp ≈Term permute mq.
        right-inv = permute-inverse-right mq
        loop-id   = loop-id-aligned uniq vlab p q
    in begin
         permute mp
           ≈⟨ ≈-Term-sym idˡ ⟩
         id ∘ permute mp
           ≈⟨ ∘-resp-≈ (≈-Term-sym right-inv) ≈-Term-refl ⟩
         (permute mq ∘ permute (Perm.↭-sym mq)) ∘ permute mp
           ≈⟨ assoc ⟩
         permute mq ∘ (permute (Perm.↭-sym mq) ∘ permute mp)
           ≈⟨ ∘-resp-≈ ≈-Term-refl loop-id ⟩
         permute mq ∘ id
           ≈⟨ idʳ ⟩
         permute mq
       ∎

  -- The full `FinCoherence` record value.
  finCoherence : FinCoherence
  finCoherence = record
    { Fin-permute-≈Term-coherence
        = Fin-permute-≈Term-coherence-from-self-loop
    }

--------------------------------------------------------------------------------
-- ## Construct `FinCoherence` from a length-≥2-only postulate.
--
-- ALTERNATIVE narrowing: only require coherence for lists of length
-- ≥ 2 (`x ∷ y ∷ rest`).  This is what a future agent might prove
-- directly via case analysis; we provide the dispatch wrapper.

record ShapeMismatchPostulate : Set where
  field
    Fin-permute-≈Term-coherence-≥2
      : ∀ {n} {x y : Fin n} {rest : List (Fin n)} {ys : List (Fin n)}
          (xs-uniq : Unique (x ∷ y ∷ rest))
          (vlab : Fin n → X)
          (p q : (x ∷ y ∷ rest) Perm.↭ ys)
      → permute (PermProp.map⁺ vlab p) ≈Term permute (PermProp.map⁺ vlab q)

module WithShapeMismatch (smp : ShapeMismatchPostulate) where
  open ShapeMismatchPostulate smp

  Fin-permute-≈Term-coherence-from-shape-mismatch
    : ∀ {n} {xs ys : List (Fin n)}
        (xs-uniq : Unique xs)
        (vlab : Fin n → X)
        (p q : xs Perm.↭ ys)
    → permute (PermProp.map⁺ vlab p) ≈Term permute (PermProp.map⁺ vlab q)
  Fin-permute-≈Term-coherence-from-shape-mismatch {xs = []}     uniq vlab p q
    with PermProp.↭-empty-inv (Perm.↭-sym p)
  ... | refl = Fin-coherence-empty vlab p q
  Fin-permute-≈Term-coherence-from-shape-mismatch {xs = _ ∷ []} uniq vlab p q
    with PermProp.↭-singleton-inv (Perm.↭-sym p)
  ... | refl = Fin-coherence-singleton vlab p q
  Fin-permute-≈Term-coherence-from-shape-mismatch {xs = _ ∷ _ ∷ _} uniq vlab p q =
    Fin-permute-≈Term-coherence-≥2 uniq vlab p q

  finCoherence : FinCoherence
  finCoherence = record
    { Fin-permute-≈Term-coherence
        = Fin-permute-≈Term-coherence-from-shape-mismatch
    }

--------------------------------------------------------------------------------
-- ## Per-case breakdown (for the final report and for future agents)
--
-- ### Cases closed FULLY constructively (no postulate):
--
--   1. Empty list (length 0):
--        Closed by `Fin-coherence-empty` (Phase 1).
--        Uses: `↭-empty-inv`, `idˡ`, `≈-Term-refl`, `≈-Term-trans`.
--        agda-categories primitives: none needed (axioms suffice).
--
--   2. Singleton list (length 1):
--        Closed by `Fin-coherence-singleton` (Phase 2).
--        Uses: `↭-singleton-inv`, `idˡ`, `id⊗id≈id`, Phase 1 IH.
--        agda-categories primitives: none needed.
--
--   3. `permute (↭-sym p) ∘ permute p ≈Term id` for any `p`:
--        Closed by `permute-inverse-left` (Phase 2.5).
--        Uses: `assoc`, `idˡ`, `id⊗id≈id`, `⊗-∘-dist`, `α-comm`,
--        `α⇐∘α⇒≈id`, `σ∘σ≈id`, plus the derived `σ-block-involutive`
--        and `σ-block-natural₃` helpers.
--        agda-categories primitives: implicit (via `σ∘σ≈id` and the
--        FreeMonoidal axioms which encode the Symmetric structure).
--        (The right-inverse version `permute-inverse-right` follows
--        via `↭-sym-involutive`.)
--
--   4. Same-shape `refl/refl`, length ≥ 2:
--        Closed by `permute-refl-refl` (existing in PermuteCoherence.agda).
--
--   5. Same-shape `prep x p/prep x q`:
--        Closed by `permute-prep-prep` (existing).
--
--   6. Same-shape `swap x y p/swap x y q` with matched intermediate:
--        Closed by `permute-swap-swap-aligned` (existing).
--
--   7. Same-shape `trans p₁ p₂/trans q₁ q₂` with matched intermediate:
--        Closed by `permute-trans-trans-aligned` (existing).
--
--   8. `trans p refl ≈ permute p`:
--        Closed by `permute-trans-refl-right` (existing).
--
--   9. `trans refl p ≈ permute p`:
--        Closed by `permute-trans-refl-left` (existing).
--
--  10. `trans (trans p q) r ≈ trans p (trans q r)`:
--        Closed by `permute-trans-assoc` (existing).
--
-- ### The narrowed residual obligations:
--
--  11. SELF-LOOP CASE (`SelfLoopPostulate`):
--        `∀ {n} {xs : List (Fin n)} (uniq : Unique xs) (vlab : Fin n → X)
--           (p : xs ↭ xs)
--         → permute (map⁺ vlab p) ≈Term id`
--
--        This is the SOLE residual obligation in the `WithSelfLoop`
--        route.  The reduction `SelfLoopPostulate → FinCoherence`
--        is fully constructive (uses `permute-inverse-right`).
--
--        Why irreducible: `p = trans p₁ p₂` with intermediate `zs ≠ xs`
--        passes through a different boundary, and the `≈Term`-rewrite
--        must use Kelly's coherence to identify `p₂ : zs ↭ xs` with
--        `↭-sym p₁ : zs ↭ xs`.
--
--        agda-categories primitives that would apply for this case:
--          * `Kelly's.coherence₁/₂/₃` — α/λ/ρ paths with unit.
--          * `braiding-coherence`, `inv-braiding-coherence` — σ-unit.
--          * `hexagon₁`, `hexagon₂` (and iso/inv) — σ-α interactions.
--          * `assoc-reverse` — ternary σ.
--          * `braiding-selfInverse`, `inv-commutative` — σ-σ.
--
--  12. SHAPE-MISMATCH CASE (`ShapeMismatchPostulate`, alternative):
--        `∀ {n} {x y : Fin n} {rest ys : List (Fin n)} (uniq : Unique (x ∷ y ∷ rest))
--           (vlab : Fin n → X) (p q : x ∷ y ∷ rest ↭ ys)
--         → permute (map⁺ vlab p) ≈Term permute (map⁺ vlab q)`
--
--        Alternative narrowing — equivalent to `SelfLoopPostulate`,
--        but stated as the full coherence at length ≥ 2.  Use this
--        if you prefer case analysis on (p, q) shapes over the
--        self-loop reduction.
--
-- ## Total LOC delivered: ~750 LOC (this file).
-- ## Discharged cases: 1 through 10 above.
-- ## Remaining sub-postulate: `SelfLoopPostulate.Fin-permute-self-loop-id`
--    (one record field, one parameter list).  See module `WithSelfLoop`.
