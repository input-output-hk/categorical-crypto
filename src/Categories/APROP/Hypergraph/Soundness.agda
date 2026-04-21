{-# OPTIONS --without-K #-}

--------------------------------------------------------------------------------
-- Soundness of the APROP-to-hypergraph translation:
--
--   soundness : f ≈Term g  →  ⟪ f ⟫ ≅ᴴ ⟪ g ⟫
--
-- Proof by induction on the `_≈Term_` derivation.
--
-- STATUS:
--   * Equivalence closure (`≈-Term-refl`, `≈-Term-sym`, `≈-Term-trans`):
--     COMPLETE, via `refl-≅ᴴ`, `sym-≅ᴴ`, `trans-≅ᴴ` from
--     `Categories.APROP.Hypergraph.Iso`.
--
--   * Congruence rules (`∘-resp-≈`, `⊗-resp-≈`): COMPLETE, via
--     `hCompose-resp-≅ᴴ` and `hTensor-resp-≅ᴴ` from
--     `Categories.APROP.Hypergraph.Congruence`.
--
--   * `id⊗id≈id`: COMPLETE via `refl-≅ᴴ`. Holds because `hId (A ⊗₀ B)`
--     unfolds definitionally to `hTensor (hId A) (hId B)` (see
--     `FromAPROP.hId`).
--
--   * Atomic axioms: POSTULATED as a single catch-all `soundness-axiom`
--     that covers all 18 `≈Term` constructors that aren't congruence or
--     equivalence rules. Per-constructor splitting was tried but runs
--     into an unification snag: `⟪_⟫` is defined by pattern matching,
--     so `⟪ id ∘ f ⟫ ≡ ⟪ id ∘ f' ⟫` does not force `f ≡ f'` and Agda
--     leaves the implicit arguments of the per-axiom postulates
--     unsolved.
--
-- Classification of the 18 atomic axioms by whether LHS and RHS have
-- the same number of vertices in the translated hypergraphs. Blocked
-- on _≅ᴴ_ refinement (see TODO.org):
--
--   (a) Equal vertex count (only the `+` re-association or shape-swap
--       of the vertex set differs; no refactor of `hCompose` is
--       needed, but the bijection proofs are still non-trivial):
--         `assoc`         : (nf+ng)+nh = nf+(ng+nh)
--         `⊗-∘-dist`     : (nf+ng)+(nf'+ng') = (nf+nf')+(ng+ng')
--         `hexagon`       : 3·(|A|+|B|+|C|) on both sides
--
--   (b) LHS has strictly more vertices than RHS — LHS contains an
--       extra identity-hypergraph factor whose K-side vertices become
--       dangling after `hCompose`. Discharging these requires TODO
--       Option A (prune dangling K-dom vertices in `hCompose`) or
--       Option B (coarsen `_≅ᴴ_` to allow vertex merging):
--         `idˡ`, `idʳ`,
--         `λ⇐∘λ⇒≈id`, `λ⇒∘λ⇐≈id`, `ρ⇐∘ρ⇒≈id`, `ρ⇒∘ρ⇐≈id`,
--         `α⇐∘α⇒≈id`, `α⇒∘α⇐≈id`, `σ∘σ≈id`, `triangle`, `pentagon`
--
--   (c) LHS and RHS have different vertex counts in general
--       (depending on the APROP signature) — naturality + unitor/
--       associator/braiding laws, where two different coherence
--       morphisms appear on each side. Same blocker as (b):
--         `λ⇒∘id⊗f≈f∘λ⇒`, `ρ⇒∘f⊗id≈f∘ρ⇒`, `α-comm`,
--         `σ∘[f⊗g]≈[g⊗f]∘σ`
--
-- Because this file depends on the postulate, it is not `--safe` and
-- is not transitively imported by `CategoricalCrypto.agda`.
--------------------------------------------------------------------------------

open import Categories.APROP

module Categories.APROP.Hypergraph.Soundness (sig : APROPSignature) where

open APROP sig
open import Categories.APROP.Hypergraph.Core
open import Categories.APROP.Hypergraph.FromAPROP sig
open import Categories.APROP.Hypergraph.Iso
open import Categories.APROP.Hypergraph.Congruence sig

--------------------------------------------------------------------------------
-- Catch-all postulate for the 18 atomic axioms.

postulate
  soundness-axiom : ∀ {A B} {f g : HomTerm A B} → f ≈Term g → ⟪ f ⟫ ≅ᴴ ⟪ g ⟫

--------------------------------------------------------------------------------
-- The soundness theorem.

soundness : ∀ {A B} {f g : HomTerm A B} → f ≈Term g → ⟪ f ⟫ ≅ᴴ ⟪ g ⟫

-- Equivalence closure.
soundness ≈-Term-refl         = refl-≅ᴴ _
soundness (≈-Term-sym  p)     = sym-≅ᴴ (soundness p)
soundness (≈-Term-trans p q)  = trans-≅ᴴ (soundness p) (soundness q)

-- Congruence for composition. Note the argument order swap: the
-- APROP term `f ∘ g` (f after g) translates to `hCompose ⟪g⟫ ⟪f⟫`
-- (g composed first, then f).
soundness (∘-resp-≈ pf pg)    = hCompose-resp-≅ᴴ (soundness pg) (soundness pf)

-- Congruence for tensor.
soundness (⊗-resp-≈ pf pg)    = hTensor-resp-≅ᴴ (soundness pf) (soundness pg)

-- `id ⊗ id ≈ id` at `A ⊗₀ B` is a definitional equality of
-- hypergraphs: `hId (A ⊗₀ B) = hTensor (hId A) (hId B)`.
soundness id⊗id≈id            = refl-≅ᴴ _

-- Atomic axioms. See module header for the classification.
soundness p                   = soundness-axiom p
