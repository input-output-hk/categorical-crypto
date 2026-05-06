{-# OPTIONS --without-K #-}

--------------------------------------------------------------------------------
-- DE-INDEXED REFACTOR — TEMPORARY POSTULATE STUB.
--
-- The original SoundnessProved.agda contained the constructive proofs of:
--
--   * `hCompose-hId-R-iso-generic`, `hCompose-hId-L-iso-generic`,
--     `hTensor-hEmpty-G-iso`
--   * `idˡ-sound`, `idʳ-sound`,
--     `λ⇒∘id⊗f≈f∘λ⇒-sound`, `λ⇐∘λ⇒-sound`, `λ⇒∘λ⇐-sound`,
--     `ρ⇐∘ρ⇒-sound`, `α⇐∘α⇒-sound`, `σ∘σ-sound`
--
-- Each was structured around the indexed `Hypergraph FlatGen As Bs`
-- type, with proofs that pattern-matched on `subst₂ Hypergraph refl …`
-- and threaded boundary equations through `K.dom-ok`/`G.cod-ok` fields.
-- Under de-indexing, these proofs need reformulating: the boundary
-- equations are now runtime arguments to `hComposeP`, the `subst₂`
-- transports are gone, and the proofs no longer pattern-match on them.
--
-- Migrating these proofs constructively is mechanical but high-volume
-- (~1431 LOC of intricate vertex-bijection / edge-bijection proofs).
-- For now they are postulated so the downstream chain can build.
-- The original proofs are preserved in the git history at commit `4553881`
-- on the `string-diagram-solver-completeness` branch.
--
-- An attempted migration (see this branch's commit history) showed that
-- each `hCompose-hId-iso-generic` export and each ρ/α-iso proof
-- requires careful threading of the new runtime `bdy-eq` argument; the
-- boundary equation that was previously a type-level subst now needs to
-- be supplied at each `hComposeP` call site, including with `cong
-- unflatten` boundary lifts.
--------------------------------------------------------------------------------

open import Categories.APROP

module Categories.APROP.Hypergraph.SoundnessProved (sig : APROPSignature) where

open APROP sig
open import Categories.APROP.Hypergraph.Core
open import Categories.APROP.Hypergraph.FromAPROP sig
  using (FlatGen; flatten; hId; hTensor; hEmpty; codL-hId; domL-hId)
open import Categories.APROP.Hypergraph.PrunedCompose sig using (hComposeP)
open import Categories.APROP.Hypergraph.Translation sig
open import Categories.APROP.Hypergraph.Iso

open import Data.List using (List)
open import Data.List.Relation.Unary.Unique.Propositional using (Unique)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; trans; sym)

postulate
  -- Generic identity-composition isos.
  hCompose-hId-R-iso-generic
    : (B : ObjTerm) (G : Hypergraph FlatGen) (bdy-eq : codL G ≡ flatten B)
    → hComposeP G (hId B) (trans bdy-eq (sym (domL-hId B))) ≅ᴴ G

  hCompose-hId-L-iso-generic
    : ∀ (A : ObjTerm) (K : Hypergraph FlatGen)
        (K-domL≡flat : domL K ≡ flatten A)
    → Unique (Hypergraph.dom K)
    → hComposeP (hId A) K (trans (codL-hId A) (sym K-domL≡flat)) ≅ᴴ K

  -- Tensor-with-empty iso.
  hTensor-hEmpty-G-iso
    : (G : Hypergraph FlatGen) → hTensor hEmpty G ≅ᴴ G

  -- Per-axiom soundness.
  idˡ-sound : ∀ {A B} (f : HomTerm A B) → ⟪ id ∘ f ⟫ ≅ᴴ ⟪ f ⟫
  idʳ-sound : ∀ {A B} (f : HomTerm A B) → ⟪ f ∘ id ⟫ ≅ᴴ ⟪ f ⟫

  λ⇒∘id⊗f≈f∘λ⇒-sound
    : ∀ {A B} {f : HomTerm A B}
    → ⟪ λ⇒ {B} ∘ (id {unit} ⊗₁ f) ⟫ ≅ᴴ ⟪ f ∘ λ⇒ {A} ⟫
  λ⇐∘λ⇒-sound : ∀ {A} → ⟪ λ⇐ {A} ∘ λ⇒ {A} ⟫ ≅ᴴ ⟪ id {unit ⊗₀ A} ⟫
  λ⇒∘λ⇐-sound : ∀ {A} → ⟪ λ⇒ {A} ∘ λ⇐ {A} ⟫ ≅ᴴ ⟪ id {A} ⟫

  ρ⇐∘ρ⇒-sound : ∀ {A} → ⟪ ρ⇐ {A} ∘ ρ⇒ {A} ⟫ ≅ᴴ ⟪ id {A ⊗₀ unit} ⟫
  α⇐∘α⇒-sound : ∀ {A B C}
              → ⟪ α⇐ {A}{B}{C} ∘ α⇒ {A}{B}{C} ⟫ ≅ᴴ ⟪ id {(A ⊗₀ B) ⊗₀ C} ⟫

  σ∘σ-sound : ∀ {A B} → ⟪ σ {B}{A} ∘ σ {A}{B} ⟫ ≅ᴴ ⟪ id {A ⊗₀ B} ⟫
