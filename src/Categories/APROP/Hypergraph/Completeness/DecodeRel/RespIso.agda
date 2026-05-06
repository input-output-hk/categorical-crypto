{-# OPTIONS #-}

--------------------------------------------------------------------------------
-- Atomic-case proofs of `decode-rel-resp-≅ᴴ` from DecodeRel.agda.
--
-- For atomic constructors (Agen, σ, id, λ⇒, λ⇐, ρ⇒, ρ⇐, α⇒, α⇐), the
-- definition `decode-rel f = bridge f` reduces the iso-respect property
-- to:
--   ⟪ f ⟫ ≅ᴴ ⟪ g ⟫ → bridge f ≈Term bridge g.
--
-- For SAME-constructor pairs at the same source/target objects, the
-- ObjTerm parameters are forced (modulo Agen, where the underlying
-- mor must be derived from the iso's edge-label equality).  Most
-- pairs reduce to `≈-Term-refl`.
--
-- For CROSS-constructor pairs the proof requires extracting structural
-- consequences of the iso (e.g., when f = id and g = some
-- structurally-trivial atomic with iso translation).  This file
-- collects what we can prove without the full general theorem.
--------------------------------------------------------------------------------

open import Categories.APROP

module Categories.APROP.Hypergraph.Completeness.DecodeRel.RespIso
  (sig : APROPSignature) where

open APROP sig
open import Categories.APROP.Hypergraph.Core using (Hypergraph)
open import Categories.APROP.Hypergraph.FromAPROP sig using (FlatGen; ⟪_⟫)
open import Categories.APROP.Hypergraph.Iso using (_≅ᴴ_)
open import Categories.APROP.Hypergraph.Completeness.DecodeAttempt sig
  using (bridge)
open import Categories.APROP.Hypergraph.Completeness.DecodeRel sig
  using (decode-rel)
open import Categories.APROP.Hypergraph.SoundnessProved sig using (hId-nE)

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin using (Fin; zero; suc)
open import Data.Nat using (ℕ; zero; suc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

--------------------------------------------------------------------------------
-- Same-constructor pairs.  When f and g are the SAME atomic constructor
-- with the same source/target object, their ObjTerm parameters are
-- forced equal by Agda's type inference, so `decode-rel f ≡ decode-rel g`
-- is `refl`.
--
-- The only exception is Agen, where two different generators
-- `g₁ g₂ : mor A B` can both yield `HomTerm A B` — see below.

decode-rel-resp-≅ᴴ-id-id
  : ∀ {A} → ⟪ id {A} ⟫ ≅ᴴ ⟪ id {A} ⟫
  → decode-rel (id {A}) ≈Term decode-rel (id {A})
decode-rel-resp-≅ᴴ-id-id _ = ≈-Term-refl

decode-rel-resp-≅ᴴ-λ⇒-λ⇒
  : ∀ {A} → ⟪ λ⇒ {A} ⟫ ≅ᴴ ⟪ λ⇒ {A} ⟫
  → decode-rel (λ⇒ {A}) ≈Term decode-rel (λ⇒ {A})
decode-rel-resp-≅ᴴ-λ⇒-λ⇒ _ = ≈-Term-refl

decode-rel-resp-≅ᴴ-λ⇐-λ⇐
  : ∀ {A} → ⟪ λ⇐ {A} ⟫ ≅ᴴ ⟪ λ⇐ {A} ⟫
  → decode-rel (λ⇐ {A}) ≈Term decode-rel (λ⇐ {A})
decode-rel-resp-≅ᴴ-λ⇐-λ⇐ _ = ≈-Term-refl

decode-rel-resp-≅ᴴ-ρ⇒-ρ⇒
  : ∀ {A} → ⟪ ρ⇒ {A} ⟫ ≅ᴴ ⟪ ρ⇒ {A} ⟫
  → decode-rel (ρ⇒ {A}) ≈Term decode-rel (ρ⇒ {A})
decode-rel-resp-≅ᴴ-ρ⇒-ρ⇒ _ = ≈-Term-refl

decode-rel-resp-≅ᴴ-ρ⇐-ρ⇐
  : ∀ {A} → ⟪ ρ⇐ {A} ⟫ ≅ᴴ ⟪ ρ⇐ {A} ⟫
  → decode-rel (ρ⇐ {A}) ≈Term decode-rel (ρ⇐ {A})
decode-rel-resp-≅ᴴ-ρ⇐-ρ⇐ _ = ≈-Term-refl

decode-rel-resp-≅ᴴ-α⇒-α⇒
  : ∀ {A B C} → ⟪ α⇒ {A} {B} {C} ⟫ ≅ᴴ ⟪ α⇒ {A} {B} {C} ⟫
  → decode-rel (α⇒ {A} {B} {C}) ≈Term decode-rel (α⇒ {A} {B} {C})
decode-rel-resp-≅ᴴ-α⇒-α⇒ _ = ≈-Term-refl

decode-rel-resp-≅ᴴ-α⇐-α⇐
  : ∀ {A B C} → ⟪ α⇐ {A} {B} {C} ⟫ ≅ᴴ ⟪ α⇐ {A} {B} {C} ⟫
  → decode-rel (α⇐ {A} {B} {C}) ≈Term decode-rel (α⇐ {A} {B} {C})
decode-rel-resp-≅ᴴ-α⇐-α⇐ _ = ≈-Term-refl

decode-rel-resp-≅ᴴ-σ-σ
  : ∀ {A B} ⦃ s : Symm ≤ Symm ⦄
  → ⟪ σ {A = A} {B = B} ⦃ s ⦄ ⟫ ≅ᴴ ⟪ σ {A = A} {B = B} ⦃ s ⦄ ⟫
  → decode-rel (σ {A = A} {B = B} ⦃ s ⦄)
  ≈Term decode-rel (σ {A = A} {B = B} ⦃ s ⦄)
decode-rel-resp-≅ᴴ-σ-σ _ = ≈-Term-refl

--------------------------------------------------------------------------------
-- Cross-constructor impossibility: Agen vs any non-Agen atomic.
--
-- Since `⟪ Agen g ⟫ = hGen g` has nE = 1 while every other atomic
-- constructor's translation has nE = 0 (id/λ/ρ/α route through `hId`,
-- and σ routes through `hSwap`), the iso's edge bijection ψ⁻¹ : Fin 0
-- → Fin 1 must produce a `Fin 1` element from no input — impossible.
--
-- Conversely Agen on the right is also impossible by symmetry.

-- Helper: from an iso with G.nE = 1 and K.nE = 0, extract ⊥ via ψ.
private
  open import Relation.Binary.PropositionalEquality using (subst)

  Fin-zero-empty : Fin 0 → ⊥
  Fin-zero-empty ()

  Agen-nonAgen-absurd
    : ∀ {G K : Hypergraph FlatGen}
    → Hypergraph.nE G ≡ 1 → Hypergraph.nE K ≡ 0
    → G ≅ᴴ K → ⊥
  Agen-nonAgen-absurd {G} {K} G-nE≡1 K-nE≡0 iso =
    Fin-zero-empty (subst Fin K-nE≡0 (ψ G-applied))
    where
      open _≅ᴴ_ iso
      G-applied : Fin (Hypergraph.nE G)
      G-applied = subst Fin (≡-sym G-nE≡1) zero
        where open import Relation.Binary.PropositionalEquality renaming (sym to ≡-sym)

decode-rel-resp-≅ᴴ-Agen-id-absurd
  : ∀ {A} (g : mor A A) → ⟪ Agen g ⟫ ≅ᴴ ⟪ id {A} ⟫ → ⊥
decode-rel-resp-≅ᴴ-Agen-id-absurd {A} g iso =
  Agen-nonAgen-absurd refl (hId-nE A) iso
