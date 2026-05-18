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

-- The reverse direction: id ↦ Agen is impossible by the same argument.
decode-rel-resp-≅ᴴ-id-Agen-absurd
  : ∀ {A} (g : mor A A) → ⟪ id {A} ⟫ ≅ᴴ ⟪ Agen g ⟫ → ⊥
decode-rel-resp-≅ᴴ-id-Agen-absurd {A} g iso =
  Agen-nonAgen-absurd refl (hId-nE A) iso'
  where
    open import Categories.APROP.Hypergraph.Iso using (sym-≅ᴴ)
    iso' : ⟪ Agen g ⟫ ≅ᴴ ⟪ id {A} ⟫
    iso' = sym-≅ᴴ iso

-- All other cross-pairs Agen-vs-non-Agen-atomic share the nE-mismatch
-- structure: Agen has 1 edge, every other atomic constructor's
-- translation has 0 edges.  Each lemma below is `Agen-nonAgen-absurd`
-- applied to the appropriate `hId-nE` or `refl`.

-- Agen vs σ: ⟪σ⟫ = hSwap, hSwap.nE = 0 definitionally.
decode-rel-resp-≅ᴴ-Agen-σ-absurd
  : ∀ {A B} ⦃ s : Symm ≤ Symm ⦄
    (g : mor (A ⊗₀ B) (B ⊗₀ A))
  → ⟪ Agen g ⟫ ≅ᴴ ⟪ σ {A = A} {B = B} ⦃ s ⦄ ⟫ → ⊥
decode-rel-resp-≅ᴴ-Agen-σ-absurd g iso = Agen-nonAgen-absurd refl refl iso

-- Agen vs λ⇒: ⟪λ⇒ A⟫ = hId A.
decode-rel-resp-≅ᴴ-Agen-λ⇒-absurd
  : ∀ {A} (g : mor (unit ⊗₀ A) A)
  → ⟪ Agen g ⟫ ≅ᴴ ⟪ λ⇒ {A} ⟫ → ⊥
decode-rel-resp-≅ᴴ-Agen-λ⇒-absurd {A} g iso =
  Agen-nonAgen-absurd refl (hId-nE A) iso

-- Agen vs λ⇐: ⟪λ⇐ A⟫ = hId A.
decode-rel-resp-≅ᴴ-Agen-λ⇐-absurd
  : ∀ {A} (g : mor A (unit ⊗₀ A))
  → ⟪ Agen g ⟫ ≅ᴴ ⟪ λ⇐ {A} ⟫ → ⊥
decode-rel-resp-≅ᴴ-Agen-λ⇐-absurd {A} g iso =
  Agen-nonAgen-absurd refl (hId-nE A) iso

-- Agen vs ρ⇒: ⟪ρ⇒ A⟫ = hId (A ⊗ unit).
decode-rel-resp-≅ᴴ-Agen-ρ⇒-absurd
  : ∀ {A} (g : mor (A ⊗₀ unit) A)
  → ⟪ Agen g ⟫ ≅ᴴ ⟪ ρ⇒ {A} ⟫ → ⊥
decode-rel-resp-≅ᴴ-Agen-ρ⇒-absurd {A} g iso =
  Agen-nonAgen-absurd refl (hId-nE (A ⊗₀ unit)) iso

-- Agen vs ρ⇐: ⟪ρ⇐ A⟫ = hId (A ⊗ unit).
decode-rel-resp-≅ᴴ-Agen-ρ⇐-absurd
  : ∀ {A} (g : mor A (A ⊗₀ unit))
  → ⟪ Agen g ⟫ ≅ᴴ ⟪ ρ⇐ {A} ⟫ → ⊥
decode-rel-resp-≅ᴴ-Agen-ρ⇐-absurd {A} g iso =
  Agen-nonAgen-absurd refl (hId-nE (A ⊗₀ unit)) iso

-- Agen vs α⇒: ⟪α⇒ A B C⟫ = hId ((A ⊗ B) ⊗ C).
decode-rel-resp-≅ᴴ-Agen-α⇒-absurd
  : ∀ {A B C} (g : mor ((A ⊗₀ B) ⊗₀ C) (A ⊗₀ (B ⊗₀ C)))
  → ⟪ Agen g ⟫ ≅ᴴ ⟪ α⇒ {A} {B} {C} ⟫ → ⊥
decode-rel-resp-≅ᴴ-Agen-α⇒-absurd {A} {B} {C} g iso =
  Agen-nonAgen-absurd refl (hId-nE ((A ⊗₀ B) ⊗₀ C)) iso

-- Agen vs α⇐: ⟪α⇐ A B C⟫ = hId ((A ⊗ B) ⊗ C).
decode-rel-resp-≅ᴴ-Agen-α⇐-absurd
  : ∀ {A B C} (g : mor (A ⊗₀ (B ⊗₀ C)) ((A ⊗₀ B) ⊗₀ C))
  → ⟪ Agen g ⟫ ≅ᴴ ⟪ α⇐ {A} {B} {C} ⟫ → ⊥
decode-rel-resp-≅ᴴ-Agen-α⇐-absurd {A} {B} {C} g iso =
  Agen-nonAgen-absurd refl (hId-nE ((A ⊗₀ B) ⊗₀ C)) iso

--------------------------------------------------------------------------------
-- Reverse direction: X-vs-Agen for X ∈ {σ, λ⇒, λ⇐, ρ⇒, ρ⇐, α⇒, α⇐}.
-- Each is the corresponding Agen-X lemma precomposed with sym-≅ᴴ.

open import Categories.APROP.Hypergraph.Iso using (sym-≅ᴴ)

-- σ vs Agen.
decode-rel-resp-≅ᴴ-σ-Agen-absurd
  : ∀ {A B} ⦃ s : Symm ≤ Symm ⦄
    (g : mor (A ⊗₀ B) (B ⊗₀ A))
  → ⟪ σ {A = A} {B = B} ⦃ s ⦄ ⟫ ≅ᴴ ⟪ Agen g ⟫ → ⊥
decode-rel-resp-≅ᴴ-σ-Agen-absurd ⦃ s ⦄ g iso =
  decode-rel-resp-≅ᴴ-Agen-σ-absurd ⦃ s ⦄ g (sym-≅ᴴ iso)

-- λ⇒ vs Agen.
decode-rel-resp-≅ᴴ-λ⇒-Agen-absurd
  : ∀ {A} (g : mor (unit ⊗₀ A) A)
  → ⟪ λ⇒ {A} ⟫ ≅ᴴ ⟪ Agen g ⟫ → ⊥
decode-rel-resp-≅ᴴ-λ⇒-Agen-absurd g iso =
  decode-rel-resp-≅ᴴ-Agen-λ⇒-absurd g (sym-≅ᴴ iso)

-- λ⇐ vs Agen.
decode-rel-resp-≅ᴴ-λ⇐-Agen-absurd
  : ∀ {A} (g : mor A (unit ⊗₀ A))
  → ⟪ λ⇐ {A} ⟫ ≅ᴴ ⟪ Agen g ⟫ → ⊥
decode-rel-resp-≅ᴴ-λ⇐-Agen-absurd g iso =
  decode-rel-resp-≅ᴴ-Agen-λ⇐-absurd g (sym-≅ᴴ iso)

-- ρ⇒ vs Agen.
decode-rel-resp-≅ᴴ-ρ⇒-Agen-absurd
  : ∀ {A} (g : mor (A ⊗₀ unit) A)
  → ⟪ ρ⇒ {A} ⟫ ≅ᴴ ⟪ Agen g ⟫ → ⊥
decode-rel-resp-≅ᴴ-ρ⇒-Agen-absurd g iso =
  decode-rel-resp-≅ᴴ-Agen-ρ⇒-absurd g (sym-≅ᴴ iso)

-- ρ⇐ vs Agen.
decode-rel-resp-≅ᴴ-ρ⇐-Agen-absurd
  : ∀ {A} (g : mor A (A ⊗₀ unit))
  → ⟪ ρ⇐ {A} ⟫ ≅ᴴ ⟪ Agen g ⟫ → ⊥
decode-rel-resp-≅ᴴ-ρ⇐-Agen-absurd g iso =
  decode-rel-resp-≅ᴴ-Agen-ρ⇐-absurd g (sym-≅ᴴ iso)

-- α⇒ vs Agen.
decode-rel-resp-≅ᴴ-α⇒-Agen-absurd
  : ∀ {A B C} (g : mor ((A ⊗₀ B) ⊗₀ C) (A ⊗₀ (B ⊗₀ C)))
  → ⟪ α⇒ {A} {B} {C} ⟫ ≅ᴴ ⟪ Agen g ⟫ → ⊥
decode-rel-resp-≅ᴴ-α⇒-Agen-absurd g iso =
  decode-rel-resp-≅ᴴ-Agen-α⇒-absurd g (sym-≅ᴴ iso)

-- α⇐ vs Agen.
decode-rel-resp-≅ᴴ-α⇐-Agen-absurd
  : ∀ {A B C} (g : mor (A ⊗₀ (B ⊗₀ C)) ((A ⊗₀ B) ⊗₀ C))
  → ⟪ α⇐ {A} {B} {C} ⟫ ≅ᴴ ⟪ Agen g ⟫ → ⊥
decode-rel-resp-≅ᴴ-α⇐-Agen-absurd g iso =
  decode-rel-resp-≅ᴴ-Agen-α⇐-absurd g (sym-≅ᴴ iso)
