{-# OPTIONS #-}

--------------------------------------------------------------------------------
-- Atomic-vs-compound cases of `decode-rel-resp-≅ᴴ`.
--
-- A term `f` is *atomic* when it is one of the leaf constructors (Agen,
-- id, λ⇒, λ⇐, ρ⇒, ρ⇐, α⇒, α⇐, σ); it is *compound* when it is `_∘_`
-- or `_⊗₁_`.  This file discharges the two cross-shape lemmas
--
--   decode-rel-resp-≅ᴴ-atomic-compound : Atomic f → Compound g → ⟪f⟫ ≅ᴴ ⟪g⟫
--                                       → decode-rel f ≈Term decode-rel g
--
-- (and its symmetric variant) by combining edge-count arithmetic with
-- the abstract inductive hypothesis on subterms.
--
-- Key observation: each atomic constructor's translation has a known
-- edge count:
--
--   * `⟪ Agen g ⟫ = hGen g` has `nE ≡ 1`.
--   * `⟪ id A ⟫ = ⟪ λ⇒ A ⟫ = ⟪ λ⇐ A ⟫ = hId A`,
--     `⟪ ρ⇒ A ⟫ = ⟪ ρ⇐ A ⟫ = hId (A ⊗₀ unit)`,
--     `⟪ α⇒ A B C ⟫ = ⟪ α⇐ A B C ⟫ = hId ((A ⊗₀ B) ⊗₀ C)`,
--     and `hId X` has `nE ≡ 0`.
--   * `⟪ σ A B ⟫ = hSwap A B` has `nE ≡ 0`.
--
-- Compound nE is the sum of the components' nE.  For an iso between G
-- and K we have `Fin G.nE` ↔ `Fin K.nE` via the iso's `ψ`/`ψ⁻¹`, which
-- gives an immediate contradiction whenever the counts differ in the
-- "0 vs ≥ 1" direction.
--
-- The genuinely-non-trivial cases (atomic-Agen vs single-edge compound,
-- and atomic-structural vs 0-edge compound) are reduced to narrow
-- postulates whose discharge requires the same kind of iso-decomposition
-- machinery as the compound-compound case in `Inductive.agda`.  The
-- abstract IH parameter is propagated so a future refinement of those
-- postulates can consume it directly.
--------------------------------------------------------------------------------

open import Categories.APROP
open import Categories.APROP.Hypergraph.Solver.Signature using (APROPSignatureDec)

module Categories.APROP.Hypergraph.Completeness.DecodeRel.RespIso.AtomicCompound
  (sig-dec : APROPSignatureDec) where

open APROPSignatureDec sig-dec using (sig)
open APROP sig
open import Categories.APROP.Hypergraph.Core using (Hypergraph)
open import Categories.APROP.Hypergraph.FromAPROP sig using (FlatGen; ⟪_⟫)
open import Categories.APROP.Hypergraph.Iso using (_≅ᴴ_; sym-≅ᴴ)
open import Categories.APROP.Hypergraph.SoundnessProved sig using (hId-nE)
open import Categories.APROP.Hypergraph.Completeness.DecodeRel sig
  using (decode-rel)

open import Categories.APROP.Hypergraph.Completeness.DecodeRel.RespIso.Atomic sig-dec
  using ( Atomic
        ; atomic-Agen; atomic-id
        ; atomic-λ⇒; atomic-λ⇐; atomic-ρ⇒; atomic-ρ⇐
        ; atomic-α⇒; atomic-α⇐; atomic-σ
        )
import Categories.APROP.Hypergraph.Completeness.DecodeRel.RespIso.Discharge.NEAgenIso1 sig
  as DischargeNEAgenIso1
import Categories.APROP.Hypergraph.Completeness.DecodeRel.RespIso.Discharge.AtomicCompound0E sig-dec
  as DischargeAC0E

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin using (Fin; zero; suc)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; subst)

--------------------------------------------------------------------------------
-- The `Compound` predicate (mirror of the one in `Inductive.agda`).
-- We re-declare it here to avoid the circular import:
-- `Inductive.agda` already imports this module for its dispatcher.

data Compound : ∀ {A B} → HomTerm A B → Set where
  compound-∘ : ∀ {A B C} (g : HomTerm B C) (f : HomTerm A B)
             → Compound (g ∘ f)
  compound-⊗ : ∀ {A B C D} (f : HomTerm A B) (g : HomTerm C D)
             → Compound (f ⊗₁ g)

--------------------------------------------------------------------------------
-- Edge-count helpers.

private
  nE : Hypergraph FlatGen → ℕ
  nE = Hypergraph.nE

nE-Agen : ∀ {A B} (g : mor A B) → nE ⟪ Agen g ⟫ ≡ 1
nE-Agen _ = refl

nE-id : ∀ {A} → nE ⟪ id {A} ⟫ ≡ 0
nE-id {A} = hId-nE A

nE-λ⇒ : ∀ {A} → nE ⟪ λ⇒ {A} ⟫ ≡ 0
nE-λ⇒ {A} = hId-nE A

nE-λ⇐ : ∀ {A} → nE ⟪ λ⇐ {A} ⟫ ≡ 0
nE-λ⇐ {A} = hId-nE A

nE-ρ⇒ : ∀ {A} → nE ⟪ ρ⇒ {A} ⟫ ≡ 0
nE-ρ⇒ {A} = hId-nE (A ⊗₀ unit)

nE-ρ⇐ : ∀ {A} → nE ⟪ ρ⇐ {A} ⟫ ≡ 0
nE-ρ⇐ {A} = hId-nE (A ⊗₀ unit)

nE-α⇒ : ∀ {A B C} → nE ⟪ α⇒ {A} {B} {C} ⟫ ≡ 0
nE-α⇒ {A} {B} {C} = hId-nE ((A ⊗₀ B) ⊗₀ C)

nE-α⇐ : ∀ {A B C} → nE ⟪ α⇐ {A} {B} {C} ⟫ ≡ 0
nE-α⇐ {A} {B} {C} = hId-nE ((A ⊗₀ B) ⊗₀ C)

nE-σ : ∀ {A B} ⦃ s : Symm ≤ Symm ⦄ → nE ⟪ σ {A = A} {B = B} ⦃ s ⦄ ⟫ ≡ 0
nE-σ = refl

-- Compound: `⟪g ∘ f⟫` and `⟪f ⊗₁ g⟫` both have `nE = nE(LHS) + nE(RHS)`
-- definitionally.  Kept for documentation.

nE-∘ : ∀ {A B C} (g : HomTerm B C) (f : HomTerm A B)
     → nE ⟪ g ∘ f ⟫ ≡ nE ⟪ f ⟫ + nE ⟪ g ⟫
nE-∘ _ _ = refl

nE-⊗ : ∀ {A B C D} (f : HomTerm A B) (g : HomTerm C D)
     → nE ⟪ f ⊗₁ g ⟫ ≡ nE ⟪ f ⟫ + nE ⟪ g ⟫
nE-⊗ _ _ = refl

--------------------------------------------------------------------------------
-- Impossibility helper: `Fin 0` is empty, so an iso whose source has
-- 0 edges and whose target has ≥ 1 forces `⊥` via `ψ⁻¹`.

private
  Fin-zero-empty : Fin 0 → ⊥
  Fin-zero-empty ()

  nE-0-suc-absurd
    : ∀ {G K : Hypergraph FlatGen} {n : ℕ}
    → nE G ≡ 0 → nE K ≡ suc n
    → G ≅ᴴ K → ⊥
  nE-0-suc-absurd {G} {K} {n} G-nE≡0 K-nE≡suc iso =
    Fin-zero-empty
      (subst Fin G-nE≡0
        (_≅ᴴ_.ψ⁻¹ iso (subst Fin (sym K-nE≡suc) zero)))

--------------------------------------------------------------------------------
-- The remainder of this file is parameterised by the abstract IH.
-- Pure Agda doesn't allow `let open import` in top-level module
-- parameters (which is the only way to get `IH` mentioning `HomTerm`,
-- `⟪_⟫`, etc. as a top-level module parameter), so we use an
-- anonymous inner module instead.  Callers (e.g. `Inductive.agda`)
-- pass IH explicitly via this module's open-application.

--------------------------------------------------------------------------------
-- Outstanding postulates.  Public so `Inductive.agda` can reference
-- them directly without instantiating the IH-parameterised inner module.
--
-- * `…-0E` cases: atomic is structural (0 edges) and compound has 0
--   total edges (so both sub-terms are 0-edge structural).  The
--   atomic equality holds by Kelly-style coherence on the structure
--   of both terms.
-- * `…-1E` cases: atomic is Agen (1 edge) and compound has exactly
--   1 edge (so exactly one sub-term contains the unique Agen).
-- * `nE-Agen-iso-1`: the iso's edge bijection forces the compound's
--   nE to 1.

-- `decode-rel-resp-≅ᴴ-atomic-compound-0E`: NARROWED postulate, fully
-- discharged constructively from `Structural-coherence-≈Term` (the
-- symmetric-monoidal coherence equation on the structural fragment)
-- in `Discharge/AtomicCompound0E.agda`.  Imported here as a function
-- (no postulate at this layer).  The `Compound g` argument from the
-- original signature is now redundant under `nE ⟪ g ⟫ ≡ 0` — we
-- drop it for the import call, then thread it back through for the
-- dispatch site's signature.

decode-rel-resp-≅ᴴ-atomic-compound-0E
  : ∀ {A B} {f g : HomTerm A B}
  → Atomic f → Compound g
  → nE ⟪ g ⟫ ≡ 0
  → ⟪ f ⟫ ≅ᴴ ⟪ g ⟫
  → decode-rel f ≈Term decode-rel g
decode-rel-resp-≅ᴴ-atomic-compound-0E af _ g-nE≡0 iso =
  DischargeAC0E.decode-rel-resp-≅ᴴ-atomic-compound-0E af g-nE≡0 iso

postulate
  decode-rel-resp-≅ᴴ-Agen-compound-1E
    : ∀ {A B} {g : mor A B} {h : HomTerm A B}
    → Compound h
    → nE ⟪ h ⟫ ≡ 1
    → ⟪ Agen g ⟫ ≅ᴴ ⟪ h ⟫
    → decode-rel (Agen g) ≈Term decode-rel h

-- `nE-Agen-iso-1`: discharged constructively in
-- `Discharge/NEAgenIso1.agda` (a pure `Fin 1 ↔ Fin n` counting argument).
-- Re-exported here under the original signature for the existing call site.

nE-Agen-iso-1
  : ∀ {A B} {g : mor A B} {h : HomTerm A B}
  → Compound h
  → ⟪ Agen g ⟫ ≅ᴴ ⟪ h ⟫
  → nE ⟪ h ⟫ ≡ 1
nE-Agen-iso-1 {h = h} _ iso = DischargeNEAgenIso1.nE-Agen-iso-1 {h = h} iso

--------------------------------------------------------------------------------
-- Main lemmas.  Pattern-match on the atomic shape; for structural
-- atomic, dispatch on the compound's nE.  These don't depend on any IH
-- — they only thread the three postulates above with the impossibility
-- helper.

decode-rel-resp-≅ᴴ-atomic-compound
  : ∀ {A B} {f g : HomTerm A B}
  → Atomic f → Compound g
  → ⟪ f ⟫ ≅ᴴ ⟪ g ⟫
  → decode-rel f ≈Term decode-rel g

-- Helper: 0-edge atomic vs compound, route by compound nE.
private
  dispatch-structural
    : ∀ {A B} {f g : HomTerm A B}
    → (af : Atomic f) → (cg : Compound g)
    → nE ⟪ f ⟫ ≡ 0
    → ⟪ f ⟫ ≅ᴴ ⟪ g ⟫
    → decode-rel f ≈Term decode-rel g
  dispatch-structural {f = f} {g = g} af cg f-nE≡0 iso
    with nE ⟪ g ⟫ in g-nE-eq
  ... | zero  = decode-rel-resp-≅ᴴ-atomic-compound-0E af cg g-nE-eq iso
  ... | suc n = ⊥-elim (nE-0-suc-absurd f-nE≡0 g-nE-eq iso)

decode-rel-resp-≅ᴴ-atomic-compound (atomic-Agen g) cg iso =
  decode-rel-resp-≅ᴴ-Agen-compound-1E cg (nE-Agen-iso-1 cg iso) iso
decode-rel-resp-≅ᴴ-atomic-compound (atomic-id {A}) cg iso =
  dispatch-structural (atomic-id {A}) cg (nE-id {A}) iso
decode-rel-resp-≅ᴴ-atomic-compound (atomic-λ⇒ {A}) cg iso =
  dispatch-structural (atomic-λ⇒ {A}) cg (nE-λ⇒ {A}) iso
decode-rel-resp-≅ᴴ-atomic-compound (atomic-λ⇐ {A}) cg iso =
  dispatch-structural (atomic-λ⇐ {A}) cg (nE-λ⇐ {A}) iso
decode-rel-resp-≅ᴴ-atomic-compound (atomic-ρ⇒ {A}) cg iso =
  dispatch-structural (atomic-ρ⇒ {A}) cg (nE-ρ⇒ {A}) iso
decode-rel-resp-≅ᴴ-atomic-compound (atomic-ρ⇐ {A}) cg iso =
  dispatch-structural (atomic-ρ⇐ {A}) cg (nE-ρ⇐ {A}) iso
decode-rel-resp-≅ᴴ-atomic-compound (atomic-α⇒ {A} {B} {C}) cg iso =
  dispatch-structural (atomic-α⇒ {A} {B} {C}) cg (nE-α⇒ {A} {B} {C}) iso
decode-rel-resp-≅ᴴ-atomic-compound (atomic-α⇐ {A} {B} {C}) cg iso =
  dispatch-structural (atomic-α⇐ {A} {B} {C}) cg (nE-α⇐ {A} {B} {C}) iso
decode-rel-resp-≅ᴴ-atomic-compound (atomic-σ {A} {B} ⦃ s ⦄) cg iso =
  dispatch-structural (atomic-σ {A} {B} ⦃ s ⦄) cg (nE-σ {A} {B} ⦃ s ⦄) iso

-- Symmetric direction: Compound f, Atomic g.  Reduces to the
-- atomic-compound direction via `sym-≅ᴴ` and `≈-Term-sym`.
decode-rel-resp-≅ᴴ-compound-atomic
  : ∀ {A B} {f g : HomTerm A B}
  → Compound f → Atomic g
  → ⟪ f ⟫ ≅ᴴ ⟪ g ⟫
  → decode-rel f ≈Term decode-rel g
decode-rel-resp-≅ᴴ-compound-atomic cf ag iso =
  ≈-Term-sym
    (decode-rel-resp-≅ᴴ-atomic-compound ag cf (sym-≅ᴴ iso))
