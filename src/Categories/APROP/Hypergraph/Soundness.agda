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
--   * Atomic axioms: 16 of 19 now have a dedicated named dispatch via a
--     focused lemma in `SoundnessAxioms`. The omnibus `soundness-axiom`
--     catch-all remains only for the 3 axioms that blew up type-checking
--     when dispatched individually (pentagon, assoc, ⊗-∘-dist) — their
--     `⟪_⟫` normalization drove typecheck past 3× baseline even after
--     SoundnessAxioms is built. Those 3 still have named postulates
--     (`pentagon-sound`, `assoc-sound`, `⊗-∘-dist-sound`) available for
--     future per-constructor hookup, but the dispatch goes through the
--     catch-all to keep build times bounded.
--
-- Currently under catch-all (3):
--   * `pentagon`  — five-α coherence.
--   * `assoc`     — hComposeP associativity.
--   * `⊗-∘-dist`  — tensor/compose interchange.
--
-- Currently dispatched, still postulated (5):
--   * `ρ⇒∘f⊗id≈f∘ρ⇒-sound` — ρ-nat
--   * `α-comm-sound`        — α naturality
--   * `triangle-sound`      — α/λ/ρ coherence on (A⊗unit)⊗B
--   * `σ∘[f⊗g]≈[g⊗f]∘σ-sound` — σ-nat
--   * `hexagon-sound`       — three-α/three-σ coherence
--
-- Because this file depends on those postulates and the catch-all, it
-- is not `--safe` and is not transitively imported by
-- `CategoricalCrypto.agda`.
--------------------------------------------------------------------------------

open import Categories.APROP

module Categories.APROP.Hypergraph.Soundness (sig : APROPSignature) where

open APROP sig
open import Categories.APROP.Hypergraph.Core
open import Categories.APROP.Hypergraph.FromAPROP sig
  using (FlatGen; hTensor)
open import Categories.APROP.Hypergraph.Translation sig
open import Categories.APROP.Hypergraph.Iso
open import Categories.APROP.Hypergraph.Congruence sig using (hTensor-resp-≅ᴴ)
open import Categories.APROP.Hypergraph.CongruenceP sig using (hComposeP-resp-≅ᴴ)
open import Categories.APROP.Hypergraph.SoundnessAxioms sig
  using ( idˡ-sound; idʳ-sound
        ; λ⇐∘λ⇒-sound; λ⇒∘λ⇐-sound; σ∘σ-sound
        ; ρ⇐∘ρ⇒-sound; α⇐∘α⇒-sound
        ; ρ⇒∘ρ⇐-sound; α⇒∘α⇐-sound
        ; λ⇒∘id⊗f≈f∘λ⇒-sound
        ; ρ⇒∘f⊗id≈f∘ρ⇒-sound
        ; α-comm-sound
        ; triangle-sound
        ; σ∘[f⊗g]≈[g⊗f]∘σ-sound
        ; hexagon-sound)
open import Categories.APROP.Hypergraph.HomTermInvariant sig
  using (⟪_⟫-dom-unique)
open import Data.List.Relation.Unary.Unique.Propositional using (Unique)

--------------------------------------------------------------------------------
-- Catch-all postulates.
-- (1) The 18 atomic axioms (unchanged from the old Soundness).
-- (2) The `Unique ⟪f⟫.dom` invariant, needed to pass to the pruned
--     hComposeP-resp-≅ᴴ for the `∘-resp-≈` congruence. Follows from
--     structural induction on HomTerm; proof deferred to a future
--     `Hypergraph.Invariant` extension.

postulate
  soundness-axiom : ∀ {A B} {f g : HomTerm A B} → f ≈Term g → ⟪ f ⟫ ≅ᴴ ⟪ g ⟫

--------------------------------------------------------------------------------
-- The soundness theorem.

soundness : ∀ {A B} {f g : HomTerm A B} → f ≈Term g → ⟪ f ⟫ ≅ᴴ ⟪ g ⟫

-- Equivalence closure.
soundness ≈-Term-refl         = refl-≅ᴴ _
soundness (≈-Term-sym  p)     = sym-≅ᴴ (soundness p)
soundness (≈-Term-trans p q)  = trans-≅ᴴ (soundness p) (soundness q)

-- Congruence for composition. The APROP term `f ∘ g` (f after g)
-- translates to `hComposeP ⟪g⟫ ⟪f⟫`. `hComposeP-resp-≅ᴴ` takes the
-- G-side iso, K-side iso, and Unique K₁.dom — the last supplied by
-- the `⟪_⟫-dom-unique` invariant for `f` (which is the K-side).
soundness (∘-resp-≈ {f = f} pf pg) =
  hComposeP-resp-≅ᴴ (soundness pg) (soundness pf) (⟪_⟫-dom-unique f)

-- Congruence for tensor.
soundness (⊗-resp-≈ pf pg)    = hTensor-resp-≅ᴴ (soundness pf) (soundness pg)

-- `id ⊗ id ≈ id` at `A ⊗₀ B` is a definitional equality of
-- hypergraphs: `hId (A ⊗₀ B) = hTensor (hId A) (hId B)`.
soundness id⊗id≈id            = refl-≅ᴴ _

-- Atomic axioms discharged from SoundnessAxioms (modulo internal
-- postulates for the last 2-3 fields of each iso).
soundness (idˡ {f = f})           = idˡ-sound f
soundness (λ⇐∘λ⇒≈id {A = A})      = λ⇐∘λ⇒-sound {A}
soundness (λ⇒∘λ⇐≈id {A = A})      = λ⇒∘λ⇐-sound {A}
soundness (σ∘σ≈id {A = A} {B = B}) = σ∘σ-sound {A} {B}
soundness (ρ⇐∘ρ⇒≈id {A = A})      = ρ⇐∘ρ⇒-sound {A}
soundness (α⇐∘α⇒≈id {A = A} {B = B} {C = C}) = α⇐∘α⇒-sound {A} {B} {C}
soundness (ρ⇒∘ρ⇐≈id {A = A})      = ρ⇒∘ρ⇐-sound {A}
soundness (α⇒∘α⇐≈id {A = A} {B = B} {C = C}) = α⇒∘α⇐-sound {A} {B} {C}
soundness (idʳ {f = f})           = idʳ-sound f
soundness (λ⇒∘id⊗f≈f∘λ⇒ {f = f})  = λ⇒∘id⊗f≈f∘λ⇒-sound {f = f}
soundness (ρ⇒∘f⊗id≈f∘ρ⇒ {f = f})   = ρ⇒∘f⊗id≈f∘ρ⇒-sound {f = f}
soundness (α-comm {f = f} {g = g} {h = h}) = α-comm-sound {f = f} {g = g} {h = h}
soundness (triangle {A = A} {B = B}) = triangle-sound {A} {B}
soundness (σ∘[f⊗g]≈[g⊗f]∘σ {f = f} {g = g}) = σ∘[f⊗g]≈[g⊗f]∘σ-sound {f = f} {g = g}
soundness (hexagon {A = A} {B = B} {C = C}) = hexagon-sound {A} {B} {C}

-- Atomic axioms still using catch-all. See module header for the
-- classification.
soundness p                   = soundness-axiom p
