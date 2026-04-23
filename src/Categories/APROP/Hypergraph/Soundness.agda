{-# OPTIONS --without-K --lossy-unification #-}

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
--   * Atomic axioms: every `≈Term` constructor has its own explicit
--     dispatch clause to a named focused lemma in `SoundnessAxioms`.
--     11 of the 19 atomic axioms are proven (possibly modulo internal
--     subst₂-cancel postulates); 8 are still postulated.
--
-- Note on the dispatch machinery (`--lossy-unification`):
--
--   Without `--lossy-unification`, dispatching a focused postulate like
--   `pentagon-sound : ∀ {A B C D} → ⟪ pentagon-LHS ⟫ ≅ᴴ ⟪ pentagon-RHS ⟫`
--   triggers a 25-minute unification at the dispatch site.  Agda's
--   unifier can't solve the implicit `{A B C D}` metas from the goal's
--   `⟪ pentagon-LHS ⟫` because `⟪_⟫` isn't (by default) invertible;
--   it normalises both sides to compare `Hypergraph.cod-ok` proof
--   fields, which are deep nested `trans (sym (trans ...)) ...` chains
--   for `hTensor`/`hComposeP` constructions.
--
--   Two flags together resolve this:
--     * `--lossy-unification` lets Agda heuristically unify by assuming
--       the relevant reductions align — fine here because the postulate
--       and goal have syntactically identical `⟪_⟫` shapes.
--     * `{-# INJECTIVE_FOR_INFERENCE ⟪_⟫ #-}` (in `Translation.agda`)
--       lets Agda conclude `f ≡ g` from `⟪ f ⟫ ≡ ⟪ g ⟫`, which lets
--       the implicit morphism variables be inferred back through `⟪_⟫`.
--
--   With both flags, all 8 focused postulates dispatch in <1s each.
--
-- 8 per-axiom postulates still outstanding (see TODO.org Step 6):
--   * `ρ⇒∘f⊗id≈f∘ρ⇒-sound` — ρ-nat
--   * `α-comm-sound`        — α naturality
--   * `triangle-sound`      — α/λ/ρ coherence
--   * `σ∘[f⊗g]≈[g⊗f]∘σ-sound` — σ-nat
--   * `hexagon-sound`       — symmetric hexagon
--   * `pentagon-sound`      — five-α coherence
--   * `assoc-sound`         — hComposeP associativity
--   * `⊗-∘-dist-sound`      — tensor/compose interchange
--
-- Because this file depends on those postulates, it is not `--safe` and
-- is not transitively imported by `CategoricalCrypto.agda`.
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
        ; hexagon-sound
        ; pentagon-sound; assoc-sound; ⊗-∘-dist-sound)
open import Categories.APROP.Hypergraph.HomTermInvariant sig
  using (⟪_⟫-dom-unique)
open import Data.List.Relation.Unary.Unique.Propositional using (Unique)

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
soundness pentagon     = pentagon-sound
soundness assoc        = assoc-sound
soundness ⊗-∘-dist     = ⊗-∘-dist-sound
