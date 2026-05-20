{-# OPTIONS #-}

--------------------------------------------------------------------------------
-- Path B (Day 1-2): replace the inductive `decode-rel-resp-≅ᴴ-full`
-- (which dispatched on atomic/compound shape and required ~6 narrow
-- postulates: `iso-decompose-{⊗⊗,∘∘,∘⊗,⊗∘}` plus the atomic-compound
-- dispatchers and `decode-rel-resp-≅ᴴ-Agen-compound-1E`) with a single
-- top-level postulate `nf-resp-≅ᴴ` routed through the normal-form
-- decoder bridge.
--
-- The old inductive structure was architecturally blocked: four of the
-- restriction postulates in `IsoDecomposeTT`/`IsoDecomposeCC` are NOT
-- theorems under the current `_≅ᴴ_` (σ-naturality and idˡ/idʳ
-- counter-examples — see memory `completeness_architectural_blockers`).
--
-- The new top-level postulate `nf-resp-≅ᴴ` is the *only* postulate
-- needed for `decode-rel-resp-≅ᴴ-full`.  It states the normal-form
-- decoder respects hypergraph iso — provable via a normal-form
-- canonicalisation of `Hypergraph FlatGen → HomTerm` invariant under
-- `≅ᴴ` (Path B Day 3+ work).
--
-- The orphaned files (no longer on the critical path) include:
--   * RespIso/Atomic.agda
--   * RespIso/AtomicCompound.agda  (and AtomicCompound0E.agda)
--   * RespIso/TensorTensor.agda
--   * RespIso/ComposeCompose.agda
--   * RespIso/Discharge/CrossOC.agda
--   * RespIso/Discharge/CrossCO.agda
--   * BlockDiagonal/* and IsoDecompose{TT,CC}.agda
-- All are left in place for a separate cleanup pass.
--------------------------------------------------------------------------------

open import Categories.APROP
open import Categories.APROP.Hypergraph.Solver.Signature using (APROPSignatureDec)

module Categories.APROP.Hypergraph.Completeness.DecodeRel.Inductive
  (sig-dec : APROPSignatureDec) where

open APROPSignatureDec sig-dec using (sig)
open APROP sig
open import Categories.APROP.Hypergraph.FromAPROP sig using (⟪_⟫)
open import Categories.APROP.Hypergraph.Iso using (_≅ᴴ_)
open import Categories.APROP.Hypergraph.Completeness.DecodeAttempt sig
  using (bridge)
open import Categories.APROP.Hypergraph.Completeness.DecodeRel sig
  using (decode-rel; decode-roundtrip-rel)

--------------------------------------------------------------------------------
-- The single Path B postulate: the normal-form decoder respects
-- hypergraph isomorphism.  Stated at the `bridge` level (equivalently
-- `decode-rel` modulo `decode-roundtrip-rel`) because `bridge` is the
-- canonical embedding of every `HomTerm` into the `unflatten ∘ flatten`
-- normalised types — the natural target for a hypergraph-iso-invariant
-- normal form.
--
-- Discharge route (Path B Day 3+): define a normal-form canonicalizer
-- `nf : ∀ {A B} → Hypergraph FlatGen → HomTerm (unflatten dom)
-- (unflatten cod)` invariant under `≅ᴴ`, then prove `bridge f ≈Term nf
-- ⟪ f ⟫` by induction on `f`.  The σ-free Mac Lane fragment is already
-- constructive (see commit b7e31da).

postulate
  nf-resp-≅ᴴ
    : ∀ {A B} (f g : HomTerm A B)
    → ⟪ f ⟫ ≅ᴴ ⟪ g ⟫
    → bridge f ≈Term bridge g

--------------------------------------------------------------------------------
-- `nf-bridge`: the bridge from `decode-rel` to `bridge`.  This is
-- *exactly* `decode-roundtrip-rel` (in `DecodeRel.agda`), restated
-- here so the composition below reads as the path-B story.

nf-bridge
  : ∀ {A B} (f : HomTerm A B)
  → decode-rel f ≈Term bridge f
nf-bridge = decode-roundtrip-rel

--------------------------------------------------------------------------------
-- The full theorem, now a one-shot composition:
--
--   decode-rel f
--     ≈⟨ nf-bridge f ⟩      bridge f
--     ≈⟨ nf-resp-≅ᴴ iso ⟩   bridge g
--     ≈⟨ sym (nf-bridge g) ⟩ decode-rel g
--
-- No induction on `f`/`g` is needed: termination is trivial.

decode-rel-resp-≅ᴴ-full
  : ∀ {A B} (f g : HomTerm A B)
  → ⟪ f ⟫ ≅ᴴ ⟪ g ⟫
  → decode-rel f ≈Term decode-rel g
decode-rel-resp-≅ᴴ-full f g iso =
  ≈-Term-trans (nf-bridge f)
    (≈-Term-trans (nf-resp-≅ᴴ f g iso)
                  (≈-Term-sym (nf-bridge g)))
