{-# OPTIONS #-}

--------------------------------------------------------------------------------
-- ∘∘ compound-compound case of `decode-rel-resp-≅ᴴ`.
--
-- Given:
--
--   g₁ : HomTerm X B    f₁ : HomTerm A X
--   g₂ : HomTerm Y B    f₂ : HomTerm A Y
--   iso : ⟪ g₁ ∘ f₁ ⟫ ≅ᴴ ⟪ g₂ ∘ f₂ ⟫
--
-- prove `decode-rel (g₁ ∘ f₁) ≈Term decode-rel (g₂ ∘ f₂)`.
--
-- Approach (parallels `TensorTensor.agda`).  By the definitional equation
--
--   decode-rel (g ∘ f) = decode-rel g ∘ decode-rel f
--
-- it suffices to prove
--
--   decode-rel g₁ ∘ decode-rel f₁ ≈Term decode-rel g₂ ∘ decode-rel f₂.
--
-- Why this is harder than `⊗⊗`
-- =============================
--
-- The ∘∘ case has three structural complications absent in `⊗⊗`:
--
--   1. The middle boundary types (`X` vs `Y`) need not agree as
--      `ObjTerm`s.  Whereas in `⊗⊗` both sides share `HomTerm A B` /
--      `HomTerm C D` at the same `A, B, C, D` exogenously, here the
--      intermediate object is *existentially* quantified — and the iso
--      could mediate between two genuinely-different choices `X ≠ Y`
--      (e.g.,  X = A ⊗ unit and Y = A, with a coherence iso in between).
--      This in particular means we cannot naïvely apply the IH (which
--      requires *same* source and target objects) to the middle factors.
--
--   2. The vertex bijection `φ` in the composite need not split
--      cleanly along the `G/K` partition of `hCompose-impl`.  The
--      `remap` machinery (lines 428-460 of `FromAPROP.agda`) identifies
--      each `K.dom`-vertex with the corresponding `G.cod`-vertex, so an
--      iso can re-attribute vertices across the `G/K` boundary.  In
--      `hTensor` (cf. `⊗⊗`) the two halves are disjoint at the vertex
--      level, simplifying decomposition.
--
--   3. Associativity gives the same composite term two parses
--      `(g ∘ h) ∘ f₁ = g ∘ (h ∘ f₁)`; the decomposition `(f₂', g₂')`
--      extracted from `iso` may correspond to *either* parse and must
--      be reconciled with the user's parse `(f₂, g₂)` via `assoc`
--      (or a more elaborate rebracketing).
--
-- Iso decomposition lemma (narrow postulate)
-- ===========================================
--
-- The deep math is the postulate `iso-decompose-∘∘` below.  Because the
-- IH parameter consumes `HomTerm A B` at the *same* A, B, the
-- decomposition lemma must produce sub-isos whose endpoints match `f₁`
-- and `g₁` exactly:
--
--    ⟪ f₁ ⟫ ≅ᴴ ⟪ f₂' ⟫     where f₂' : HomTerm A X     (same middle as f₁)
--    ⟪ g₁ ⟫ ≅ᴴ ⟪ g₂' ⟫     where g₂' : HomTerm X B     (same middle as g₁)
--
-- Together with a bridge `decode-rel (g₂' ∘ f₂') ≈Term decode-rel (g₂ ∘ f₂)`.
-- The bridge term absorbs the X-vs-Y middle-object mismatch: it is the
-- ≈Term-derivation that rewrites `g₂ ∘ f₂` (parsed through middle Y) into
-- `g₂' ∘ f₂'` (parsed through middle X), using whatever coherence iso
-- bridges X and Y at the hypergraph level.
--
-- Discharging this postulate (~1-2 weeks of work) requires:
--
--   * Partitioning the edge bijection `ψ : Fin (G₁.nE + K₁.nE) →
--     Fin (G₂.nE + K₂.nE)` along the `G/K` split on each side.  Edges
--     do not merge in `hCompose` (no edge identification), so `ψ`
--     must preserve the partition; this is provable directly from the
--     iso's `ψ-elab` field plus the `elab-c` `inj₁/inj₂` reduction
--     lemmas (`hCompose-impl.elab-c-inj₁/inj₂` in FromAPROP.agda).
--
--   * Reading off the component edge bijections, then computing the
--     resulting vertex bijections by tracing endpoints through the
--     `injL`/`remap` maps.  The boundary witnesses `bdy-eq₁/bdy-eq₂`
--     identify the relevant vertex sets.
--
--   * Constructing `f₂'` and `g₂'` by syntactically transporting `f₂`
--     and `g₂` through the X-vs-Y bridge — concretely, using
--     `unflatten-flatten-≈` and the coherence isos to bridge the
--     intermediate types.
--
-- None of these sub-tasks require new high-level math: the categorical
-- content is exactly the symmetric-monoidal coherence theorem, which
-- is already implicit in the `≈Term`-data type.
--
-- Honest verdict
-- ==============
--
-- This file currently:
--   * Provides the framework module structure (parameterised by IH to
--     break the import cycle with `Inductive.agda`).
--   * Defines a narrow `iso-decompose-∘∘` postulate that captures the
--     "deep math" needed (extracts sub-isos at the SAME middle type X
--     as `f₁`/`g₁`, plus a coherence bridge).
--   * Reduces the main theorem to that postulate plus `∘-resp-≈` and
--     IH on the extracted sub-isos.
--
-- This is parallel to the structure of `TensorTensor.agda`, where the
-- analogous `iso-decompose-⊗⊗` postulate plays the same role.  The
-- difference: `iso-decompose-⊗⊗` is provable in 100-200 LOC of vertex
-- bookkeeping; `iso-decompose-∘∘` is closer to 500-1000 LOC (mainly
-- because the `remap` mechanics are more intricate than the disjoint
-- `injL`/`injR` of `hTensor`, AND because of the X-vs-Y middle-object
-- bridge).
--
-- Cf. REFACTORING.md Phase 2 step 5: "Iso decomposition lemmas (~1 week)".
--------------------------------------------------------------------------------

open import Categories.APROP
open import Categories.APROP.Hypergraph.Solver.Signature using (APROPSignatureDec)

module Categories.APROP.Hypergraph.Completeness.DecodeRel.RespIso.ComposeCompose
  (sig-dec : APROPSignatureDec)
  where

open APROPSignatureDec sig-dec using (sig)
open APROP sig
open import Categories.APROP.Hypergraph.FromAPROP sig using (⟪_⟫)
open import Categories.APROP.Hypergraph.Iso using (_≅ᴴ_)
open import Categories.APROP.Hypergraph.Completeness.DecodeRel sig
  using (decode-rel)

-- The iso-decomposition lemma is now constructively assembled from
-- THREE narrower sub-postulates in the discharge module.  This file
-- re-exports `iso-decompose-∘∘` for downstream consumers
-- (`Inductive.agda`) without introducing any new postulates here.
open import Categories.APROP.Hypergraph.Completeness.DecodeRel.RespIso.Discharge.IsoDecomposeCC sig-dec
  using (iso-decompose-∘∘) public

open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)

--------------------------------------------------------------------------------
-- Module-level abstract IH parameter.  `Inductive.agda` will pass
-- `decode-rel-resp-≅ᴴ-full` here when consuming this module.

--------------------------------------------------------------------------------
-- Iso decomposition: see `Discharge/IsoDecomposeCC.agda` for the
-- narrower sub-postulate structure (`middle-type-eq`, `sub-iso-f`,
-- `sub-iso-g`) and the constructive assembly that produces the
-- existential pair (f₂', g₂') along with the sub-isos and the
-- (`≈-Term-refl`) bridge.
--
-- The previous incarnation of this file held a single monolithic
-- postulate `iso-decompose-∘∘`.  Removing it in favour of the
-- discharge module keeps the public API identical while strictly
-- narrowing the postulate surface area.

module _
  (IH : ∀ {A B} (f g : HomTerm A B)
      → ⟪ f ⟫ ≅ᴴ ⟪ g ⟫
      → decode-rel f ≈Term decode-rel g)
  where

  --------------------------------------------------------------------------------
  -- Main lemma.
  --
  -- By definition `decode-rel (g ∘ f) = decode-rel g ∘ decode-rel f`,
  -- so the goal is `decode-rel g₁ ∘ decode-rel f₁ ≈Term
  --                  decode-rel g₂ ∘ decode-rel f₂`.
  --
  -- Strategy:
  --   1. Decompose iso into sub-isos and a coherence bridge via
  --      `iso-decompose-∘∘`.
  --   2. Apply IH to each sub-iso: get `decode-rel f₁ ≈Term decode-rel f₂'`
  --      and `decode-rel g₁ ≈Term decode-rel g₂'` (both well-typed
  --      because f₂', g₂' share f₁/g₁'s endpoints).
  --   3. Combine via `∘-resp-≈`:
  --        decode-rel g₁ ∘ decode-rel f₁
  --        ≈Term  decode-rel g₂' ∘ decode-rel f₂'    (by ∘-resp-≈ ⟨IH-g, IH-f⟩)
  --        ≡       decode-rel (g₂' ∘ f₂')             (definitional)
  --        ≈Term  decode-rel (g₂ ∘ f₂)                (by bridge)

  decode-rel-resp-≅ᴴ-∘∘
    : ∀ {A B X Y} (g₁ : HomTerm X B) (f₁ : HomTerm A X)
                    (g₂ : HomTerm Y B) (f₂ : HomTerm A Y)
    → ⟪ g₁ ∘ f₁ ⟫ ≅ᴴ ⟪ g₂ ∘ f₂ ⟫
    → decode-rel (g₁ ∘ f₁) ≈Term decode-rel (g₂ ∘ f₂)
  decode-rel-resp-≅ᴴ-∘∘ {A} {B} {X} {Y} g₁ f₁ g₂ f₂ iso =
    -- decode-rel (g₁ ∘ f₁) reduces to decode-rel g₁ ∘ decode-rel f₁
    -- definitionally; likewise on the (g₂' ∘ f₂') side.
    ≈-Term-trans (∘-resp-≈ IH-g IH-f) bridge
    where
      decomp : Σ (HomTerm A X) λ f₂' →
               Σ (HomTerm X B) λ g₂' →
                  (⟪ f₁ ⟫ ≅ᴴ ⟪ f₂' ⟫)
                × (⟪ g₁ ⟫ ≅ᴴ ⟪ g₂' ⟫)
                × (decode-rel (g₂' ∘ f₂') ≈Term decode-rel (g₂ ∘ f₂))
      decomp = iso-decompose-∘∘ g₁ f₁ g₂ f₂ iso

      f₂'     = proj₁ decomp
      g₂'     = proj₁ (proj₂ decomp)
      iso-f   = proj₁ (proj₂ (proj₂ decomp))
      iso-g   = proj₁ (proj₂ (proj₂ (proj₂ decomp)))
      bridge  = proj₂ (proj₂ (proj₂ (proj₂ decomp)))

      IH-f : decode-rel f₁ ≈Term decode-rel f₂'
      IH-f = IH f₁ f₂' iso-f

      IH-g : decode-rel g₁ ≈Term decode-rel g₂'
      IH-g = IH g₁ g₂' iso-g
