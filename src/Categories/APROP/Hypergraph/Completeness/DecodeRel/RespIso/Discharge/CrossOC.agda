{-# OPTIONS #-}

--------------------------------------------------------------------------------
-- ∘⊗ cross-shape case of `decode-rel-resp-≅ᴴ`.
--
-- Given:
--
--   g : HomTerm X (Bp ⊗₀ Bq)
--   f : HomTerm (Ap ⊗₀ Aq) X
--   p : HomTerm Ap Bp
--   q : HomTerm Aq Bq
--   iso : ⟪ g ∘ f ⟫ ≅ᴴ ⟪ p ⊗₁ q ⟫
--
-- prove `decode-rel (g ∘ f) ≈Term decode-rel (p ⊗₁ q)`.
--
-- This is the cross-shape pair (one side is a composition, the other is
-- a tensor).  Unlike the same-shape compound-compound cases, no
-- impossibility holds in general at the level of edge/vertex counts.
-- Indeed, `p ⊗₁ q` can be re-presented as `(p ⊗₁ id) ∘ (id ⊗₁ q)` or
-- `(id ⊗₁ q) ∘ (p ⊗₁ id)`, so isomorphic structures genuinely exist for
-- many configurations of `X`.
--
-- The strategy mirrors `ComposeCompose.agda` and `TensorTensor.agda`:
-- expose a single narrow decomposition postulate that captures the deep
-- math, then prove the main theorem by combining the decomposition with
-- the abstract IH.
--
-- Decomposition target
-- ====================
--
-- Given `iso`, we want intermediate factors `p' : HomTerm Ap Bp` and
-- `q' : HomTerm Aq Bq` (any honest re-presentation of p, q) and a pair
-- of "interchange" factors `f' : HomTerm (Ap ⊗₀ Aq) X` and
-- `g' : HomTerm X (Bp ⊗₀ Bq)` such that:
--
--   * `⟪ f ⟫ ≅ᴴ ⟪ f' ⟫`     (same X — preserves IH applicability)
--   * `⟪ g ⟫ ≅ᴴ ⟪ g' ⟫`
--   * `decode-rel (g' ∘ f') ≈Term decode-rel (p ⊗₁ q)`
--
-- The bridge term absorbs any X-vs-canonical-middle mismatch using the
-- ⊗-∘-dist axiom and the coherence isos.  Concretely, a canonical
-- witness when the iso forces `X ≅ Bp ⊗₀ Aq` (the natural middle for
-- the `(p ⊗ id) ∘ (id ⊗ q)` decomposition) is:
--
--   f' = γ.from ∘ (id ⊗₁ q)   :  Ap ⊗₀ Aq  →  X         (γ : Bp ⊗ Aq ≅ X)
--   g' = (p ⊗₁ id) ∘ γ.to     :  X         →  Bp ⊗₀ Bq
--
-- and `g' ∘ f' ≈ (p ⊗ id) ∘ (id ⊗ q) ≈ p ⊗ q` via ⊗-∘-dist and idˡ/idʳ.
-- The deep math is producing the coherence iso `γ` from the hypergraph
-- iso `iso` — that is exactly the content packaged by `iso-decompose-∘⊗`.
--
-- Why this is hard
-- ================
--
-- The ∘⊗ direction has the same "X is existential" complication as the
-- ∘∘ case (`ComposeCompose.agda`): the middle object `X` is given
-- structurally by the user's term `g ∘ f`, while the right-hand side
-- `p ⊗₁ q` has no such middle.  The iso must reveal a *coherence* iso
-- in `FreeMonoidal` between X and some canonical splitting of
-- `Bp ⊗₀ Aq` (or `Ap ⊗₀ Bq`).  Extracting this iso from the
-- hypergraph-level `≅ᴴ` is the bulk of the work — analogous to the
-- ~500-1000 LOC of vertex bookkeeping needed for `iso-decompose-∘∘`.
--
-- This file therefore:
--   * Provides the framework module structure (parameterised by IH).
--   * Defines a narrow `iso-decompose-∘⊗` postulate that captures the
--     deep math (extracts sub-isos at f's and g's exact endpoints,
--     plus a coherence bridge that lands on `p ⊗₁ q`).
--   * Reduces the main theorem to that postulate plus `∘-resp-≈` and
--     IH on the extracted sub-isos.
--
-- The symmetric direction `⊗∘` (with `decode-rel (p ⊗₁ q) ≈Term
-- decode-rel (g ∘ f)`) follows by `sym-≅ᴴ` and `≈-Term-sym`.
--
-- Cf. REFACTORING.md and the postulates in `Inductive.agda`:
-- `decode-rel-resp-≅ᴴ-∘⊗` / `decode-rel-resp-≅ᴴ-⊗∘`.
--------------------------------------------------------------------------------

open import Categories.APROP
open import Categories.APROP.Hypergraph.Solver.Signature using (APROPSignatureDec)

module Categories.APROP.Hypergraph.Completeness.DecodeRel.RespIso.Discharge.CrossOC
  (sig-dec : APROPSignatureDec)
  where

open APROPSignatureDec sig-dec using (sig)
open APROP sig
open import Categories.APROP.Hypergraph.FromAPROP sig using (⟪_⟫)
open import Categories.APROP.Hypergraph.Iso using (_≅ᴴ_; sym-≅ᴴ)
open import Categories.APROP.Hypergraph.Completeness.DecodeRel sig
  using (decode-rel)

open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)

--------------------------------------------------------------------------------
-- Iso decomposition (narrow postulate, public so the discharge module
-- and `Inductive.agda` can use it directly without instantiating the
-- IH module).
--
-- The deep math.  Given an iso `⟪ g ∘ f ⟫ ≅ᴴ ⟪ p ⊗₁ q ⟫`, produce:
--   * an "interchange" middle factor `f' : HomTerm (Ap ⊗₀ Aq) X`
--     (same middle X as f),
--   * an "interchange" outer factor `g' : HomTerm X (Bp ⊗₀ Bq)`,
--   * sub-isos witnessing `⟪ f ⟫ ≅ᴴ ⟪ f' ⟫` and `⟪ g ⟫ ≅ᴴ ⟪ g' ⟫`,
--   * a `≈Term`-bridge `decode-rel (g' ∘ f') ≈Term decode-rel (p ⊗₁ q)`.
--
-- The endpoints of f and f' (resp. g and g') match exactly, so the
-- abstract IH applies directly to the sub-isos.

postulate
  iso-decompose-∘⊗
    : ∀ {Ap Aq Bp Bq X}
        (g : HomTerm X (Bp ⊗₀ Bq)) (f : HomTerm (Ap ⊗₀ Aq) X)
        (p : HomTerm Ap Bp)        (q : HomTerm Aq Bq)
    → ⟪ g ∘ f ⟫ ≅ᴴ ⟪ p ⊗₁ q ⟫
    → Σ (HomTerm (Ap ⊗₀ Aq) X) λ f' →
      Σ (HomTerm X (Bp ⊗₀ Bq)) λ g' →
          (⟪ f ⟫ ≅ᴴ ⟪ f' ⟫)
        × (⟪ g ⟫ ≅ᴴ ⟪ g' ⟫)
        × (decode-rel (g' ∘ f') ≈Term decode-rel (p ⊗₁ q))

module _
  (IH : ∀ {A B} (f g : HomTerm A B)
      → ⟪ f ⟫ ≅ᴴ ⟪ g ⟫
      → decode-rel f ≈Term decode-rel g)
  where

  --------------------------------------------------------------------------------
  -- Main lemma (forward direction).
  --
  -- Strategy:
  --   1. Decompose iso into sub-isos and a coherence bridge via
  --      `iso-decompose-∘⊗`.
  --   2. Apply IH to each sub-iso: `decode-rel f ≈Term decode-rel f'` and
  --      `decode-rel g ≈Term decode-rel g'` (well-typed because f', g'
  --      share f/g's endpoints).
  --   3. Combine via `∘-resp-≈`:
  --        decode-rel (g ∘ f)
  --        ≡       decode-rel g ∘ decode-rel f         (definitional)
  --        ≈Term  decode-rel g' ∘ decode-rel f'        (by ∘-resp-≈ ⟨IH-g, IH-f⟩)
  --        ≡       decode-rel (g' ∘ f')                (definitional)
  --        ≈Term  decode-rel (p ⊗₁ q)                   (by bridge)

  decode-rel-resp-≅ᴴ-∘⊗
    : ∀ {Ap Aq Bp Bq X}
        (g : HomTerm X (Bp ⊗₀ Bq)) (f : HomTerm (Ap ⊗₀ Aq) X)
        (p : HomTerm Ap Bp)        (q : HomTerm Aq Bq)
    → ⟪ g ∘ f ⟫ ≅ᴴ ⟪ p ⊗₁ q ⟫
    → decode-rel (g ∘ f) ≈Term decode-rel (p ⊗₁ q)
  decode-rel-resp-≅ᴴ-∘⊗ {Ap} {Aq} {Bp} {Bq} {X} g f p q iso =
    ≈-Term-trans (∘-resp-≈ IH-g IH-f) bridge
    where
      decomp : Σ (HomTerm (Ap ⊗₀ Aq) X) λ f' →
               Σ (HomTerm X (Bp ⊗₀ Bq)) λ g' →
                  (⟪ f ⟫ ≅ᴴ ⟪ f' ⟫)
                × (⟪ g ⟫ ≅ᴴ ⟪ g' ⟫)
                × (decode-rel (g' ∘ f') ≈Term decode-rel (p ⊗₁ q))
      decomp = iso-decompose-∘⊗ g f p q iso

      f'      = proj₁ decomp
      g'      = proj₁ (proj₂ decomp)
      iso-f   = proj₁ (proj₂ (proj₂ decomp))
      iso-g   = proj₁ (proj₂ (proj₂ (proj₂ decomp)))
      bridge  = proj₂ (proj₂ (proj₂ (proj₂ decomp)))

      IH-f : decode-rel f ≈Term decode-rel f'
      IH-f = IH f f' iso-f

      IH-g : decode-rel g ≈Term decode-rel g'
      IH-g = IH g g' iso-g

  --------------------------------------------------------------------------------
  -- Symmetric direction (⊗∘): reduces to the forward direction via
  -- `sym-≅ᴴ` and `≈-Term-sym`.

  decode-rel-resp-≅ᴴ-⊗∘
    : ∀ {Ap Aq Bp Bq X}
        (p : HomTerm Ap Bp)        (q : HomTerm Aq Bq)
        (g : HomTerm X (Bp ⊗₀ Bq)) (f : HomTerm (Ap ⊗₀ Aq) X)
    → ⟪ p ⊗₁ q ⟫ ≅ᴴ ⟪ g ∘ f ⟫
    → decode-rel (p ⊗₁ q) ≈Term decode-rel (g ∘ f)
  decode-rel-resp-≅ᴴ-⊗∘ p q g f iso =
    ≈-Term-sym (decode-rel-resp-≅ᴴ-∘⊗ g f p q (sym-≅ᴴ iso))
