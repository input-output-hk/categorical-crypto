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
-- Strategy
-- ========
--
-- The deep math is producing a coherence iso `γ : Ap ⊗₀ Bq ≅ X` in
-- `FreeMonoidal` along with sub-isos witnessing that `f` and `g`
-- factor through `γ` as
--
--     f ≅ᴴ γ.from ∘ (id ⊗₁ q)  : Ap ⊗₀ Aq  →  X
--     g ≅ᴴ (p ⊗₁ id) ∘ γ.to    : X         →  Bp ⊗₀ Bq.
--
-- The middle object `Ap ⊗₀ Bq` is the canonical middle for the natural
-- decomposition
--
--   p ⊗ q  ≈ (p ⊗ id) ∘ (id ⊗ q).
--
-- (Symmetrically `Bp ⊗₀ Aq` would work for `p ⊗ q ≈ (id ⊗ q) ∘ (p ⊗ id)`;
-- the asymmetry is just a presentation choice — see `Discharge/CrossCO.agda`
-- for the symmetric direction `⊗∘`.)
--
-- This file:
--
--   * Postulates only the *primitive* data described above (the
--     coherence iso `γ` and the two sub-isos at the canonical witnesses).
--     This is strictly less than the previous monolithic postulate, which
--     additionally asked for a free-form `≈Term` bridge.
--
--   * Constructively *proves* the rest: the bridge
--     `decode-rel (g' ∘ f') ≈Term decode-rel (p ⊗₁ q)`
--     follows from `γ.iso.isoˡ`, `⊗-∘-dist`, `idˡ`, `idʳ`, and a
--     general `decode-rel-resp-≈Term` lifting fact (proved below).
--
--   * Re-derives the wider `iso-decompose-∘⊗` interface used by
--     `Inductive.agda`.
--
--   * Reduces the main theorem to the primitive plus `∘-resp-≈` and
--     the abstract IH on the extracted sub-isos.
--
-- The symmetric direction `⊗∘` (with `decode-rel (p ⊗₁ q) ≈Term
-- decode-rel (g ∘ f)`) follows by `sym-≅ᴴ` and `≈-Term-sym`.
--
-- Cf. REFACTORING.md and the wired call from `Inductive.agda`:
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
  using (decode-rel; decode-roundtrip-rel)
open import Categories.APROP.Hypergraph.Completeness.DecodeAttempt sig
  using (bridge)

open import Categories.Morphism FreeMonoidal using (_≅_)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)

--------------------------------------------------------------------------------
-- Helper: lift `_≈Term_` through `decode-rel`.
--
-- `decode-rel` is recursive on the term, but its image lives in
-- `HomTerm (unflatten (flatten A)) (unflatten (flatten B))`.  Since
-- `decode-roundtrip-rel f : decode-rel f ≈Term bridge f` and
-- `bridge f = uf-from ∘ f ∘ uf-to`, we can lift `f ≈Term g` to
-- `decode-rel f ≈Term decode-rel g` by sandwiching with
-- `decode-roundtrip-rel`.

decode-rel-resp-≈Term
  : ∀ {A B} {f g : HomTerm A B}
  → f ≈Term g
  → decode-rel f ≈Term decode-rel g
decode-rel-resp-≈Term {f = f} {g = g} eq =
  ≈-Term-trans (decode-roundtrip-rel f)
    (≈-Term-trans
       (∘-resp-≈ ≈-Term-refl (∘-resp-≈ eq ≈-Term-refl))
       (≈-Term-sym (decode-roundtrip-rel g)))

--------------------------------------------------------------------------------
-- Primitive (narrowed) postulate.
--
-- This is the strict narrowing of the previous monolithic
-- `iso-decompose-∘⊗`.  The previous postulate asked, in addition to
-- the coherence-iso content, for a free-form `≈Term` bridge.  Here
-- we postulate *only* the coherence-iso content; the bridge becomes
-- a theorem.
--
-- The deep math: given `iso : ⟪ g ∘ f ⟫ ≅ᴴ ⟪ p ⊗₁ q ⟫`, produce a
-- coherence iso `γ : Bp ⊗₀ Aq ≅ X` in `FreeMonoidal`, together with
-- sub-isos witnessing that `f` and `g` agree (at the hypergraph
-- level) with their canonical factors through `γ`.
--
-- Equivalent shape: the deeper bookkeeping for `iso-decompose-∘∘`
-- (item 2 in REFACTORING.md) is exactly what produces the coherence
-- iso `γ` here.  See `Discharge/IsoDecomposeCC.agda` for the
-- analogous discharge programme.

postulate
  iso-decompose-∘⊗-primitive
    : ∀ {Ap Aq Bp Bq X}
        (g : HomTerm X (Bp ⊗₀ Bq)) (f : HomTerm (Ap ⊗₀ Aq) X)
        (p : HomTerm Ap Bp)        (q : HomTerm Aq Bq)
    → ⟪ g ∘ f ⟫ ≅ᴴ ⟪ p ⊗₁ q ⟫
    → Σ ((Ap ⊗₀ Bq) ≅ X) λ γ →
          (⟪ f ⟫ ≅ᴴ ⟪ _≅_.from γ ∘ (id ⊗₁ q) ⟫)
        × (⟪ g ⟫ ≅ᴴ ⟪ (p ⊗₁ id) ∘ _≅_.to γ ⟫)

--------------------------------------------------------------------------------
-- Bridge lemma: from the coherence iso `γ`, the canonical factors
-- `f' = γ.from ∘ (id ⊗₁ q)` and `g' = (p ⊗₁ id) ∘ γ.to` compose to
-- `p ⊗₁ q` up to `≈Term`, definitionally lifted to `decode-rel`.

bridge-from-γ
  : ∀ {Ap Aq Bp Bq X}
      (p : HomTerm Ap Bp) (q : HomTerm Aq Bq)
      (γ : (Ap ⊗₀ Bq) ≅ X)
  → decode-rel ( ((p ⊗₁ id) ∘ _≅_.to γ) ∘ (_≅_.from γ ∘ (id ⊗₁ q)) )
      ≈Term decode-rel (p ⊗₁ q)
bridge-from-γ {Ap} {Aq} {Bp} {Bq} {X} p q γ =
  decode-rel-resp-≈Term hom-≈
  where
    -- The categorical bridge in `HomTerm`, lifted to `decode-rel` by
    -- `decode-rel-resp-≈Term`.
    --
    --   ((p ⊗ id) ∘ γ.to) ∘ (γ.from ∘ (id ⊗ q))
    --   ≈Term  (p ⊗ id) ∘ (γ.to ∘ γ.from) ∘ (id ⊗ q)        [assoc]
    --   ≈Term  (p ⊗ id) ∘ id ∘ (id ⊗ q)                     [γ.iso.isoˡ]
    --   ≈Term  (p ⊗ id) ∘ (id ⊗ q)                          [idˡ]
    --   ≈Term  (p ∘ id) ⊗ (id ∘ q)                          [⊗-∘-dist⁻¹]
    --   ≈Term  p ⊗ q                                         [idʳ × idˡ]

    open _≅_ γ using (from; to; iso)
    open import Categories.Morphism FreeMonoidal using (Iso)
    open Iso iso using (isoˡ)
    -- isoˡ : to ∘ from ≈Term id

    step-assoc : ((p ⊗₁ id) ∘ to) ∘ (from ∘ (id ⊗₁ q))
               ≈Term (p ⊗₁ id) ∘ (to ∘ from) ∘ (id ⊗₁ q)
    step-assoc =
      ≈-Term-trans
        assoc                                              -- ((p ⊗ id) ∘ to) ∘ (from ∘ (id ⊗ q))
                                                            --   ≈ (p ⊗ id) ∘ (to ∘ (from ∘ (id ⊗ q)))
        (∘-resp-≈ ≈-Term-refl (≈-Term-sym assoc))
                                                            --   ≈ (p ⊗ id) ∘ ((to ∘ from) ∘ (id ⊗ q))

    step-iso : (p ⊗₁ id) ∘ (to ∘ from) ∘ (id ⊗₁ q)
             ≈Term (p ⊗₁ id) ∘ id ∘ (id ⊗₁ q)
    step-iso = ∘-resp-≈ ≈-Term-refl (∘-resp-≈ isoˡ ≈-Term-refl)

    step-idˡ : (p ⊗₁ id) ∘ id ∘ (id ⊗₁ q)
             ≈Term (p ⊗₁ id) ∘ (id ⊗₁ q)
    step-idˡ = ∘-resp-≈ ≈-Term-refl idˡ

    step-dist⁻¹ : (p ⊗₁ id) ∘ (id ⊗₁ q)
                ≈Term (p ∘ id) ⊗₁ (id ∘ q)
    step-dist⁻¹ = ≈-Term-sym ⊗-∘-dist

    step-ids : (p ∘ id) ⊗₁ (id ∘ q) ≈Term p ⊗₁ q
    step-ids = ⊗-resp-≈ idʳ idˡ

    hom-≈ : ((p ⊗₁ id) ∘ to) ∘ (from ∘ (id ⊗₁ q)) ≈Term p ⊗₁ q
    hom-≈ =
      ≈-Term-trans step-assoc
        (≈-Term-trans step-iso
           (≈-Term-trans step-idˡ
              (≈-Term-trans step-dist⁻¹ step-ids)))

--------------------------------------------------------------------------------
-- Wide interface (derived from the primitive plus the bridge lemma).
--
-- `iso-decompose-∘⊗` is now a *theorem*, not a postulate.  It packages
-- the primitive output into the original Σ-record shape consumed by
-- `Inductive.agda`.

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
iso-decompose-∘⊗ {Ap} {Aq} {Bp} {Bq} {X} g f p q iso =
  let prim   = iso-decompose-∘⊗-primitive g f p q iso
      γ      = proj₁ prim
      iso-f  = proj₁ (proj₂ prim)
      iso-g  = proj₂ (proj₂ prim)
      f'     = _≅_.from γ ∘ (id ⊗₁ q)
      g'     = (p ⊗₁ id) ∘ _≅_.to γ
      brdg   = bridge-from-γ p q γ
  in f' , g' , iso-f , iso-g , brdg

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
    ≈-Term-trans (∘-resp-≈ IH-g IH-f) brdg
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
      brdg    = proj₂ (proj₂ (proj₂ (proj₂ decomp)))

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
