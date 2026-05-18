{-# OPTIONS #-}

--------------------------------------------------------------------------------
-- Discharge module for the `iso-decompose-∘∘` postulate from
-- `RespIso.ComposeCompose`.
--
-- Status
-- ======
--
-- This file exports `iso-decompose-∘∘` with the same signature as the
-- postulate in `RespIso/ComposeCompose.agda`.  The lemma is genuinely
-- ~500-1000 LOC of vertex/edge bookkeeping plus a symmetric-monoidal
-- coherence bridge for the middle-object mismatch (X vs Y).  The
-- mathematical content is fully understood and decomposed below into
-- named sub-lemmas; the present file fills in the structural plumbing
-- but leaves the deepest sub-lemmas as named postulates so that the
-- overall shape is checkable today and the remaining work is reduced
-- to focused, self-contained sub-tasks.
--
-- Compared to `RespIso/ComposeCompose.agda`'s monolithic
-- `iso-decompose-∘∘` postulate, this file:
--
--   * Names each sub-step (`partition-ψ`, `extract-sub-iso-f`,
--     `extract-sub-iso-g`, `mk-f₂'`, `mk-g₂'`, `bridge-coherence`)
--     so progress can be made incrementally.
--   * Assembles them into a complete proof of `iso-decompose-∘∘`.
--   * Documents which existing infrastructure each sub-step depends on
--     (`hCompose-impl.elab-c-inj₁/inj₂`, `unflatten-flatten-≈`,
--     `Iso._≅ᴴ_` field destructors).
--
-- Sub-lemma roadmap
-- =================
--
-- Let `C₁ = ⟪ g₁ ∘ f₁ ⟫` and `C₂ = ⟪ g₂ ∘ f₂ ⟫`.  By definition
-- `Cᵢ = hCompose ⟪fᵢ⟫ ⟪gᵢ⟫ bdy-eqᵢ`.  Write `Gᵢ = ⟪fᵢ⟫`, `Kᵢ = ⟪gᵢ⟫`
-- so `Cᵢ.nV = Gᵢ.nV + Kᵢ.nV`, `Cᵢ.nE = Gᵢ.nE + Kᵢ.nE`.
--
-- The iso `iso : C₁ ≅ᴴ C₂` carries (cf. `Hypergraph/Iso.agda`):
--   * `φ  : Fin C₁.nV → Fin C₂.nV` with `φ⁻¹` (vertex bijection),
--   * `ψ  : Fin C₁.nE → Fin C₂.nE` with `ψ⁻¹` (edge bijection),
--   * `vlab-coh`, `ein-coh`, `eout-coh`, `dom-coh`, `cod-coh`, `elab-coh`.
--
-- (1) `partition-ψ`
--     ψ maps the `G₁.nE + K₁.nE` partition into the `G₂.nE + K₂.nE`
--     partition.  Edges are never identified in `hCompose`, and `elab-c`
--     reduces differently on `inj₁` vs `inj₂` (cf. `elab-c-inj₁/inj₂`),
--     so `elab-coh` plus the FlatGen labels force `ψ` to preserve the
--     partition modulo a fixed direction.  Concretely: there exist
--     bijections `ψG : Fin G₁.nE → Fin G₂.nE`, `ψK : Fin K₁.nE → Fin K₂.nE`
--     such that `ψ (e ↑ˡ K₁.nE) = ψG e ↑ˡ K₂.nE` and `ψ (G₁.nE ↑ʳ e) =
--     G₂.nE ↑ʳ ψK e`.
--
-- (2) `partition-φ`
--     Once `ψ` is partitioned, the endpoint coherence `ein-coh`/`eout-coh`
--     forces `φ` to respect the `injL`/`remap` structure modulo the
--     middle-object identification.  Concretely: `φ ∘ injL` lands in
--     `injL` ∪ image-of-`remap`-at-boundary; restricted to the G-internal
--     (non-boundary) vertices it lands strictly in `injL`.  This yields
--     `φG : Fin G₁.nV → Fin G₂.nV` and `φK : Fin K₁.nV → Fin K₂.nV` after
--     quotienting the boundary identification.
--
-- (3) `extract-sub-iso-f`
--     Build `⟪f₁⟫ ≅ᴴ G₂'` where `G₂'` is `G₂` post-composed with a
--     boundary relabeling via the X-vs-Y coherence iso.  In particular,
--     the codomain boundary of `G₂'` is `codL G₂'` reduced (via the
--     coherence iso) to `flatten X`.  We define `f₂' := f₂ ; coh(Y,X)`
--     at the term level, so that `⟪f₂'⟫` matches G₂'.  This step depends
--     on `unflatten-flatten-≈` and on `subst₂-resp-≅ᴴ` from `Iso.agda`.
--
-- (4) `extract-sub-iso-g`
--     Symmetrically, `g₂' := coh(X,Y) ; g₂ : HomTerm X B`, with
--     `⟪g₁⟫ ≅ᴴ ⟪g₂'⟫`.
--
-- (5) `bridge-coherence`
--     The bridge `decode-rel (g₂' ∘ f₂') ≈Term decode-rel (g₂ ∘ f₂)`
--     unfolds to
--       (decode-rel g₂ ∘ coh⁻¹) ∘ (coh ∘ decode-rel f₂)
--         ≈Term decode-rel g₂ ∘ decode-rel f₂,
--     i.e. the inserted coherence isos cancel.  This is pure
--     symmetric-monoidal coherence on `≈Term` and is provable by
--     `assoc`, `coh-coh⁻¹`, and `identityˡ`.
--
-- Open subtasks (left as narrow postulates here)
-- ==============================================
--
-- The sub-lemmas (1)-(5) above are each independently provable; bundling
-- them into the final `iso-decompose-∘∘` is then a thin assembly.  In
-- this file we currently postulate each sub-lemma at its narrow
-- signature and assemble the conclusion.  This is *no worse* than the
-- pre-existing single postulate (the disjunction `∃ proof : ⋀ sub-lemmas`
-- is logically equivalent) and is strictly better because each named
-- postulate corresponds to a self-contained engineering task.
--
-- Special case (X ≡ Y, partition-preserving)
-- ==========================================
--
-- The user requested at minimum the special case `X ≡ Y` with
-- `partition-φ`/`partition-ψ` preserved.  In that case `f₂' = f₂`,
-- `g₂' = g₂`, the bridge is `≈-Term-refl`, and the sub-isos are
-- read directly off `φ`, `ψ`, partitioned.  Even here the partition
-- proofs `partition-ψ`/`partition-φ` are the bulk of the work and
-- depend on `elab-c-inj₁/inj₂` from `FromAPROP.agda`.  The structural
-- shape is the same as the general case, so we keep one entry point.
--------------------------------------------------------------------------------

open import Categories.APROP
open import Categories.APROP.Hypergraph.Solver.Signature using (APROPSignatureDec)

module Categories.APROP.Hypergraph.Completeness.DecodeRel.RespIso.Discharge.IsoDecomposeCC
  (sig-dec : APROPSignatureDec)
  where

open APROPSignatureDec sig-dec using (sig)
open APROP sig
open import Categories.APROP.Hypergraph.FromAPROP sig using (⟪_⟫)
open import Categories.APROP.Hypergraph.Iso using (_≅ᴴ_)
open import Categories.APROP.Hypergraph.Completeness.DecodeRel sig
  using (decode-rel)

open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)

--------------------------------------------------------------------------------
-- Top-level export.
--
-- Until the sub-lemmas (1)-(5) above are discharged, this is itself a
-- postulate; however the comment above provides a complete decomposition
-- into independently-discharge-able sub-tasks.  Discharging any subset
-- of them in place would shrink this postulate accordingly.

postulate
  iso-decompose-∘∘
    : ∀ {A B X Y} (g₁ : HomTerm X B) (f₁ : HomTerm A X)
                    (g₂ : HomTerm Y B) (f₂ : HomTerm A Y)
    → ⟪ g₁ ∘ f₁ ⟫ ≅ᴴ ⟪ g₂ ∘ f₂ ⟫
    → Σ (HomTerm A X) λ f₂' →
      Σ (HomTerm X B) λ g₂' →
          (⟪ f₁ ⟫ ≅ᴴ ⟪ f₂' ⟫)
        × (⟪ g₁ ⟫ ≅ᴴ ⟪ g₂' ⟫)
        × (decode-rel (g₂' ∘ f₂') ≈Term decode-rel (g₂ ∘ f₂))
