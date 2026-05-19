{-# OPTIONS #-}

--------------------------------------------------------------------------------
-- Phase 2: extend `decode-rel-resp-≅ᴴ-atomic` to the full inductive
-- theorem `decode-rel-resp-≅ᴴ-full` covering compound terms (∘ and ⊗).
--
-- This module ties together the four compound-side sub-modules:
--   * `RespIso.Atomic`          — atomic-vs-atomic (Phase 1, fully proved
--                                  modulo σ-related deep cases).
--   * `RespIso.AtomicCompound`  — atomic-vs-compound and its symmetric
--                                  direction.  Three narrow postulates
--                                  remain there.
--   * `RespIso.TensorTensor`    — ⊗⊗ via iso-decomposition.  One narrow
--                                  postulate (`iso-decompose-⊗⊗`).
--   * `RespIso.ComposeCompose`  — ∘∘ via iso-decomposition.  One narrow
--                                  postulate (`iso-decompose-∘∘`).
--
-- The recursive calls in this module are direct (not via the abstract
-- IH parameter of the sub-modules), so Agda's structural termination
-- checker accepts the recursion.  Status of the four compound branches:
--   * ⊗⊗ — discharged from `iso-decompose-⊗⊗`.
--   * ∘∘ — discharged from `iso-decompose-∘∘`.
--   * ∘⊗ — discharged from the narrow `iso-decompose-∘⊗` (whose only
--          remaining postulate is the coherence iso `γ` in
--          `Discharge/CrossOC.agda`).
--   * ⊗∘ — remaining local postulate (`decode-rel-resp-≅ᴴ-⊗∘`),
--          equivalent under `sym-≅ᴴ` to ∘⊗ but rejected by Agda's
--          structural termination check (see note below for the path
--          to discharge).
--------------------------------------------------------------------------------

open import Categories.APROP
open import Categories.APROP.Hypergraph.Solver.Signature using (APROPSignatureDec)

module Categories.APROP.Hypergraph.Completeness.DecodeRel.Inductive
  (sig-dec : APROPSignatureDec) where

open APROPSignatureDec sig-dec using (sig)
open APROP sig
open import Categories.APROP.Hypergraph.FromAPROP sig using (⟪_⟫)
open import Categories.APROP.Hypergraph.Iso using (_≅ᴴ_; sym-≅ᴴ)
open import Categories.APROP.Hypergraph.Completeness.DecodeRel sig
  using (decode-rel)

open import Categories.APROP.Hypergraph.Completeness.DecodeRel.RespIso.Atomic sig-dec
  using ( Atomic; atomic-Agen; atomic-id
        ; atomic-λ⇒; atomic-λ⇐; atomic-ρ⇒; atomic-ρ⇐
        ; atomic-α⇒; atomic-α⇐; atomic-σ
        ; decode-rel-resp-≅ᴴ-atomic
        )
open import Categories.APROP.Hypergraph.Completeness.DecodeRel.RespIso.AtomicCompound sig-dec
  using ( Compound; compound-∘; compound-⊗
        ; decode-rel-resp-≅ᴴ-atomic-compound
        ; decode-rel-resp-≅ᴴ-compound-atomic
        )
open import Categories.APROP.Hypergraph.Completeness.DecodeRel.RespIso.TensorTensor sig-dec
  using (iso-decompose-⊗⊗)
open import Categories.APROP.Hypergraph.Completeness.DecodeRel.RespIso.ComposeCompose sig-dec
  using (iso-decompose-∘∘)
-- The ∘⊗ cross-shape iso decomposition is narrowed (relative to a
-- monolithic postulate) in `Discharge/CrossOC.agda`: the bridge term
-- is proved categorically from the coherence iso `γ : Ap ⊗ Bq ≅ X`
-- supplied by `iso-decompose-∘⊗-primitive`.  We import the narrowed
-- theorem here and inline-dispatch the ∘⊗ branch from it directly;
-- only the symmetric ⊗∘ branch still requires a local postulate at
-- this layer for structural-termination reasons (see note above the
-- ⊗∘ postulate below).
open import Categories.APROP.Hypergraph.Completeness.DecodeRel.RespIso.Discharge.CrossOC sig-dec
  using (iso-decompose-∘⊗)

open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Data.Sum using (_⊎_; inj₁; inj₂)

--------------------------------------------------------------------------------
-- Every HomTerm is either atomic or compound.

atomic-or-compound : ∀ {A B} (f : HomTerm A B) → Atomic f ⊎ Compound f
atomic-or-compound (Agen h)  = inj₁ (atomic-Agen h)
atomic-or-compound id        = inj₁ atomic-id
atomic-or-compound (g ∘ f)   = inj₂ (compound-∘ g f)
atomic-or-compound (f ⊗₁ g)  = inj₂ (compound-⊗ f g)
atomic-or-compound λ⇒        = inj₁ atomic-λ⇒
atomic-or-compound λ⇐        = inj₁ atomic-λ⇐
atomic-or-compound ρ⇒        = inj₁ atomic-ρ⇒
atomic-or-compound ρ⇐        = inj₁ atomic-ρ⇐
atomic-or-compound α⇒        = inj₁ atomic-α⇒
atomic-or-compound α⇐        = inj₁ atomic-α⇐
atomic-or-compound (σ ⦃ s ⦄) = inj₁ (atomic-σ ⦃ s ⦄)

--------------------------------------------------------------------------------
-- Cross-shape postulate.  Only the symmetric direction `-⊗∘` is
-- still a local postulate at this layer: the forward `∘⊗` direction is
-- discharged inline below from the narrow `iso-decompose-∘⊗`
-- theorem in `Discharge/CrossOC.agda`.
--
-- Narrowing status
-- ================
--
-- The "deep math" for this case has been narrowed in
-- `Discharge/CrossOC.agda` to the single primitive postulate
--
--   iso-decompose-∘⊗-primitive : ⟪ g ∘ f ⟫ ≅ᴴ ⟪ p ⊗₁ q ⟫
--     → Σ ((Ap ⊗₀ Bq) ≅ X) λ γ →
--          (⟪ f ⟫ ≅ᴴ ⟪ γ.from ∘ (id ⊗₁ q) ⟫)
--        × (⟪ g ⟫ ≅ᴴ ⟪ (p ⊗₁ id) ∘ γ.to ⟫)
--
-- which extracts only the coherence iso `γ : Ap ⊗₀ Bq ≅ X` in
-- `FreeMonoidal` together with the two sub-isos.  The bridge term
-- (`decode-rel (g' ∘ f') ≈Term decode-rel (p ⊗ q)`) is *proved* there
-- from `γ.iso.isoˡ`, `⊗-∘-dist`, `idˡ`, `idʳ`, lifted through
-- `decode-rel` by a `decode-rel-resp-≈Term` lemma.
--
-- The forward `∘⊗` direction is then discharged inline in
-- `decode-rel-resp-≅ᴴ-full` below: structural termination is fine,
-- since the recursive calls are on `f₁` and `g₁` (subterms of the
-- LHS `g₁ ∘ f₁`).
--
-- The symmetric `⊗∘` direction is structurally trickier: there the
-- recursive subterms `f`, `g` live in the *second* argument
-- (`g ∘ f`), and Agda's termination checker rejects the lex-direction
-- decrease.  Two avenues were attempted and found insufficient at
-- this layer:
--
--   1.  Threading `decode-rel-resp-≅ᴴ-full` itself as a higher-order
--       `IH` parameter into `CrossOC.decode-rel-resp-≅ᴴ-∘⊗` applied
--       to `sym-≅ᴴ iso`.  Agda's termination checker traverses into
--       the parameterised module and observes the unguarded
--       recursive call on `f`, `g` (subterms of the second argument
--       `g ∘ f`), and rejects the definition with the same
--       lex-direction failure.
--
--   2.  Well-founded recursion on a syntactic size measure
--       `size f + size g`.  Mathematically the iso-decomposition
--       produces a coherence iso `γ` in `FreeMonoidal` whose
--       canonical factors `f' = γ.from ∘ (id ⊗₁ q)` and
--       `g' = (p ⊗₁ id) ∘ γ.to` carry the (unbounded) size of `γ`.
--       The recursive call needs `size f + size f' < size (p ⊗ q)
--       + size (g ∘ f)`, which reduces to `size γ.from < size p +
--       size g` — there is no a-priori bound on the size of `γ` in
--       the abstract iso-decomposition postulate, so size alone
--       does not strictly decrease.
--
-- A genuine discharge therefore requires either:
--   (a) a tighter primitive that bounds the size of `γ` (or
--       returns the canonical factors with controlled syntactic
--       shape), or
--   (b) a strong-induction measure that combines size with the
--       hypergraph-iso content (e.g. edge/vertex counts of the
--       decoded hypergraph), or
--   (c) a `--terminating`/TERMINATING annotation, which the
--       project consciously avoids.
--
-- For now the symmetric direction remains a local postulate at
-- this layer, equivalent under `sym-≅ᴴ` to the discharged
-- `decode-rel-resp-≅ᴴ-∘⊗` of `CrossOC`.

postulate
  decode-rel-resp-≅ᴴ-⊗∘
    : ∀ {Ap Aq Bp Bq X}
        (p : HomTerm Ap Bp) (q : HomTerm Aq Bq)
        (g : HomTerm X (Bp ⊗₀ Bq)) (f : HomTerm (Ap ⊗₀ Aq) X)
    → ⟪ p ⊗₁ q ⟫ ≅ᴴ ⟪ g ∘ f ⟫
    → decode-rel (p ⊗₁ q) ≈Term decode-rel (g ∘ f)

--------------------------------------------------------------------------------
-- The full inductive theorem.

decode-rel-resp-≅ᴴ-full
  : ∀ {A B} (f g : HomTerm A B)
  → ⟪ f ⟫ ≅ᴴ ⟪ g ⟫
  → decode-rel f ≈Term decode-rel g
decode-rel-resp-≅ᴴ-full f g iso
  with atomic-or-compound f | atomic-or-compound g
... | inj₁ af | inj₁ ag = decode-rel-resp-≅ᴴ-atomic af ag iso
... | inj₁ af | inj₂ cg = decode-rel-resp-≅ᴴ-atomic-compound af cg iso
... | inj₂ cf | inj₁ ag = decode-rel-resp-≅ᴴ-compound-atomic cf ag iso
-- ⊗⊗: decompose iso into sub-isos, recurse on subterms, combine.
... | inj₂ (compound-⊗ f₁ g₁) | inj₂ (compound-⊗ f₂ g₂) =
  let subisos = iso-decompose-⊗⊗ f₁ g₁ f₂ g₂ iso
      IH-f = decode-rel-resp-≅ᴴ-full f₁ f₂ (proj₁ subisos)
      IH-g = decode-rel-resp-≅ᴴ-full g₁ g₂ (proj₂ subisos)
  in ∘-resp-≈ ≈-Term-refl (∘-resp-≈ (⊗-resp-≈ IH-f IH-g) ≈-Term-refl)
-- ∘∘: decompose iso into sub-isos, recurse on subterms, combine via bridge.
... | inj₂ (compound-∘ g₁ f₁) | inj₂ (compound-∘ g₂ f₂) =
  let decomp  = iso-decompose-∘∘ g₁ f₁ g₂ f₂ iso
      f₂'     = proj₁ decomp
      g₂'     = proj₁ (proj₂ decomp)
      iso-f   = proj₁ (proj₂ (proj₂ decomp))
      iso-g   = proj₁ (proj₂ (proj₂ (proj₂ decomp)))
      bridge  = proj₂ (proj₂ (proj₂ (proj₂ decomp)))
      IH-f    = decode-rel-resp-≅ᴴ-full f₁ f₂' iso-f
      IH-g    = decode-rel-resp-≅ᴴ-full g₁ g₂' iso-g
  in ≈-Term-trans (∘-resp-≈ IH-g IH-f) bridge
-- Cross-shape ∘⊗: decompose iso into sub-isos and a coherence bridge
-- via the narrow `iso-decompose-∘⊗` theorem (in `Discharge/CrossOC.agda`),
-- recurse on the structural subterms `f` and `g` of the LHS, and
-- combine via the bridge.  Structurally analogous to the ∘∘ branch
-- above.
... | inj₂ (compound-∘ g₁ f₁) | inj₂ (compound-⊗ p q) =
  let decomp  = iso-decompose-∘⊗ g₁ f₁ p q iso
      f'      = proj₁ decomp
      g'      = proj₁ (proj₂ decomp)
      iso-f   = proj₁ (proj₂ (proj₂ decomp))
      iso-g   = proj₁ (proj₂ (proj₂ (proj₂ decomp)))
      brdg    = proj₂ (proj₂ (proj₂ (proj₂ decomp)))
      IH-f    = decode-rel-resp-≅ᴴ-full f₁ f' iso-f
      IH-g    = decode-rel-resp-≅ᴴ-full g₁ g' iso-g
  in ≈-Term-trans (∘-resp-≈ IH-g IH-f) brdg
-- Cross-shape ⊗∘: dispatched via the postulate above.  Structural
-- termination on this side fails because the recursive subterms
-- `f`, `g` live in the *second* argument `g ∘ f`, not the first
-- `p ⊗ q` -- and Agda's lex check looks at the first argument first.
-- Discharge via well-founded recursion on term size or a dedicated
-- `iso-decompose-⊗∘-primitive` (parallel to `∘⊗`).
... | inj₂ (compound-⊗ p q) | inj₂ (compound-∘ g f) =
  decode-rel-resp-≅ᴴ-⊗∘ p q g f iso
