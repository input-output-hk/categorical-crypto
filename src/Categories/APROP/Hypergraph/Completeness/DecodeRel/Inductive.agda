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
-- checker accepts the recursion.  Only the cross-shape cases (∘ vs ⊗,
-- ⊗ vs ∘) remain as local postulates in this file — they were left out
-- of the subagent dispatch.
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
-- Cross-shape postulate.  Only the forward direction (`-∘⊗`) is
-- postulated; the symmetric direction `-⊗∘` is derived constructively
-- below via `sym-≅ᴴ`.

postulate
  decode-rel-resp-≅ᴴ-∘⊗
    : ∀ {Ap Aq Bp Bq X}
        (g : HomTerm X (Bp ⊗₀ Bq)) (f : HomTerm (Ap ⊗₀ Aq) X)
        (p : HomTerm Ap Bp) (q : HomTerm Aq Bq)
    → ⟪ g ∘ f ⟫ ≅ᴴ ⟪ p ⊗₁ q ⟫
    → decode-rel (g ∘ f) ≈Term decode-rel (p ⊗₁ q)

decode-rel-resp-≅ᴴ-⊗∘
  : ∀ {Ap Aq Bp Bq X}
      (p : HomTerm Ap Bp) (q : HomTerm Aq Bq)
      (g : HomTerm X (Bp ⊗₀ Bq)) (f : HomTerm (Ap ⊗₀ Aq) X)
  → ⟪ p ⊗₁ q ⟫ ≅ᴴ ⟪ g ∘ f ⟫
  → decode-rel (p ⊗₁ q) ≈Term decode-rel (g ∘ f)
decode-rel-resp-≅ᴴ-⊗∘ p q g f iso =
  ≈-Term-sym (decode-rel-resp-≅ᴴ-∘⊗ g f p q (sym-≅ᴴ iso))

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
-- Cross-shape: postulated.
... | inj₂ (compound-∘ g f) | inj₂ (compound-⊗ p q) =
  decode-rel-resp-≅ᴴ-∘⊗ g f p q iso
... | inj₂ (compound-⊗ p q) | inj₂ (compound-∘ g f) =
  decode-rel-resp-≅ᴴ-⊗∘ p q g f iso
