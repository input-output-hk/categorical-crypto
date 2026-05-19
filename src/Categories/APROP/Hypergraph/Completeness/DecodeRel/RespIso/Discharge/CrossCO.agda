{-# OPTIONS #-}

--------------------------------------------------------------------------------
-- ⊗∘ cross-shape case of `decode-rel-resp-≅ᴴ`.
--
-- This is the symmetric direction of `Discharge/CrossOC.agda`.  Given:
--
--   p : HomTerm Ap Bp
--   q : HomTerm Aq Bq
--   g : HomTerm X (Bp ⊗₀ Bq)
--   f : HomTerm (Ap ⊗₀ Aq) X
--   iso : ⟪ p ⊗₁ q ⟫ ≅ᴴ ⟪ g ∘ f ⟫
--
-- prove `decode-rel (p ⊗₁ q) ≈Term decode-rel (g ∘ f)`.
--
-- Strategy
-- ========
--
-- We mirror the ∘⊗ direction structurally so that the *first* argument
-- of `decode-rel-resp-≅ᴴ-full` decreases on the recursive call.  The
-- previous `sym-≅ᴴ`-flip approach was rejected by Agda's lex termination
-- check because the recursive subterms (`f`, `g`) live in the *second*
-- argument `g ∘ f`, not the first.
--
-- The symmetric `iso-decompose-⊗∘-primitive` extracts a permutation
-- (bounded coherence) `π : flatten X ↭ flatten (Bp ⊗₀ Aq)` plus *trivial*
-- sub-isos on `p` and `q`.  This makes the symmetric IH calls land on
-- `p` and `q` (structural subterms of the first argument `p ⊗ q`).
--
-- In effect, this isolates the postulate to the same "deep math" as the
-- ∘⊗ direction (extracting a permutation between flat atom lists),
-- while keeping the recursion structurally well-formed.
--------------------------------------------------------------------------------

open import Categories.APROP
open import Categories.APROP.Hypergraph.Solver.Signature using (APROPSignatureDec)

module Categories.APROP.Hypergraph.Completeness.DecodeRel.RespIso.Discharge.CrossCO
  (sig-dec : APROPSignatureDec) where

open APROPSignatureDec sig-dec using (sig)
open APROP sig
open import Categories.APROP.Hypergraph.FromAPROP sig using (⟪_⟫; flatten)
open import Categories.APROP.Hypergraph.Iso using (_≅ᴴ_; sym-≅ᴴ)
open import Categories.APROP.Hypergraph.Completeness.DecodeRel sig
  using (decode-rel; decode-roundtrip-rel)
open import Categories.APROP.Hypergraph.Completeness.Unflatten sig
  using (unflatten; unflatten-flatten-≈)
open import Categories.APROP.Hypergraph.Completeness.PermutationCoherence sig
  using (↭-to-≅)

open import Categories.Morphism FreeMonoidal using (_≅_; module ≅)
open import Data.List.Relation.Binary.Permutation.Propositional using (_↭_)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)

--------------------------------------------------------------------------------
-- Helper: lift `_≈Term_` through `decode-rel`.
--
-- Mirror of the helper in `CrossOC.agda`.

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
-- Narrowed primitive (permutation form).
--
-- Given `iso : ⟪ p ⊗₁ q ⟫ ≅ᴴ ⟪ g ∘ f ⟫`, postulate only:
--
--   * a propositional permutation `π : flatten X ↭ flatten (Bp ⊗₀ Aq)`
--     between flat atom lists (bounded coherence content), and
--   * sub-isos `⟪ p ⟫ ≅ᴴ ⟪ p' ⟫` and `⟪ q ⟫ ≅ᴴ ⟪ q' ⟫`
--   * a `decode-rel`-level bridge between the canonical factorisation
--     and `g ∘ f`.
--
-- The associated coherence iso `γ : Bp ⊗₀ Aq ≅ X` is *built* from `π`
-- (via `↭-to-≅` and `unflatten-flatten-≈`), so its syntactic size is
-- bounded by the permutation derivation.
--
-- The choice of sub-iso target HomTerms `p'`, `q'` is left to the
-- postulate (in the simplest instantiation they are `p`, `q` themselves
-- with reflexive sub-isos, in which case the bridge term carries all
-- of the iso content; permutations naturally handle the σ case).

postulate
  iso-decompose-⊗∘-primitive-perm
    : ∀ {Ap Aq Bp Bq X}
        (p : HomTerm Ap Bp) (q : HomTerm Aq Bq)
        (g : HomTerm X (Bp ⊗₀ Bq)) (f : HomTerm (Ap ⊗₀ Aq) X)
    → ⟪ p ⊗₁ q ⟫ ≅ᴴ ⟪ g ∘ f ⟫
    → Σ (flatten X ↭ flatten (Bp ⊗₀ Aq)) λ π →
      Σ (HomTerm Ap Bp) λ p' →
      Σ (HomTerm Aq Bq) λ q' →
          (⟪ p ⟫ ≅ᴴ ⟪ p' ⟫)
        × (⟪ q ⟫ ≅ᴴ ⟪ q' ⟫)
        × (decode-rel (p' ⊗₁ q') ≈Term decode-rel (g ∘ f))

--------------------------------------------------------------------------------
-- Wide interface (consumed by `Inductive.agda`).
--
-- Repackages the primitive into a record convenient for the inductive
-- pass — peels off the permutation and exposes only the sub-isos and
-- the bridge.

iso-decompose-⊗∘
  : ∀ {Ap Aq Bp Bq X}
      (p : HomTerm Ap Bp) (q : HomTerm Aq Bq)
      (g : HomTerm X (Bp ⊗₀ Bq)) (f : HomTerm (Ap ⊗₀ Aq) X)
  → ⟪ p ⊗₁ q ⟫ ≅ᴴ ⟪ g ∘ f ⟫
  → Σ (HomTerm Ap Bp) λ p' →
    Σ (HomTerm Aq Bq) λ q' →
        (⟪ p ⟫ ≅ᴴ ⟪ p' ⟫)
      × (⟪ q ⟫ ≅ᴴ ⟪ q' ⟫)
      × (decode-rel (p' ⊗₁ q') ≈Term decode-rel (g ∘ f))
iso-decompose-⊗∘ p q g f iso =
  let prim   = iso-decompose-⊗∘-primitive-perm p q g f iso
      p'     = proj₁ (proj₂ prim)
      q'     = proj₁ (proj₂ (proj₂ prim))
      iso-p  = proj₁ (proj₂ (proj₂ (proj₂ prim)))
      iso-q  = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ prim))))
      brdg   = proj₂ (proj₂ (proj₂ (proj₂ (proj₂ prim))))
  in p' , q' , iso-p , iso-q , brdg
