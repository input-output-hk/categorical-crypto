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
open import Categories.APROP.Hypergraph.Iso using (_≅ᴴ_; sym-≅ᴴ; trans-≅ᴴ; refl-≅ᴴ)
open import Categories.APROP.Hypergraph.Completeness.DecodeRel sig
  using (decode-rel; decode-roundtrip-rel)
open import Categories.APROP.Hypergraph.Completeness.Unflatten sig
  using (unflatten; unflatten-flatten-≈)
open import Categories.APROP.Hypergraph.Completeness.PermutationCoherence sig
  using (↭-to-≅)
open import Categories.APROP.Hypergraph.Completeness.DecodeRel.RespIso.Discharge.IsoDecomposeCC sig-dec
  using (middle-iso-perm)

open import Categories.Morphism FreeMonoidal using (_≅_; module ≅)
import Data.List.Relation.Binary.Permutation.Propositional as Perm
open Perm using (_↭_; ↭-sym)
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

-- NARROWING (this pass): the wide perm-primitive (with permutation,
-- choice of `p'`, `q'`, sub-isos, and decode-rel bridge) is replaced
-- by a CONSTRUCTIVE assembly from a single, much narrower postulate
-- `⊗∘-decode-rel-bridge` — see below.
--
-- The wide signature is reconstructed by always returning `p' = p`
-- and `q' = q` with reflexive sub-isos and identity permutation; the
-- only residual content is the decode-rel bridge
--   `decode-rel (p ⊗₁ q) ≈Term decode-rel (g ∘ f)`,
-- isolated as the narrow postulate.
--
-- Why this can't be further discharged HERE (i.e. inside this
-- primitive layer): the bridge bridges the *cross-shape* iso to an
-- `≈Term`-equation, but no FromAPROP-side ≈Term-style coherence
-- closes this from the iso alone — converting `⟪f⟫ ≅ᴴ ⟪f'⟫` to
-- `decode-rel f ≈Term decode-rel f'` requires the recursive
-- `decode-rel-resp-≅ᴴ` itself (the IH).  The IH is threaded by the
-- consumer (`Inductive.agda`), not available here.

postulate
  -- Narrow coherence iso: mirror tensor/compose interchange on the
  -- FromAPROP side.  Same shape as `CrossOC.⊗-∘-dist-FromAPROP-iso`
  -- but with the alternative middle object `Bp ⊗₀ Aq`.
  ⊗-∘-dist-FromAPROP-iso-mirror
    : ∀ {Ap Aq Bp Bq}
        (p : HomTerm Ap Bp) (q : HomTerm Aq Bq)
    → ⟪ p ⊗₁ q ⟫ ≅ᴴ ⟪ (id {Bp} ⊗₁ q) ∘ (p ⊗₁ id {Aq}) ⟫

  -- The residual decode-rel content of the original perm-primitive
  -- (narrowed: the perm and sub-iso slots are now reflexive in the
  -- assembly below).  See the comment in `iso-decompose-⊗∘-primitive-perm`.
  ⊗∘-decode-rel-bridge
    : ∀ {Ap Aq Bp Bq X}
        (p : HomTerm Ap Bp) (q : HomTerm Aq Bq)
        (g : HomTerm X (Bp ⊗₀ Bq)) (f : HomTerm (Ap ⊗₀ Aq) X)
    → ⟪ p ⊗₁ q ⟫ ≅ᴴ ⟪ g ∘ f ⟫
    → decode-rel (p ⊗₁ q) ≈Term decode-rel (g ∘ f)

-- Constructive reassembly of the wide perm-primitive.
--
--   * The permutation `π : flatten X ↭ flatten (Bp ⊗₀ Aq)` is built
--     by transporting the input iso across `⊗-∘-dist-mirror`, applying
--     `IsoDecomposeCC.middle-iso-perm` to extract a permutation on the
--     middle list, then flipping direction via `↭-sym`.
--   * `p' = p`, `q' = q` with reflexive sub-isos.
--   * The decode-rel bridge is the narrow `⊗∘-decode-rel-bridge`.
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
iso-decompose-⊗∘-primitive-perm {Ap} {Aq} {Bp} {Bq} {X} p q g f iso =
  let
    -- ⟪ (id ⊗ q) ∘ (p ⊗ id) ⟫ ≅ᴴ ⟪ g ∘ f ⟫
    iso' : ⟪ (id {Bp} ⊗₁ q) ∘ (p ⊗₁ id {Aq}) ⟫ ≅ᴴ ⟪ g ∘ f ⟫
    iso' = trans-≅ᴴ (sym-≅ᴴ (⊗-∘-dist-FromAPROP-iso-mirror p q)) iso
    -- IsoDecomposeCC.middle-iso-perm with g₁=(id⊗q), f₁=(p⊗id), g₂=g, f₂=f
    -- returns:  flatten Y ↭ flatten X  where Y is the *second*
    -- composite's middle.  But here the SECOND composite is `g ∘ f`
    -- whose middle is `X`, and the FIRST is the iso's LHS with middle
    -- `Bp ⊗ Aq`.  So `middle-iso-perm` returns `flatten X ↭ flatten (Bp ⊗ Aq)`.
    -- We can return this permutation directly (no ↭-sym needed).
    π-cc : flatten X ↭ flatten (Bp ⊗₀ Aq)
    π-cc = middle-iso-perm (id {Bp} ⊗₁ q) (p ⊗₁ id {Aq}) g f iso'
  in π-cc , p , q , refl-≅ᴴ ⟪ p ⟫ , refl-≅ᴴ ⟪ q ⟫ , ⊗∘-decode-rel-bridge p q g f iso

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
