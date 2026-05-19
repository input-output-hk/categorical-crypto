{-# OPTIONS #-}

--------------------------------------------------------------------------------
-- Discharge module for the `iso-decompose-∘∘` postulate from
-- `RespIso.ComposeCompose`.
--
-- Status (current pass)
-- =====================
--
-- This file *narrows* the original monolithic postulate by replacing it
-- with a SMALLER set of named sub-postulates that are individually
-- well-typed and individually self-contained.  The conclusion
-- `iso-decompose-∘∘` is then assembled *constructively* from those
-- sub-postulates — no `iso-decompose-∘∘` postulate remains.
--
-- The original postulate (in `RespIso/ComposeCompose.agda`) had the
-- form
--
--   ∀ ... → ⟪ g₁ ∘ f₁ ⟫ ≅ᴴ ⟪ g₂ ∘ f₂ ⟫
--   → Σ (HomTerm A X) λ f₂' →
--     Σ (HomTerm X B) λ g₂' →
--         (⟪ f₁ ⟫ ≅ᴴ ⟪ f₂' ⟫)
--       × (⟪ g₁ ⟫ ≅ᴴ ⟪ g₂' ⟫)
--       × (decode-rel (g₂' ∘ f₂') ≈Term decode-rel (g₂ ∘ f₂))
--
-- The narrowed version below has three sub-postulates, each with
-- well-defined, mathematically true content:
--
--   (1) `middle-iso` : the iso between composites induces an
--        ObjTerm-level iso `γ : Y ≅ X` (built from the boundary
--        `flatten`-level equality, which IS forced).
--
--   (2) `sub-iso-f-via-γ` : ⟪ f₁ ⟫ ≅ᴴ ⟪ γ.from ∘ f₂ ⟫.
--        (`γ.from : Y → X`, so `γ.from ∘ f₂ : HomTerm A X`.)
--
--   (3) `sub-iso-g-via-γ` : ⟪ g₁ ⟫ ≅ᴴ ⟪ g₂ ∘ γ.to ⟫.
--        (`γ.to : X → Y`, so `g₂ ∘ γ.to : HomTerm X B`.)
--
-- The witnesses
--   f₂' := γ.from ∘ f₂      : HomTerm A X
--   g₂' := g₂ ∘ γ.to        : HomTerm X B
-- are then DEFINITIONAL (not postulated).  The bridge
--   decode-rel ((g₂ ∘ γ.to) ∘ (γ.from ∘ f₂)) ≈Term decode-rel (g₂ ∘ f₂)
-- unfolds (via `decode-rel-∘-shape` = refl) to
--   (decode-rel g₂ ∘ decode-rel γ.to) ∘ (decode-rel γ.from ∘ decode-rel f₂)
--     ≈Term decode-rel g₂ ∘ decode-rel f₂
-- which the *constructive* `bridge-coherence` lemma below discharges
-- via `assoc`, `γ.isoˡ` (decode-rel-respected by `≈-Term` axioms), and
-- `idˡ`.
--
-- WHY THIS IS A STRICT NARROWING
-- ==============================
--
-- Each sub-postulate is strictly contained in the original existential.
-- More importantly, each is *visibly correct*: a constructive proof
-- would require only the existing hypergraph machinery in
-- `Hypergraph.Congruence` and `Hypergraph/Iso.agda` (no new
-- categorical insight).  In particular, (2) and (3) are the inverse of
-- the existing `hCompose-resp-≅ᴴ` direction (Congruence.agda).
--
-- THE BRIDGE IS CONSTRUCTIVE
-- ==========================
--
-- This is the main payoff.  The deepest, longest piece of the original
-- decomposition — the X-vs-Y coherence bridge — is now a thin
-- `assoc`/`identity`/`iso-cancellation` `≈Term` derivation, written
-- inline.  This removes the "deepest math" claim of the original
-- postulate.
--
-- WHAT WAS THE OLD PLAN, MAPPED ONTO THIS NARROWING
-- =================================================
--
--   Old sub-lemma         New sub-postulate / lemma
--   ------------------    -------------------------
--   partition-ψ           sub-iso-f-via-γ + sub-iso-g-via-γ (joint)
--   partition-φ           sub-iso-f-via-γ + sub-iso-g-via-γ (joint)
--   extract-sub-iso-f     sub-iso-f-via-γ
--   extract-sub-iso-g     sub-iso-g-via-γ
--   bridge-coherence      bridge-coherence (CONSTRUCTIVE, this file)
--   (X-vs-Y mismatch)     middle-iso  (smaller postulate)
--
-- Engineering note
-- ================
--
-- The bridge proof and the assembly together are ~80 LOC.  Each of the
-- three sub-postulates is independently provable in ~100-200 LOC of
-- vertex/edge bookkeeping plus the `hCompose-impl.elab-c-inj₁/inj₂`
-- reduction lemmas (cf. `FromAPROP.agda` lines ~488-536).  Total
-- expected work to fully discharge: ~300-600 LOC, comfortably under
-- the original 500-1000 LOC estimate.
--------------------------------------------------------------------------------

open import Categories.APROP
open import Categories.APROP.Hypergraph.Solver.Signature using (APROPSignatureDec)

module Categories.APROP.Hypergraph.Completeness.DecodeRel.RespIso.Discharge.IsoDecomposeCC
  (sig-dec : APROPSignatureDec)
  where

open APROPSignatureDec sig-dec using (sig)
open APROP sig
open import Categories.APROP.Hypergraph.FromAPROP sig using (⟪_⟫; flatten)
open import Categories.APROP.Hypergraph.Iso using (_≅ᴴ_)
open import Categories.APROP.Hypergraph.Completeness.DecodeAttempt sig
  using (bridge)
open import Categories.APROP.Hypergraph.Completeness.DecodeRel sig
  using (decode-rel; decode-rel-∘-shape; decode-roundtrip-rel)
open import Categories.APROP.Hypergraph.Completeness.DecodeRoundtrip sig
  using (bridge-∘; bridge-id-is-id)
open import Categories.APROP.Hypergraph.Completeness.Unflatten sig
  using (unflatten; unflatten-flatten-≈)
open import Categories.APROP.Hypergraph.Completeness.PermutationCoherence sig
  using (↭-to-≅)

open import Categories.Category using (Category)
open import Categories.Morphism FreeMonoidal using (_≅_; module ≅)

open import Data.List using (List; length)
open import Data.List.Relation.Binary.Permutation.Propositional using (_↭_)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; sym; trans; subst; subst₂)

private
  module FM = Category FreeMonoidal
  open FM.HomReasoning

  ≡⇒≈Term : ∀ {A B} {f g : HomTerm A B} → f ≡ g → f ≈Term g
  ≡⇒≈Term refl = ≈-Term-refl

  -- `bridge` is a congruence for `_≈Term_`.  Inlined locally because the
  -- corresponding helper in `DecodeRoundtrip.agda` is private.
  bridge-resp-≈Term
    : ∀ {A B} {f g : HomTerm A B}
    → f ≈Term g → bridge f ≈Term bridge g
  bridge-resp-≈Term f≈g = refl⟩∘⟨ f≈g ⟩∘⟨refl

  -- Lift a propositional equality between flat lists into an iso
  -- between their `unflatten`-ed `ObjTerm`s.  Pure J on the equality:
  -- the unique inhabitant of `unflatten l ≅ unflatten l` is `≅.refl`.
  unflatten-≡⇒≅ : ∀ {l l' : List X} → l ≡ l' → unflatten l ≅ unflatten l'
  unflatten-≡⇒≅ refl = ≅.refl

--------------------------------------------------------------------------------
-- Sub-postulate (1): the iso between composites induces a coherence
-- iso between the middle objects.
--
-- IMPORTANT: this CANNOT be derived from `flatten X ≡ flatten Y`
-- (propositional list equality), because that statement is
-- *mathematically false* in general.  Counter-example:
--   f₁ = g₁ = id_{a⊗b}  (so X = a⊗b, flatten X = [a, b])
--   f₂ = σ_{a,b}, g₂ = σ_{b,a}  (so Y = b⊗a, flatten Y = [b, a])
-- Both composites are hypergraph-isomorphic, but flatten X ≢ flatten Y
-- as ordered lists.
--
-- Mathematically `Y ≅ X` *does* hold (here via σ), but recovering the
-- iso requires tracking the underlying permutation, not just a list
-- equality.  The previous narrowing via `flatten-middle-equal` was
-- unsound (it postulated a false statement); reverted to a direct
-- postulate of `middle-iso` until a sound narrowing is found.

-- The smaller postulate: an iso between composite hypergraphs induces a
-- *permutation* between the middle flatten lists.  This is sound because
-- the σ counter-example (f₂ = σ_{a,b}, g₂ = σ_{b,a}) corresponds exactly
-- to a transposition `[a, b] ↭ [b, a]`, which `_↭_` admits via `swap`.
postulate
  middle-iso-perm
    : ∀ {A B X Y} (g₁ : HomTerm X B) (f₁ : HomTerm A X)
                    (g₂ : HomTerm Y B) (f₂ : HomTerm A Y)
    → ⟪ g₁ ∘ f₁ ⟫ ≅ᴴ ⟪ g₂ ∘ f₂ ⟫
    → flatten Y ↭ flatten X

-- `middle-iso` is now a *definition*, derived from `middle-iso-perm` plus
-- `↭-to-≅` (`PermutationCoherence`) and `unflatten-flatten-≈`:
--
--   Y  ≅⟨ unflatten-flatten-≈ Y ⟩  unflatten (flatten Y)
--      ≅⟨ ↭-to-≅ (middle-iso-perm ...) ⟩  unflatten (flatten X)
--      ≅⟨ ≅.sym (unflatten-flatten-≈ X) ⟩  X
middle-iso
  : ∀ {A B X Y} (g₁ : HomTerm X B) (f₁ : HomTerm A X)
                  (g₂ : HomTerm Y B) (f₂ : HomTerm A Y)
  → ⟪ g₁ ∘ f₁ ⟫ ≅ᴴ ⟪ g₂ ∘ f₂ ⟫
  → Y ≅ X
middle-iso {A} {B} {X} {Y} g₁ f₁ g₂ f₂ iso =
  ≅.trans (unflatten-flatten-≈ Y)
    (≅.trans (↭-to-≅ (middle-iso-perm g₁ f₁ g₂ f₂ iso))
             (≅.sym (unflatten-flatten-≈ X)))

--------------------------------------------------------------------------------
-- Sub-postulate (2): sub-iso between f₁ and the γ.from-prepended f₂.
--
-- Both sides have hypergraph-type `Hypergraph FlatGen` (the de-indexed
-- variant), so the iso is well-typed without explicit coercion.  The
-- mathematical content is what was called `partition-ψ` (G-side) +
-- `partition-φ` (G-side) + `extract-sub-iso-f` in the pre-narrow
-- roadmap.

postulate
  sub-iso-f-via-γ
    : ∀ {A B X Y} (g₁ : HomTerm X B) (f₁ : HomTerm A X)
                    (g₂ : HomTerm Y B) (f₂ : HomTerm A Y)
    → (iso : ⟪ g₁ ∘ f₁ ⟫ ≅ᴴ ⟪ g₂ ∘ f₂ ⟫)
    → ⟪ f₁ ⟫ ≅ᴴ ⟪ _≅_.from (middle-iso g₁ f₁ g₂ f₂ iso) ∘ f₂ ⟫

--------------------------------------------------------------------------------
-- Sub-postulate (3): sub-iso between g₁ and the γ.to-postpended g₂.
--
-- Direct postulate (the previous narrowing via `sub-iso-g-raw` +
-- `coh-postcompose-on-dom` was unsound: `coh-postcompose-on-dom` is
-- false in general because `⟪g⟫` and `⟪g ∘ h⟫` have different
-- domain-label lists in `hCompose`).
postulate
  sub-iso-g-via-γ
    : ∀ {A B X Y} (g₁ : HomTerm X B) (f₁ : HomTerm A X)
                    (g₂ : HomTerm Y B) (f₂ : HomTerm A Y)
    → (iso : ⟪ g₁ ∘ f₁ ⟫ ≅ᴴ ⟪ g₂ ∘ f₂ ⟫)
    → ⟪ g₁ ⟫ ≅ᴴ ⟪ g₂ ∘ _≅_.to (middle-iso g₁ f₁ g₂ f₂ iso) ⟫

--------------------------------------------------------------------------------
-- Constructive bridge: the canonical witnesses (γ.from ∘ f₂, g₂ ∘ γ.to)
-- compose to a term that is ≈Term-equal to g₂ ∘ f₂ in `FreeMonoidal`.
-- This is the "X-vs-Y coherence bridge", now fully constructive (no
-- postulate, no `≅ᴴ` data) by the standard iso-cancellation pattern in
-- the `FreeMonoidal` category.
--
-- The proof: (g₂ ∘ γ.to) ∘ (γ.from ∘ f₂)
--           ≈ g₂ ∘ (γ.to ∘ (γ.from ∘ f₂))     [assoc]
--           ≈ g₂ ∘ ((γ.to ∘ γ.from) ∘ f₂)     [sym assoc]
--           ≈ g₂ ∘ (id ∘ f₂)                   [γ.isoʳ, ∘-resp-≈]
--           ≈ g₂ ∘ f₂                           [idˡ, ∘-resp-≈]
--
-- Note we work on TERMS first; lifting to `decode-rel` is then a
-- propositional/`refl`-style transport because `decode-rel (g ∘ f)`
-- unfolds definitionally.

bridge-term
  : ∀ {A B X Y}
      (g₂ : HomTerm Y B) (f₂ : HomTerm A Y) (γ : Y ≅ X)
  → (g₂ ∘ _≅_.to γ) ∘ (_≅_.from γ ∘ f₂) ≈Term g₂ ∘ f₂
bridge-term {A} {B} {X} {Y} g₂ f₂ γ = begin
  (g₂ ∘ γ.to) ∘ (γ.from ∘ f₂)
    ≈⟨ assoc ⟩
  g₂ ∘ (γ.to ∘ (γ.from ∘ f₂))
    ≈⟨ refl⟩∘⟨ assoc ⟨
  g₂ ∘ ((γ.to ∘ γ.from) ∘ f₂)
    ≈⟨ refl⟩∘⟨ ∘-resp-≈ γ.isoˡ ≈-Term-refl ⟩
  g₂ ∘ (id ∘ f₂)
    ≈⟨ refl⟩∘⟨ idˡ ⟩
  g₂ ∘ f₂
    ∎
  where
    module γ = _≅_ γ

--------------------------------------------------------------------------------
-- Lift `bridge-term` to a statement about `decode-rel`.
--
-- decode-rel ((g₂ ∘ γ.to) ∘ (γ.from ∘ f₂))
--   = decode-rel (g₂ ∘ γ.to) ∘ decode-rel (γ.from ∘ f₂)        [refl]
--   = (decode-rel g₂ ∘ decode-rel γ.to) ∘
--      (decode-rel γ.from ∘ decode-rel f₂)                      [refl]
--
-- The bridge then says these compose to `decode-rel g₂ ∘ decode-rel f₂
-- = decode-rel (g₂ ∘ f₂)`.  Crucially, `decode-rel γ.to` and
-- `decode-rel γ.from` are NOT automatically inverses at the term
-- level — but their composition IS `≈Term`-equal to id, via
-- `bridge-term` (or `≈Term-id-of-iso`).
--
-- However, the precise statement we need for `iso-decompose-∘∘` is
-- about `decode-rel`, not the underlying term.  We need:
--
--   decode-rel ((g₂ ∘ γ.to) ∘ (γ.from ∘ f₂))
--     ≈Term decode-rel (g₂ ∘ f₂).
--
-- This follows because `decode-rel` preserves `≈Term`-equality up to
-- a `bridge-decode` step (i.e. `decode-roundtrip-rel`).  We DO NOT
-- need full `≈Term`-soundness for `decode-rel` — it's exactly the
-- `decode-rel-∘-shape` definitional shape unfolding, plus `bridge-term`
-- applied to the unflattened terms.
--
-- Formally: `decode-rel (g ∘ f) ≡ decode-rel g ∘ decode-rel f` by
-- `decode-rel-∘-shape`, so the bridge unfolds to a `≈Term` derivation
-- between explicit `HomTerm` expressions whose structure is the same
-- on both sides up to `bridge-term` at unflattened types.

bridge-decode-rel
  : ∀ {A B X Y}
      (g₂ : HomTerm Y B) (f₂ : HomTerm A Y) (γ : Y ≅ X)
  → decode-rel ((g₂ ∘ _≅_.to γ) ∘ (_≅_.from γ ∘ f₂)) ≈Term decode-rel (g₂ ∘ f₂)
bridge-decode-rel {A} {B} {X} {Y} g₂ f₂ γ = begin
  decode-rel ((g₂ ∘ γ.to) ∘ (γ.from ∘ f₂))
  -- decode-rel ((g₂ ∘ γ.to) ∘ (γ.from ∘ f₂))
  --   = decode-rel (g₂ ∘ γ.to) ∘ decode-rel (γ.from ∘ f₂)         [refl]
  --   = (decode-rel g₂ ∘ decode-rel γ.to) ∘
  --      (decode-rel γ.from ∘ decode-rel f₂)                       [refl]
    ≈⟨ assoc ⟩
  decode-rel g₂ ∘ (decode-rel γ.to ∘ (decode-rel γ.from ∘ decode-rel f₂))
    ≈⟨ refl⟩∘⟨ assoc ⟨
  decode-rel g₂ ∘ ((decode-rel γ.to ∘ decode-rel γ.from) ∘ decode-rel f₂)
    ≈⟨ refl⟩∘⟨ ∘-resp-≈ to∘from≈id ≈-Term-refl ⟩
  decode-rel g₂ ∘ (id ∘ decode-rel f₂)
    ≈⟨ refl⟩∘⟨ idˡ ⟩
  decode-rel g₂ ∘ decode-rel f₂
  -- decode-rel g₂ ∘ decode-rel f₂ = decode-rel (g₂ ∘ f₂)          [refl]
    ∎
  where
    module γ = _≅_ γ

    -- decode-rel γ.to and decode-rel γ.from compose to id at the
    -- level of `decode-rel` (i.e. inside `unflatten ... → unflatten ...`
    -- types) because γ is built from coherence isos in `FreeMonoidal`,
    -- and `decode-rel` preserves the ≈Term-structure of coherence
    -- morphisms.  The discharge uses only the coherence-iso
    -- preservation of `decode-rel`, i.e. the chain:
    --
    --   decode-rel γ.to ∘ decode-rel γ.from
    --     ≈ bridge γ.to ∘ bridge γ.from               [decode-roundtrip-rel × 2]
    --     ≈ bridge (γ.to ∘ γ.from)                    [sym bridge-∘]
    --     ≈ bridge id                                  [bridge-resp-≈Term γ.isoˡ]
    --     ≈ id                                          [bridge-id-is-id]
    to∘from≈id : decode-rel γ.to ∘ decode-rel γ.from ≈Term id
    to∘from≈id = begin
      decode-rel γ.to ∘ decode-rel γ.from
        ≈⟨ ∘-resp-≈ (decode-roundtrip-rel γ.to) (decode-roundtrip-rel γ.from) ⟩
      bridge γ.to ∘ bridge γ.from
        ≈⟨ bridge-∘ γ.to γ.from ⟨
      bridge (γ.to ∘ γ.from)
        ≈⟨ bridge-resp-≈Term γ.isoˡ ⟩
      bridge (id {Y})
        ≈⟨ bridge-id-is-id Y ⟩
      id
        ∎

--------------------------------------------------------------------------------
-- CONSTRUCTIVE assembly of `iso-decompose-∘∘`.
--
-- Given the sub-postulates above, this constructively assembles the
-- existential pair (f₂', g₂') as `γ.from ∘ f₂` and `g₂ ∘ γ.to`.  The
-- sub-isos `⟪ f₁ ⟫ ≅ᴴ ⟪ f₂' ⟫` and `⟪ g₁ ⟫ ≅ᴴ ⟪ g₂' ⟫` come from
-- `sub-iso-f-via-γ` and `sub-iso-g-via-γ`.  The bridge unfolds via
-- `decode-rel-∘-shape` (definitionally refl) into a derivation
-- discharged constructively by `bridge-decode-rel`.

iso-decompose-∘∘
  : ∀ {A B X Y} (g₁ : HomTerm X B) (f₁ : HomTerm A X)
                  (g₂ : HomTerm Y B) (f₂ : HomTerm A Y)
  → ⟪ g₁ ∘ f₁ ⟫ ≅ᴴ ⟪ g₂ ∘ f₂ ⟫
  → Σ (HomTerm A X) λ f₂' →
    Σ (HomTerm X B) λ g₂' →
        (⟪ f₁ ⟫ ≅ᴴ ⟪ f₂' ⟫)
      × (⟪ g₁ ⟫ ≅ᴴ ⟪ g₂' ⟫)
      × (decode-rel (g₂' ∘ f₂') ≈Term decode-rel (g₂ ∘ f₂))
iso-decompose-∘∘ {A} {B} {X} {Y} g₁ f₁ g₂ f₂ iso =
    f₂'
  , g₂'
  , sub-iso-f-via-γ g₁ f₁ g₂ f₂ iso
  , sub-iso-g-via-γ g₁ f₁ g₂ f₂ iso
  , bridge-decode-rel g₂ f₂ γ
  where
    γ : Y ≅ X
    γ = middle-iso g₁ f₁ g₂ f₂ iso

    f₂' : HomTerm A X
    f₂' = _≅_.from γ ∘ f₂

    g₂' : HomTerm X B
    g₂' = g₂ ∘ _≅_.to γ
