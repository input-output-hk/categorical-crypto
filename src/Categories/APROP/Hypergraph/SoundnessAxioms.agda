{-# OPTIONS --without-K #-}

--------------------------------------------------------------------------------
-- Per-axiom soundness *postulates* and the proofs that depend on them.
--
-- Everything constructive (i.e. the proofs that do NOT require any of the
-- postulates below) has been moved to `SoundnessProved`, which is
-- `--safe`.  This module retains only:
--
--   1. Focused postulates for structural claims that haven't been proved
--      constructively yet:
--        * `hTensor-G-hEmpty-iso-substed`
--        * `subst₂-hId-assoc-cancel`
--   2. Derivations that depend on those postulates:
--        * `subst₂-hId-cancel`  (from `hTensor-G-hEmpty-iso-substed`)
--        * `ρ⇒∘ρ⇐-sound`        (uses `subst₂-hId-cancel`)
--        * `α⇒∘α⇐-sound`        (uses `subst₂-hId-assoc-cancel`)
--   3. Flat postulates for the five still-unproven atomic axioms:
--        * `ρ⇒∘f⊗id≈f∘ρ⇒-sound`   (ρ-nat)
--        * `σ∘[f⊗g]≈[g⊗f]∘σ-sound` (σ-nat)
--        * `hexagon-sound`, `assoc-sound`, `⊗-∘-dist-sound`
--
-- The constructive proofs (idˡ, idʳ, λ-family, ρ⇐∘ρ⇒, α⇐∘α⇒, σ∘σ,
-- λ⇒∘id⊗f), plus the generic helpers (`hCompose-hId-R-iso-generic`,
-- `hCompose-hId-L-iso-generic`, `hTensor-hEmpty-G-iso`) live in
-- `SoundnessProved`.
--------------------------------------------------------------------------------

open import Categories.APROP

module Categories.APROP.Hypergraph.SoundnessAxioms (sig : APROPSignature) where

open APROP sig
open import Categories.APROP.Hypergraph.Core
open import Categories.APROP.Hypergraph.FromAPROP sig
  using (FlatGen; flatten; hId; hTensor; hEmpty)
open import Categories.APROP.Hypergraph.Translation sig
open import Categories.APROP.Hypergraph.Iso
open import Categories.APROP.Hypergraph.PrunedCompose sig

-- Constructive proofs and generic helpers live in `SoundnessProved`.
-- We need `idˡ-sound` for the `ρ⇒∘ρ⇐-sound` / `α⇒∘α⇐-sound` chains
-- below; we re-export the other constructive `-sound` lemmas for
-- clients who want a single import site.
open import Categories.APROP.Hypergraph.SoundnessProved sig public
  using ( idˡ-sound; idʳ-sound
        ; λ⇒∘id⊗f≈f∘λ⇒-sound
        ; λ⇐∘λ⇒-sound; λ⇒∘λ⇐-sound
        ; ρ⇐∘ρ⇒-sound; α⇐∘α⇒-sound
        ; σ∘σ-sound
        ; hCompose-hId-R-iso-generic
        ; hCompose-hId-L-iso-generic
        ; hTensor-hEmpty-G-iso
        ; hTensor-hEmpty-hId-iso)

open import Data.List using (List; _++_)
open import Data.List.Properties using (++-identityʳ; ++-assoc)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; cong₂; sym; trans; subst; subst₂)

--------------------------------------------------------------------------------
-- "+0 RIGHT-cancel" iso: for any G, the boundary-subst'd
-- `hTensor G hEmpty` is ≅ᴴ to G.  Mirror of `hTensor-hEmpty-G-iso`
-- but the subst₂ around the result is non-trivial: `As ++ [] ≢ As`
-- and `Bs ++ [] ≢ Bs` definitionally (unlike `[] ++ As = As`).
--
-- The construction would go field-by-field through the subst₂ field
-- projections (`nV-subst₂`, `vlab-subst₂`, `dom-subst₂`, `cod-subst₂`,
-- plus `ein-subst₂`, `eout-subst₂`, `elab-subst₂` — not yet added).
-- Since subst₂ with the non-refl `++-identityʳ` doesn't reduce, each
-- field requires explicit cast bookkeeping via `subst-subst-sym` and
-- `splitAt-↑ˡ`.

postulate
  hTensor-G-hEmpty-iso-substed
    : ∀ {As Bs : List X} (G : Hypergraph FlatGen As Bs)
    → subst₂ (Hypergraph FlatGen)
             (++-identityʳ As) (++-identityʳ Bs)
             (hTensor G hEmpty)
    ≅ᴴ G

-- Specialization: for hId A, this gives `subst₂ _ p p (hId (A⊗unit)) ≅ᴴ hId A`
-- because `hId (A⊗unit) = hTensor (hId A) hEmpty`.
subst₂-hId-cancel
  : ∀ (A : ObjTerm)
  → subst₂ (Hypergraph FlatGen)
           (++-identityʳ (flatten A)) (++-identityʳ (flatten A))
           (hId (A ⊗₀ unit))
  ≅ᴴ hId A
subst₂-hId-cancel A = hTensor-G-hEmpty-iso-substed (hId A)

--------------------------------------------------------------------------------
-- ρ⇒∘ρ⇐≈id: "asymmetric" direction. Chain via hComposeP-subst-both
-- to reduce to `subst₂ _ eq eq (hComposeP (hId _) (hId _))`, then
-- subst₂-resp-≅ᴴ + idˡ-sound + subst₂-hId-cancel.

ρ⇒∘ρ⇐-sound : ∀ {A} → ⟪ ρ⇒ {A} ∘ ρ⇐ {A} ⟫ ≅ᴴ ⟪ id {A} ⟫
ρ⇒∘ρ⇐-sound {A} =
  subst (_≅ᴴ hId A) (sym full-eq)
    (trans-≅ᴴ (subst₂-resp-≅ᴴ eq eq (idˡ-sound (id {A ⊗₀ unit})))
              (subst₂-hId-cancel A))
  where
    eq = ++-identityʳ (flatten A)
    abstract
      arg1 : ⟪ ρ⇐ {A} ⟫ ≡ subst₂ (Hypergraph FlatGen) eq refl (hId (A ⊗₀ unit))
      arg1 = refl
      arg2 : ⟪ ρ⇒ {A} ⟫ ≡ subst₂ (Hypergraph FlatGen) refl eq (hId (A ⊗₀ unit))
      arg2 = refl
    full-eq : ⟪ ρ⇒ {A} ∘ ρ⇐ {A} ⟫
            ≡ subst₂ (Hypergraph FlatGen) eq eq
                     (hComposeP (hId (A ⊗₀ unit)) (hId (A ⊗₀ unit)))
    full-eq = trans (cong₂ hComposeP arg1 arg2)
                    (hComposeP-subst-both eq refl eq
                                          (hId (A ⊗₀ unit)) (hId (A ⊗₀ unit)))

--------------------------------------------------------------------------------
-- α⇒∘α⇐≈id: analogous pattern with ++-assoc.  Needs a variant of the
-- "hId-cancel" iso: `subst₂ _ (++-assoc _) (++-assoc _) (hId ((A⊗B)⊗C))
-- ≅ᴴ hId (A⊗(B⊗C))`. This is a structural iso on hId that reassociates
-- the tensor structure — not derivable from `hTensor-G-hEmpty-iso-substed`
-- (which is about `++-identityʳ`, not `++-assoc`).  Postulated here as
-- a focused lemma; dispatching α⇒∘α⇐ uses it analogously to ρ⇒∘ρ⇐'s
-- use of `subst₂-hId-cancel`.
postulate
  subst₂-hId-assoc-cancel
    : ∀ (A B C : ObjTerm)
    → subst₂ (Hypergraph FlatGen)
             (++-assoc (flatten A) (flatten B) (flatten C))
             (++-assoc (flatten A) (flatten B) (flatten C))
             (hId ((A ⊗₀ B) ⊗₀ C))
    ≅ᴴ hId (A ⊗₀ (B ⊗₀ C))

α⇒∘α⇐-sound : ∀ {A B C} → ⟪ α⇒ {A}{B}{C} ∘ α⇐ {A}{B}{C} ⟫ ≅ᴴ ⟪ id {A ⊗₀ (B ⊗₀ C)} ⟫
α⇒∘α⇐-sound {A} {B} {C} =
  subst (_≅ᴴ hId (A ⊗₀ (B ⊗₀ C))) (sym full-eq)
    (trans-≅ᴴ (subst₂-resp-≅ᴴ eq eq (idˡ-sound (id {(A ⊗₀ B) ⊗₀ C})))
              (subst₂-hId-assoc-cancel A B C))
  where
    eq = ++-assoc (flatten A) (flatten B) (flatten C)
    abstract
      arg1 : ⟪ α⇐ {A}{B}{C} ⟫
           ≡ subst₂ (Hypergraph FlatGen) eq refl (hId ((A ⊗₀ B) ⊗₀ C))
      arg1 = refl
      arg2 : ⟪ α⇒ {A}{B}{C} ⟫
           ≡ subst₂ (Hypergraph FlatGen) refl eq (hId ((A ⊗₀ B) ⊗₀ C))
      arg2 = refl
    full-eq : ⟪ α⇒ {A}{B}{C} ∘ α⇐ {A}{B}{C} ⟫
            ≡ subst₂ (Hypergraph FlatGen) eq eq
                     (hComposeP (hId ((A ⊗₀ B) ⊗₀ C))
                                (hId ((A ⊗₀ B) ⊗₀ C)))
    full-eq = trans (cong₂ hComposeP arg1 arg2)
                    (hComposeP-subst-both eq refl eq
                                          (hId ((A ⊗₀ B) ⊗₀ C))
                                          (hId ((A ⊗₀ B) ⊗₀ C)))

--------------------------------------------------------------------------------
-- Five remaining atomic axioms as flat postulates. Each has a dedicated
-- per-axiom proof plan in TODO.org (Refactor item 6b–6i).

-- triangle, α-comm, pentagon all live in their own modules
-- (`Triangle.agda`, `AlphaCommSound.agda`, `Pentagon.agda`) with at
-- least partial constructive proofs — they are NOT re-exported here.

postulate
  -- ρ⇒ ∘ f⊗id ≈ f ∘ ρ⇒  (unitorʳ-commute)
  ρ⇒∘f⊗id≈f∘ρ⇒-sound
    : ∀ {A B} {f : HomTerm A B}
    → ⟪ ρ⇒ {B} ∘ f ⊗₁ id {unit} ⟫ ≅ᴴ ⟪ f ∘ ρ⇒ {A} ⟫

  -- NOTE: `triangle-sound`, `α-comm-sound`, `pentagon-sound`, and
  -- `σ∘[f⊗g]≈[g⊗f]∘σ-sound` all live in their own modules:
  --   * `Categories.APROP.Hypergraph.Triangle`       (constructive)
  --   * `Categories.APROP.Hypergraph.AlphaCommSound` (constructive)
  --   * `Categories.APROP.Hypergraph.Pentagon`       (focused postulate
  --                                                   + building blocks)
  --   * `Categories.APROP.Hypergraph.SigmaNat`       (constructive —
  --                                                   5 structural-field
  --                                                   postulates inside)
  -- Soundness.agda imports them from there directly, so no postulates
  -- are needed in this module.

  -- hexagon: id⊗σ ∘ α⇒ ∘ σ⊗id ≈ α⇒ ∘ σ ∘ α⇒ (symmetric hexagon)
  hexagon-sound
    : ∀ {A B C}
    → ⟪ id {B} ⊗₁ σ {A} {C} ∘ α⇒ {B} {A} {C} ∘ σ {A} {B} ⊗₁ id {C} ⟫
    ≅ᴴ ⟪ α⇒ {B} {C} {A} ∘ σ {A} {B ⊗₀ C} ∘ α⇒ {A} {B} {C} ⟫

  -- assoc: (h∘g)∘f ≈ h∘(g∘f)  (composition associativity)
  assoc-sound
    : ∀ {A B C D} {f : HomTerm A B} {g : HomTerm B C} {h : HomTerm C D}
    → ⟪ (h ∘ g) ∘ f ⟫ ≅ᴴ ⟪ h ∘ (g ∘ f) ⟫

  -- ⊗-∘-dist: (g∘f)⊗(g'∘f') ≈ (g⊗g')∘(f⊗f')  (tensor/compose interchange)
  ⊗-∘-dist-sound
    : ∀ {A B C A' B' C'}
        {f : HomTerm A B} {g : HomTerm B C}
        {f' : HomTerm A' B'} {g' : HomTerm B' C'}
    → ⟪ (g ∘ f) ⊗₁ (g' ∘ f') ⟫ ≅ᴴ ⟪ (g ⊗₁ g') ∘ (f ⊗₁ f') ⟫
