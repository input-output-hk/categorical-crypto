{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- Higher-level hypergraph peel helpers.
--
-- Packages up the common "given `T ≡ <subst-wrapped hComposeP … hId>`,
-- derive `T ≅ᴴ <same subst> G`" step that recurs across the coherence
-- soundness proofs (α-comm, triangle, pentagon, hexagon, ρ/σ-nat).
--
-- Depends on `hCompose-hId-{R,L}-iso-generic` from the `--safe` module
-- `SoundnessProved`, so this module is also `--safe`.  Pure subst₂/cong
-- bookkeeping (no dependence on the constructive peel proofs) lives in
-- `Categories.APROP.Hypergraph.CoherenceHelpers`.
--
-- Contents:
--   * `hCompose-hId-R-iso-substed` : one-step `subst₂`-wrapped right-peel.
--   * `reduce-via-hId-R`           : packaged form — takes a
--     propositional factorisation proof and returns a `≅ᴴ`.
--   * `reduce-via-hId-L`           : left dual (no outer subst₂;
--     needs `Unique` of `G.dom`).
--------------------------------------------------------------------------------

open import Categories.APROP

module Categories.APROP.Hypergraph.CoherenceReductions (sig : APROPSignature) where

open APROP sig
open import Categories.APROP.Hypergraph.Core
open import Categories.APROP.Hypergraph.FromAPROP sig
  using (FlatGen; flatten; hId)
open import Categories.APROP.Hypergraph.PrunedCompose sig
  using (hComposeP)
open import Categories.APROP.Hypergraph.Iso
  using (_≅ᴴ_; subst₂-resp-≅ᴴ)
open import Categories.APROP.Hypergraph.SoundnessProved sig
  using (hCompose-hId-R-iso-generic; hCompose-hId-L-iso-generic)

open import Data.List using (List)
open import Data.List.Relation.Unary.Unique.Propositional using (Unique)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; subst; subst₂)

--------------------------------------------------------------------------------
-- Right-side peel.

-- Peel a right `hId` through an outer `subst₂ _ refl eq`.  Pure
-- composition of `subst₂-resp-≅ᴴ` and `hCompose-hId-R-iso-generic`;
-- saves two layers of wrapping at the call site.
hCompose-hId-R-iso-substed
  : ∀ {As : List X} (A : ObjTerm)
      (G : Hypergraph FlatGen As (flatten A))
      {Bs' : List X} (eq : flatten A ≡ Bs')
  → subst₂ (Hypergraph FlatGen) refl eq (hComposeP G (hId A))
    ≅ᴴ subst₂ (Hypergraph FlatGen) refl eq G
hCompose-hId-R-iso-substed A G eq =
  subst₂-resp-≅ᴴ refl eq (hCompose-hId-R-iso-generic A G)

-- Packaged peel-and-commit: given `T ≡ subst₂ _ refl eq (hComposeP G (hId A))`,
-- derive `T ≅ᴴ subst₂ _ refl eq G`.  This is the pattern used by
-- `α-comm-sound`'s LHS and by `ρ⇒∘f⊗id≈f∘ρ⇒-sound`'s LHS.
reduce-via-hId-R
  : ∀ {As : List X} (A : ObjTerm)
      (G : Hypergraph FlatGen As (flatten A))
      {Bs' : List X} (eq : flatten A ≡ Bs')
      {T : Hypergraph FlatGen As Bs'}
  → T ≡ subst₂ (Hypergraph FlatGen) refl eq (hComposeP G (hId A))
  → T ≅ᴴ subst₂ (Hypergraph FlatGen) refl eq G
reduce-via-hId-R A G eq eq-proof =
  subst (_≅ᴴ _) (sym eq-proof) (hCompose-hId-R-iso-substed A G eq)

--------------------------------------------------------------------------------
-- Left-side peel.  No outer subst₂ (the dom side is typically already
-- canonical in the proofs that use this), but needs `Unique (G.dom)`.

-- Packaged form: given `T ≡ hComposeP (hId A) G` and `Unique (G.dom)`,
-- derive `T ≅ᴴ G`.  Used by `α-comm-sound`'s RHS.
reduce-via-hId-L
  : ∀ {Bs : List X} (A : ObjTerm)
      (G : Hypergraph FlatGen (flatten A) Bs)
  → Unique (Hypergraph.dom G)
  → {T : Hypergraph FlatGen (flatten A) Bs}
  → T ≡ hComposeP (hId A) G
  → T ≅ᴴ G
reduce-via-hId-L A G u eq-proof =
  subst (_≅ᴴ _) (sym eq-proof) (hCompose-hId-L-iso-generic A G u)
