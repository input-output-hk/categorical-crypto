{-# OPTIONS --without-K #-}

--------------------------------------------------------------------------------
-- Per-axiom soundness proofs. Extracted from the Soundness catch-all
-- postulate as each axiom is discharged.
--
-- With the switch to hComposeP (pruned cospan composition), axioms where
-- LHS had strictly more vertices than RHS under the unpruned version now
-- have matching vertex counts (modulo +-identityʳ casts) and are
-- constructively provable.
--
-- Currently proved: ∅ (this file is a placeholder for now).
--
-- Strategy per axiom:
--   1. Identify LHS and RHS of the `⟪_⟫` translation.
--   2. Use `hId-count-non-dom ≡ 0` (or `⟪_⟫-dom-unique` for the count-non
--      of general ⟪f⟫.dom) to show the vertex counts match.
--   3. Construct the ≅ᴴ record field-by-field:
--      φ/φ⁻¹ via splitAt + case on the trivially-empty side.
--      ψ/ψ⁻¹ similarly (hId has no edges).
--      Labels, endpoints, elab: chase through the subst₂ + map-via-remapP
--      machinery.
--------------------------------------------------------------------------------

open import Categories.APROP

module Categories.APROP.Hypergraph.SoundnessAxioms (sig : APROPSignature) where

open APROP sig
open import Categories.APROP.Hypergraph.Core
open import Categories.APROP.Hypergraph.FromAPROP sig
  using (FlatGen; flatten; hId; hTensor; hGen; hEmpty; hVar; hSwap)
open import Categories.APROP.Hypergraph.Translation sig
open import Categories.APROP.Hypergraph.Iso
open import Categories.APROP.Hypergraph.PrunedCompose sig
open import Categories.APROP.Hypergraph.Invariant sig

open import Categories.APROP.Hypergraph.Prune
  using (nonMem; count-non; AllIn; AllIn→count-non-zero)

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin using (Fin; zero; suc; inject+; raise; splitAt)
open import Data.Fin.Properties using (splitAt-inject+; splitAt-raise)
open import Data.List using (List; []; _∷_; map; length)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Nat.Properties using (+-identityʳ)
open import Data.Sum using ([_,_]′; inj₁; inj₂)
open import Function using (id)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; sym; trans; subst; subst₂)

--------------------------------------------------------------------------------
-- `idˡ`: `id ∘ f ≈Term f`.
--
-- Translation:
--   ⟪ id ∘ f ⟫ = hComposeP ⟪f⟫ (hId B)
-- where B is the codomain of f.
--
-- Key facts used:
--   * `hId B` has no edges (hId-nE ≡ 0 by induction on B).
--   * `hId B`.dom covers all vertices (hId-dom-covers).
--   * Therefore `count-non (hId B).dom ≡ 0` (hId-count-non-dom).
--
-- Consequence: the composite's vertex count is `⟪f⟫.nV + 0` and the
-- edge count is `⟪f⟫.nE + 0`. The iso with `⟪f⟫` is essentially
-- identity on the G-side with trivial coverage of the empty K-side.

-- First, a helper fact: hId has no edges.
hId-nE : ∀ A → Hypergraph.nE (hId A) ≡ 0
hId-nE unit       = refl
hId-nE (Var x)    = refl
hId-nE (A ⊗₀ B)   = cong₂-+ (hId-nE A) (hId-nE B)
  where
    cong₂-+ : ∀ {a b c d : ℕ} → a ≡ b → c ≡ d → a + c ≡ b + d
    cong₂-+ refl refl = refl

-- Fin-zero absurdity: if n ≡ 0 then Fin n is empty.
private
  Fin-zero-absurd : ∀ {n : ℕ} → n ≡ 0 → Fin n → ⊥
  Fin-zero-absurd refl ()

--------------------------------------------------------------------------------
-- idˡ : `id ∘ f ≈Term f`. Proof skeleton.
--
-- The proof's vertex bijection is direct: `hComposeP ⟪f⟫ (hId B)` has
-- nV = ⟪f⟫.nV + count-non (hId B).dom, which reduces to ⟪f⟫.nV + 0 by
-- `hId-count-non-dom`. φ maps any vertex by splitAt, with the K-side
-- being impossible (Fin 0) via `Fin-zero-absurd`.
--
-- The edge bijection is similar: (hId B).nE ≡ 0 by `hId-nE`.
--
-- Label, boundary, and elab preservation follow from the pruned
-- composite's structure when K has no edges and K.dom covers everything.

-- Scaffolding for the full proof:
module idˡ-proof {A B : ObjTerm} (f : HomTerm A B) where
  private
    G = ⟪ f ⟫
    K = hId B
    C = hComposeP G K
    module G = Hypergraph G
    module K = Hypergraph K
    module C = Hypergraph C

    -- Key facts.
    cn≡0 : count-non K.dom ≡ 0
    cn≡0 = hId-count-non-dom B

    nE≡0 : K.nE ≡ 0
    nE≡0 = hId-nE B

  φ : Fin C.nV → Fin G.nV
  φ v with splitAt G.nV v
  ... | inj₁ i = i
  ... | inj₂ j = ⊥-elim (Fin-zero-absurd cn≡0 j)

  φ⁻¹ : Fin G.nV → Fin C.nV
  φ⁻¹ i = inject+ (count-non K.dom) i

  ψ : Fin C.nE → Fin G.nE
  ψ e with splitAt G.nE e
  ... | inj₁ eG = eG
  ... | inj₂ eK = ⊥-elim (Fin-zero-absurd nE≡0 eK)

  ψ⁻¹ : Fin G.nE → Fin C.nE
  ψ⁻¹ e = inject+ K.nE e

  ------------------------------------------------------------------------------
  -- Bijection laws.

  open import Data.Fin.Properties using (splitAt⁻¹-↑ˡ; splitAt⁻¹-↑ʳ)

  φ-left : ∀ v → φ⁻¹ (φ v) ≡ v
  φ-left v with splitAt G.nV v in eq
  ... | inj₁ i = splitAt⁻¹-↑ˡ eq
  ... | inj₂ j = ⊥-elim (Fin-zero-absurd cn≡0 j)

  φ-rght : ∀ i → φ (φ⁻¹ i) ≡ i
  φ-rght i rewrite splitAt-inject+ G.nV (count-non K.dom) i = refl

  ψ-left : ∀ e → ψ⁻¹ (ψ e) ≡ e
  ψ-left e with splitAt G.nE e in eq
  ... | inj₁ eG = splitAt⁻¹-↑ˡ eq
  ... | inj₂ eK = ⊥-elim (Fin-zero-absurd nE≡0 eK)

  ψ-rght : ∀ e → ψ (ψ⁻¹ e) ≡ e
  ψ-rght e rewrite splitAt-inject+ G.nE K.nE e = refl

  ------------------------------------------------------------------------------
  -- Label preservation.
  --
  -- G.vlab (φ v) ≡ C.vlab v. On the inj₁ side, both reduce to G.vlab i.
  -- The inj₂ side is absurd.

  φ-lab : ∀ v → G.vlab (φ v) ≡ C.vlab v
  φ-lab v with splitAt G.nV v
  ... | inj₁ i = refl
  ... | inj₂ j = ⊥-elim (Fin-zero-absurd cn≡0 j)
