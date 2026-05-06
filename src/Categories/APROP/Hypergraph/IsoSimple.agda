{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- A simplified variant of `_≅ᴴ_` that drops `atom-ein`, `atom-eout`.
--
-- `atom-ein`/`atom-eout` in `_≅ᴴ_` are derivable from `ψ-ein`/`ψ-eout` plus
-- `φ-lab` — they simply lift the endpoint equality up through `map vlab`.
-- Removing them cuts 2 fields + their routine derivations from every iso
-- construction.
--
-- Tradeoff: the `ψ-elab` field in the simplified record uses SPECIFIC
-- derived proof terms for the subst₂ arguments. For axioms where the
-- internal elab-c's subst₂ uses DIFFERENT proof terms (e.g., `map-via-inj`
-- directly), the full `_≅ᴴ_` is preferable — you can choose atom-ein to
-- match and get `ψ-elab = refl`. For axioms where the derived form
-- naturally matches, the simplified record saves ~10 lines.
--
-- USAGE: construct `_≅ᴴˢ_`, then `to-≅ᴴ : _≅ᴴˢ_ → _≅ᴴ_` fills in the
-- derivations.
--------------------------------------------------------------------------------

module Categories.APROP.Hypergraph.IsoSimple where

open import Categories.APROP.Hypergraph.Core
open import Categories.APROP.Hypergraph.Iso

open import Data.Fin using (Fin)
open import Data.List using (List; map)
open import Data.List.Properties using (map-∘; map-cong)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; sym; trans; subst₂)

--------------------------------------------------------------------------------
-- Canonical derivations of atom-ein / atom-eout from ψ-ein / ψ-eout + φ-lab.

module _ {X : Set} {Gen : List X → List X → Set}
         (G K : Hypergraph Gen) where
  private
    module G = Hypergraph G
    module K = Hypergraph K

  derived-atom-ein
    : (φ : Fin G.nV → Fin K.nV)
      (ψ : Fin G.nE → Fin K.nE)
      (φ-lab : ∀ i → K.vlab (φ i) ≡ G.vlab i)
      (ψ-ein : ∀ e → K.ein (ψ e) ≡ map φ (G.ein e))
    → ∀ e → map K.vlab (K.ein (ψ e)) ≡ map G.vlab (G.ein e)
  derived-atom-ein φ ψ φ-lab ψ-ein e =
    trans (cong (map K.vlab) (ψ-ein e))
    (trans (sym (map-∘ (G.ein e)))
           (map-cong φ-lab (G.ein e)))

  derived-atom-eout
    : (φ : Fin G.nV → Fin K.nV)
      (ψ : Fin G.nE → Fin K.nE)
      (φ-lab : ∀ i → K.vlab (φ i) ≡ G.vlab i)
      (ψ-eout : ∀ e → K.eout (ψ e) ≡ map φ (G.eout e))
    → ∀ e → map K.vlab (K.eout (ψ e)) ≡ map G.vlab (G.eout e)
  derived-atom-eout φ ψ φ-lab ψ-eout e =
    trans (cong (map K.vlab) (ψ-eout e))
    (trans (sym (map-∘ (G.eout e)))
           (map-cong φ-lab (G.eout e)))

--------------------------------------------------------------------------------
-- Simplified iso record: 14 fields instead of 16.

module _ {X : Set} {Gen : List X → List X → Set} where

  record _≅ᴴˢ_ (G K : Hypergraph Gen) : Set where
    private
      module G = Hypergraph G
      module K = Hypergraph K
    field
      -- Vertex bijection.
      φ      : Fin G.nV → Fin K.nV
      φ⁻¹    : Fin K.nV → Fin G.nV
      φ-left : ∀ i → φ⁻¹ (φ i) ≡ i
      φ-rght : ∀ i → φ (φ⁻¹ i) ≡ i

      -- Edge bijection.
      ψ      : Fin G.nE → Fin K.nE
      ψ⁻¹    : Fin K.nE → Fin G.nE
      ψ-left : ∀ e → ψ⁻¹ (ψ e) ≡ e
      ψ-rght : ∀ e → ψ (ψ⁻¹ e) ≡ e

      -- Labels, endpoints, boundary.
      φ-lab  : ∀ i → K.vlab (φ i) ≡ G.vlab i
      ψ-ein  : ∀ e → K.ein  (ψ e) ≡ map φ (G.ein e)
      ψ-eout : ∀ e → K.eout (ψ e) ≡ map φ (G.eout e)
      φ-dom  : K.dom ≡ map φ G.dom
      φ-cod  : K.cod ≡ map φ G.cod

      -- Elab preservation, using the derived atom-ein/atom-eout.
      -- This is the ONLY "hard" field — the rest are routine.
      ψ-elab : ∀ e → subst₂ Gen
                       (derived-atom-ein  G K φ ψ φ-lab ψ-ein  e)
                       (derived-atom-eout G K φ ψ φ-lab ψ-eout e)
                       (K.elab (ψ e))
                   ≡ G.elab e

  -- Convert simplified to full ≅ᴴ.
  to-≅ᴴ : ∀ {G K : Hypergraph Gen} → G ≅ᴴˢ K → G ≅ᴴ K
  to-≅ᴴ {G} {K} s = record
    { φ         = φ
    ; φ⁻¹       = φ⁻¹
    ; φ-left    = φ-left
    ; φ-rght    = φ-rght
    ; ψ         = ψ
    ; ψ⁻¹       = ψ⁻¹
    ; ψ-left    = ψ-left
    ; ψ-rght    = ψ-rght
    ; φ-lab     = φ-lab
    ; ψ-ein     = ψ-ein
    ; ψ-eout    = ψ-eout
    ; φ-dom     = φ-dom
    ; φ-cod     = φ-cod
    ; atom-ein  = derived-atom-ein  G K φ ψ φ-lab ψ-ein
    ; atom-eout = derived-atom-eout G K φ ψ φ-lab ψ-eout
    ; ψ-elab    = ψ-elab
    }
    where
      open _≅ᴴˢ_ s
