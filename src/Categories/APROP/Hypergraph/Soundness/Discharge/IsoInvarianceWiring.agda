-- See docs/soundness-proof.typ, "Iso-invariance, part (II)".
{-# OPTIONS --safe --without-K #-}

open import Categories.APROP.Internal.Prelude

module Categories.APROP.Hypergraph.Soundness.Discharge.IsoInvarianceWiring
  (sig : APROPSignature) where

open APROP sig

open import Categories.APROP.Hypergraph.Model.Core using (Hypergraph; domL; codL)
open import Categories.APROP.Hypergraph.Model.FromAPROP sig using (FlatGen)
open import Categories.APROP.Hypergraph.Model.Iso using (_≅ᴴ_)
open import Categories.APROP.Hypergraph.Soundness.Decode.Decode sig
  using (process-edges)
open import Categories.APROP.Hypergraph.Model.Dependency
  using (Dep; ≺⇒ψ≺)
import Categories.Combinatorics.LinearExtension as LinExt

open import Categories.Combinatorics.TabulateBij
  using (tabulate-bij-↭-via-eq)

open import Data.Fin as Fin using (Fin)
open import Data.List.Properties
open import Data.List.Properties.Ext
import Data.List.Relation.Unary.AllPairs as AP
import Data.List.Relation.Unary.AllPairs.Properties as APProp
open import Data.Nat as Nat using (ℕ)
open import Relation.Nullary

------------------------------------------------------------------------
-- Hypergraph orders
------------------------------------------------------------------------

module PerHG (H : Hypergraph FlatGen) where
  private module H = Hypergraph H

  -- Connectivity needs irreflexivity, false for arbitrary H;
  -- FinOrderNoInv.dep-irrefl-⟪⟫ supplies it for translated terms.
  module L = LinExt (Fin H.nE) (Dep H)
  open L public using (NoInv; _↝_; _↝*_; connectivity; swap-step; Incomp)

  Order : Set
  Order = List (Fin H.nE)

  Valid : Order → Set
  Valid o = process-edges H o H.dom Perm.↭ H.cod

------------------------------------------------------------------------
-- Isomorphism transport
------------------------------------------------------------------------

module _ {H J : Hypergraph FlatGen} (Φ : H ≅ᴴ J) where
  private
    module H  = Hypergraph H
    module J  = Hypergraph J
  open _≅ᴴ_ Φ
    using (ψ; ψ⁻¹; ψ-left; ψ-rght
          ; φ-lab; φ-dom; φ-cod)

  domL-iso : domL J ≡ domL H
  domL-iso = trans (cong (map J.vlab) φ-dom) (map-∘-cong φ-lab H.dom)

  codL-iso : codL J ≡ codL H
  codL-iso = trans (cong (map J.vlab) φ-cod) (map-∘-cong φ-lab H.cod)

  τ : List (Fin H.nE)
  τ = map ψ⁻¹ (allFin J.nE)

  τ↭allFin : τ Perm.↭ allFin H.nE
  τ↭allFin =
    subst (λ xs → xs Perm.↭ allFin H.nE)
          (sym (map-allFin ψ⁻¹))
          (tabulate-bij-↭-via-eq (λ i → i) ψ⁻¹ ψ ψ-rght ψ-left)

  below-pull : ∀ {a b} → (¬ Dep J b a) → ¬ Dep H (ψ⁻¹ b) (ψ⁻¹ a)
  below-pull {a} {b} ndJ dH =
    ndJ (subst₂ (Dep J) (ψ-rght b) (ψ-rght a) (≺⇒ψ≺ Φ dH))

  NoInv-τ : PerHG.NoInv J (allFin J.nE) → PerHG.NoInv H τ
  NoInv-τ noJ = APProp.map⁺ (AP.map below-pull noJ)
