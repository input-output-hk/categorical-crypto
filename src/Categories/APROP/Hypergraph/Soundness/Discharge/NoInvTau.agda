-- The single wiring lemma LEMMA 4 (`NoInv-τ`) of the soundness program;
-- the other wiring lemmas are proven in their own `Discharge.*` modules.
-- `NoInv-τ` takes J's `NoInv` as an explicit hypothesis.
{-# OPTIONS --safe --without-K #-}

open import Categories.APROP

module Categories.APROP.Hypergraph.Soundness.Discharge.NoInvTau
  (sig : APROPSignature) where

open APROP sig

open import Categories.APROP.Hypergraph.Core using (Hypergraph; domL; codL)
open import Categories.APROP.Hypergraph.Iso using (_≅ᴴ_)
open import Categories.APROP.Hypergraph.FromAPROP sig using (FlatGen; range)
open import Categories.APROP.Hypergraph.Translation sig
  using (⟪_⟫; ⟪⟫-domL; ⟪⟫-codL)
open import Categories.APROP.Hypergraph.Soundness.Unflatten sig using (unflatten)
open import Categories.APROP.Hypergraph.Soundness.Decode sig using (process-edges)
open import Categories.APROP.Hypergraph.Soundness.Discharge.EdgeDependency
  using (Dep; ≺⇒ψ≺; ψ≺⇒≺)

import Categories.APROP.Hypergraph.Soundness.Discharge.IsoInvarianceWiring sig as IW
import Categories.APROP.Hypergraph.Soundness.Discharge.DepIrrefl sig as DI

open import Data.Fin using (Fin)
open import Data.Nat using (ℕ)
open import Data.List using (List; map)
open import Data.List.Relation.Unary.All as All using (All)
import Data.List.Relation.Unary.AllPairs as AP
open import Data.List.Relation.Unary.AllPairs using (AllPairs; []; _∷_)
open import Data.List.Relation.Unary.AllPairs.Properties as APProp using ()
open import Data.Product using (Σ; Σ-syntax; _,_; proj₁; proj₂)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; subst; subst₂)

------------------------------------------------------------------------
-- LEMMA 4.  NoInv-τ.  `τ = map ψ⁻¹ (range J.nE)`, `NoInv` is
-- `AllPairs (λ a b → ¬ Dep · b a)`.  Transport J's no-inversion across
-- the edge-bijection `ψ⁻¹`:
--   * `AllPairs.map`            — `AllPairs Below_J (range J)` into
--                                 `AllPairs (Below_H on ψ⁻¹) (range J)`;
--   * `AllPairs.Properties.map⁺` — push `on ψ⁻¹` through `map ψ⁻¹`.
------------------------------------------------------------------------

module Lemma4 {H J : Hypergraph FlatGen} (Φ : H ≅ᴴ J)
              (dihH : ∀ {e} → ¬ (Dep H e e))
              (dihJ : ∀ {e} → ¬ (Dep J e e)) where
  private
    module PH = IW.PerHG H dihH
    module PJ = IW.PerHG J dihJ
  open _≅ᴴ_ Φ using (ψ; ψ⁻¹; ψ-rght)

  -- Dependency reflection along ψ⁻¹: `ψ⁻¹ b ≺ ψ⁻¹ a` in H ⇒ `b ≺ a` in J.
  dep-reflect : ∀ {a b}
              → Dep H (ψ⁻¹ b) (ψ⁻¹ a)
              → Dep J b a
  dep-reflect {a} {b} d =
    subst₂ (Dep J) (ψ-rght b) (ψ-rght a) (≺⇒ψ≺ Φ d)

  -- Pointwise: J's `Below` implies H's `Below` pulled back along ψ⁻¹.
  below-pull : ∀ {a b}
             → (¬ Dep J b a)
             → ¬ Dep H (ψ⁻¹ b) (ψ⁻¹ a)
  below-pull ndJ dH = ndJ (dep-reflect dH)

  -- The `map`-of-relation step (over the FIXED list `range J.nE`).
  step-on : AllPairs (λ a b → ¬ Dep J b a) (range (Hypergraph.nE J))
          → AllPairs (λ a b → ¬ Dep H (ψ⁻¹ b) (ψ⁻¹ a)) (range (Hypergraph.nE J))
  step-on = AP.map below-pull

  -- The `map ψ⁻¹` step (`AllPairs.Properties.map⁺` at `f = ψ⁻¹`;
  -- `(Below_H on ψ⁻¹) a b = ¬ Dep H (ψ⁻¹ b) (ψ⁻¹ a)` definitionally).
  NoInv-τ : PJ.NoInv (range (Hypergraph.nE J))
          → PH.NoInv (map ψ⁻¹ (range (Hypergraph.nE J)))
  NoInv-τ noJ = APProp.map⁺ (step-on noJ)
