-- Wiring for §(II) of the soundness proof
-- (docs/soundness-proof.typ).  Connects the order-theory modules
--
--   * `Discharge.EdgeDependency`   (Lemma A: iso ⇒ dependency-order iso),
--   * `Combinatorics.LinearExtension` (connectivity of linear extensions),
--   * `Combinatorics.TabulateBij`  (the whole content of `τ↭range`),
--
-- into the cross-iso boundary identifications and the ψ-pullback order.
-- Defines `Order`/`Valid` (per-hypergraph) and, across an iso, `domL-iso`,
-- `codL-iso`, `τ` and its `NoInv-τ` transport (Lemma 4).  The analytic steps
-- live downstream, and only in their STRICT form — `SwapStep.swap-≈ˢ`,
-- `IsoTransport.order-invariantˢ`/`iso-transportˢ`; the unstarred names died
-- with the weak morphism apparatus.
{-# OPTIONS --safe --without-K #-}

open import Categories.APROP

module Categories.APROP.Hypergraph.Soundness.Discharge.IsoInvarianceWiring
  (sig : APROPSignature) where

open APROP sig

open import Categories.APROP.Hypergraph.Model.Core using (Hypergraph; domL; codL)
open import Categories.APROP.Hypergraph.Model.Iso using (_≅ᴴ_)
open import Categories.APROP.Hypergraph.Model.FromAPROP sig using (FlatGen; range)
open import Categories.APROP.Hypergraph.Soundness.Decode.Decode sig
  using (process-edges)
open import Categories.APROP.Hypergraph.Soundness.Discharge.EdgeDependency
  using (Dep; ≺⇒ψ≺)
import Data.List.Relation.Unary.AllPairs as AP
import Data.List.Relation.Unary.AllPairs.Properties as APProp
open import Categories.Combinatorics.TabulateBij
  using (tabulate-bij-↭-via-eq)

import Categories.Combinatorics.LinearExtension as LinExt

open import Data.Fin as Fin using (Fin)
open import Data.Nat as Nat using (ℕ)
open import Data.List.Properties using (map-tabulate)
open import Data.List.Properties.Ext using (map-∘-cong)
open import Relation.Nullary using (¬_)

------------------------------------------------------------------------
-- Small range/tabulate bridge lemmas (local copies; `range` is defined
-- by recursion in `FromAPROP` and `tabulate` is `Data.List.tabulate`).
------------------------------------------------------------------------

range≡tabulate-id : ∀ (n : ℕ) → range n ≡ tabulate {n = n} (λ i → i)
range≡tabulate-id Nat.zero    = refl
range≡tabulate-id (Nat.suc n) =
  cong (Fin.zero ∷_)
    (trans (cong (map Fin.suc) (range≡tabulate-id n))
           (map-tabulate (λ i → i) Fin.suc))

tabulate-as-map-range : ∀ {n} {A : Set} (f : Fin n → A) → tabulate f ≡ map f (range n)
tabulate-as-map-range {n = n} f =
  trans (sym (map-tabulate (λ i → i) f))
        (cong (map f) (sym (range≡tabulate-id n)))

------------------------------------------------------------------------
-- Per-hypergraph: the edge orders and their stack-level validity witness.
------------------------------------------------------------------------

module PerHG (H : Hypergraph FlatGen) where
  private module H = Hypergraph H

  -- The order theory at the *immediate* dependency relation.  The
  -- predicates (`NoInv`/`_↝_`/`_↝*_`) need no hypotheses on `Dep H`;
  -- `connectivity` takes its irreflexivity witness (acyclicity, FALSE
  -- for an arbitrary `H`) as an explicit argument, supplied at
  -- `H = ⟪f⟫`/`⟪g⟫` via the proven `FinOrderNoInv.dep-irrefl-⟪⟫`.
  module L = LinExt (Fin H.nE) (Dep H)
  -- The swap relation's constructor and its incomparability side condition
  -- are part of this interface: both downstream consumers pattern-match on
  -- `swap-step`, and `SwapValidity` states its hypotheses with `Incomp`.
  open L public using (NoInv; _↝_; _↝*_; connectivity; swap-step; Incomp)

  Order : Set
  Order = List (Fin H.nE)

  -- Validity of an order: running the cospan stack fold in this order from
  -- `H.dom` leaves a final stack that is a permutation of `H.cod`.  This is
  -- the totality witness at the fixed codomain.
  --
  -- NOTE (weak-decoder demotion, Review-2 F2): the CONCRETE order-indexed
  -- decoder `decodeOrd` (`permute-via-vlab H.vlab p` over `process-edges …`)
  -- had zero live consumers — downstream (`IsoTransport`, `SwapStep`,
  -- `PartII`) uses only `Order`/`Valid`
  -- and the strict twin `decodeOrdˢ`.  It has been deleted with the weak
  -- morphism apparatus; only this stack-level `Valid` witness survives.
  Valid : Order → Set
  Valid o = process-edges H o H.dom Perm.↭ H.cod

------------------------------------------------------------------------
-- Across an isomorphism: the boundary identifications and the ψ-pullback order.
------------------------------------------------------------------------

module _ {H J : Hypergraph FlatGen} (Φ : H ≅ᴴ J) where
  private
    module H  = Hypergraph H
    module J  = Hypergraph J
  open _≅ᴴ_ Φ
    using (ψ; ψ⁻¹; ψ-left; ψ-rght
          ; φ-lab; φ-dom; φ-cod)

  -- The iso identifies the boundaries (φ preserves vertex labels and the
  -- boundary lists).
  domL-iso : domL J ≡ domL H
  domL-iso = trans (cong (map J.vlab) φ-dom) (map-∘-cong φ-lab H.dom)

  codL-iso : codL J ≡ codL H
  codL-iso = trans (cong (map J.vlab) φ-cod) (map-∘-cong φ-lab H.cod)

  -- The ψ-pullback of J's natural order onto H's edges.  `≺⇒ψ≺ Φ`
  -- makes it a linear extension of `Dep H`.
  τ : List (Fin H.nE)
  τ = map ψ⁻¹ (range J.nE)

  -- `τ ↭ range H.nE`, via the Fin-bijection permutation lemma
  -- `tabulate-bij-↭-via-eq`, bridged from `range` to `tabulate id`.
  τ↭range : τ Perm.↭ range H.nE
  τ↭range = subst (λ xs → xs Perm.↭ range H.nE) bridge base-range
    where
      base : tabulate {n = J.nE} (λ i → ψ⁻¹ i) Perm.↭ tabulate {n = H.nE} (λ i → i)
      base = tabulate-bij-↭-via-eq (λ i → i) ψ⁻¹ ψ ψ-rght ψ-left

      base-range : tabulate {n = J.nE} (λ i → ψ⁻¹ i) Perm.↭ range H.nE
      base-range =
        subst (λ xs → tabulate {n = J.nE} (λ i → ψ⁻¹ i) Perm.↭ xs)
              (sym (range≡tabulate-id H.nE)) base

      -- tabulate ψ⁻¹ ≡ map ψ⁻¹ (range J.nE) = τ
      bridge : tabulate {n = J.nE} (λ i → ψ⁻¹ i) ≡ map ψ⁻¹ (range J.nE)
      bridge = tabulate-as-map-range ψ⁻¹

  ------------------------------------------------------------------------
  -- LEMMA 4.  `NoInv-τ`: transport J's no-inversion across the edge
  -- bijection `ψ⁻¹` onto the pullback order `τ`.
  --   * `AllPairs.map`             — `AllPairs Below_J (range J)` into
  --                                  `AllPairs (Below_H on ψ⁻¹) (range J)`;
  --   * `AllPairs.Properties.map⁺` — push `on ψ⁻¹` through `map ψ⁻¹`.
  ------------------------------------------------------------------------

  -- Pointwise: J's `Below` implies H's `Below` pulled back along ψ⁻¹ (the
  -- dependency `ψ⁻¹ b ≺ ψ⁻¹ a` in H reflects to `b ≺ a` in J along `≺⇒ψ≺`).
  below-pull : ∀ {a b} → (¬ Dep J b a) → ¬ Dep H (ψ⁻¹ b) (ψ⁻¹ a)
  below-pull {a} {b} ndJ dH =
    ndJ (subst₂ (Dep J) (ψ-rght b) (ψ-rght a) (≺⇒ψ≺ Φ dH))

  -- `AP.map below-pull` is the relation step over the FIXED list `range J.nE`;
  -- `AllPairs.Properties.map⁺` then pushes it through `map ψ⁻¹` (at `f = ψ⁻¹`,
  -- `(Below_H on ψ⁻¹) a b = ¬ Dep H (ψ⁻¹ b) (ψ⁻¹ a)` definitionally).
  NoInv-τ : PerHG.NoInv J (range J.nE) → PerHG.NoInv H τ
  NoInv-τ noJ = APProp.map⁺ (AP.map below-pull noJ)
