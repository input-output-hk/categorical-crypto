-- Wiring for §(II) of the soundness proof
-- (docs/soundness-proof.typ).  Connects the order-theory modules
--
--   * `Discharge.EdgeDependency`   (Lemma A: iso ⇒ dependency-order iso),
--   * `Combinatorics.LinearExtension` (connectivity of linear extensions),
--
-- into iso-invariance of the CONCRETE order-indexed decoder `decodeOrd`.
-- Defines `Order`/`Valid`/`decodeOrd` (per-hypergraph) and the cross-iso
-- boundary identifications + ψ-pullback order `τ` and its no-inversion
-- transport `NoInv-τ` (Lemma 4).  The analytic steps (`swap-≈`,
-- `order-invariant`, `iso-transport`) live downstream in
-- `IsoInvarianceConcrete` / `SwapStep` / `IsoTransport`.
{-# OPTIONS --safe --without-K #-}

open import Categories.APROP

module Categories.APROP.Hypergraph.Soundness.Discharge.IsoInvarianceWiring
  (sig : APROPSignature) where

open APROP sig

open import Categories.APROP.Hypergraph.Model.Core using (Hypergraph; domL; codL)
open import Categories.APROP.Hypergraph.Model.Iso using (_≅ᴴ_)
open import Categories.APROP.Hypergraph.Model.FromAPROP sig using (FlatGen; range)
open import Categories.APROP.Hypergraph.Soundness.Base.Unflatten sig using (unflatten)
open import Categories.APROP.Hypergraph.Soundness.Decode.Decode sig
  using (process-edges)
open import Categories.APROP.Hypergraph.Soundness.Base.Permute sig
  using (permute-via-vlab)
open import Categories.APROP.Hypergraph.Soundness.Discharge.EdgeDependency
  using (Dep; ≺⇒ψ≺)
import Data.List.Relation.Unary.AllPairs as AP
open import Data.List.Relation.Unary.AllPairs using (AllPairs)
import Data.List.Relation.Unary.AllPairs.Properties as APProp
open import Categories.APROP.Hypergraph.Soundness.Linearity.LinearityIso sig
  using (bij-fin-ℕ-≡; tabulate-bij-↭-via-eq)

import Categories.Combinatorics.LinearExtension as LinExt

open import Data.Fin using (Fin)
import Data.Fin as Fin
open import Data.Nat using (ℕ)
import Data.Nat as Nat
open import Data.List using (List; _∷_; map; tabulate)
open import Data.List.Properties using (map-∘; map-cong; map-tabulate)
import Data.List.Relation.Binary.Permutation.Propositional as Perm
open import Data.Product using (proj₁; proj₂)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; sym; trans; subst; subst₂)

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
-- Per-hypergraph: order-indexed decoder and order-invariance.
------------------------------------------------------------------------

module PerHG (H : Hypergraph FlatGen) where
  private module H = Hypergraph H

  -- The order theory at the *immediate* dependency relation.  The
  -- predicates (`NoInv`/`_↝_`/`_↝*_`) need no hypotheses on `Dep H`;
  -- `connectivity` takes its irreflexivity witness (acyclicity, FALSE
  -- for an arbitrary `H`) as an explicit argument, supplied at
  -- `H = ⟪f⟫`/`⟪g⟫` via the proven `DepIrrefl.dep-irrefl-⟪⟫`.
  module L = LinExt (Fin H.nE) (Dep H)
  open L public using (NoInv; _↝_; _↝*_; connectivity)

  Order : Set
  Order = List (Fin H.nE)

  -- Validity of an order: running the cospan algorithm in this order from
  -- `H.dom` leaves a final stack that is a permutation of `H.cod` (so the
  -- final permute to `cod` exists).  This is the witness that makes the
  -- decoder TOTAL at the fixed codomain `unflatten (codL H)`.
  Valid : Order → Set
  Valid o = proj₁ (process-edges H o H.dom) Perm.↭ H.cod

  -- The CONCRETE order-indexed decoder: the body of `decode-attempt` run
  -- with `process-edges o` in place of `process-all-edges`, followed by the
  -- final `permute-via-vlab` justified by `p`.  (`domL H = map vlab dom`,
  -- `codL H = map vlab cod` definitionally, so the boundary type lines up.)
  decodeOrd : (o : Order) → Valid o
            → HomTerm (unflatten (domL H)) (unflatten (codL H))
  decodeOrd o p = permute-via-vlab H.vlab p ∘ proj₂ (process-edges H o H.dom)

------------------------------------------------------------------------
-- Across an isomorphism: iso-invariance of the decoder.
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
  domL-iso =
    trans (cong (map J.vlab) φ-dom)
          (trans (sym (map-∘ H.dom))
                 (map-cong φ-lab H.dom))

  codL-iso : codL J ≡ codL H
  codL-iso =
    trans (cong (map J.vlab) φ-cod)
          (trans (sym (map-∘ H.cod))
                 (map-cong φ-lab H.cod))

  -- The ψ-pullback of J's natural order onto H's edges.  `≺⇒ψ≺ Φ`
  -- makes it a linear extension of `Dep H`.
  τ : List (Fin H.nE)
  τ = map ψ⁻¹ (range J.nE)

  -- `τ ↭ range H.nE`, via the Fin-bijection permutation lemma
  -- `tabulate-bij-↭-via-eq`, bridged from `range` to `tabulate id`.
  τ↭range : τ Perm.↭ range H.nE
  τ↭range = subst (λ xs → xs Perm.↭ range H.nE) bridge step
    where
      nE-eq : H.nE ≡ J.nE
      nE-eq = bij-fin-ℕ-≡ ψ ψ⁻¹ ψ-left ψ-rght

      base : tabulate {n = J.nE} (λ i → ψ⁻¹ i) Perm.↭ tabulate {n = H.nE} (λ i → i)
      base = tabulate-bij-↭-via-eq (sym nE-eq) (λ i → i) ψ⁻¹ ψ ψ-rght ψ-left

      base-range : tabulate {n = J.nE} (λ i → ψ⁻¹ i) Perm.↭ range H.nE
      base-range =
        subst (λ xs → tabulate {n = J.nE} (λ i → ψ⁻¹ i) Perm.↭ xs)
              (sym (range≡tabulate-id H.nE)) base

      -- tabulate ψ⁻¹ ≡ map ψ⁻¹ (range J.nE) = τ
      bridge : tabulate {n = J.nE} (λ i → ψ⁻¹ i) ≡ map ψ⁻¹ (range J.nE)
      bridge = tabulate-as-map-range ψ⁻¹

      step : tabulate {n = J.nE} (λ i → ψ⁻¹ i) Perm.↭ range H.nE
      step = base-range

  ------------------------------------------------------------------------
  -- LEMMA 4.  `NoInv-τ`: transport J's no-inversion across the edge
  -- bijection `ψ⁻¹` onto the pullback order `τ`.
  --   * `AllPairs.map`             — `AllPairs Below_J (range J)` into
  --                                  `AllPairs (Below_H on ψ⁻¹) (range J)`;
  --   * `AllPairs.Properties.map⁺` — push `on ψ⁻¹` through `map ψ⁻¹`.
  ------------------------------------------------------------------------

  -- Dependency reflection along ψ⁻¹: `ψ⁻¹ b ≺ ψ⁻¹ a` in H ⇒ `b ≺ a` in J.
  dep-reflect : ∀ {a b} → Dep H (ψ⁻¹ b) (ψ⁻¹ a) → Dep J b a
  dep-reflect {a} {b} d = subst₂ (Dep J) (ψ-rght b) (ψ-rght a) (≺⇒ψ≺ Φ d)

  -- Pointwise: J's `Below` implies H's `Below` pulled back along ψ⁻¹.
  below-pull : ∀ {a b} → (¬ Dep J b a) → ¬ Dep H (ψ⁻¹ b) (ψ⁻¹ a)
  below-pull ndJ dH = ndJ (dep-reflect dH)

  -- The `map`-of-relation step (over the FIXED list `range J.nE`).
  step-on : AllPairs (λ a b → ¬ Dep J b a) (range J.nE)
          → AllPairs (λ a b → ¬ Dep H (ψ⁻¹ b) (ψ⁻¹ a)) (range J.nE)
  step-on = AP.map below-pull

  -- The `map ψ⁻¹` step (`AllPairs.Properties.map⁺` at `f = ψ⁻¹`;
  -- `(Below_H on ψ⁻¹) a b = ¬ Dep H (ψ⁻¹ b) (ψ⁻¹ a)` definitionally).
  NoInv-τ : PerHG.NoInv J (range J.nE) → PerHG.NoInv H τ
  NoInv-τ noJ = APProp.map⁺ (step-on noJ)
