-- Wiring for §(II) of the completeness proof
-- (docs/completeness-proof.typ).  Connects the order-theory modules
--
--   * `Discharge.EdgeDependency`   (Lemma A: iso ⇒ dependency-order iso),
--   * `Combinatorics.LinearExtension` (connectivity of linear extensions),
--
-- into iso-invariance of the CONCRETE order-indexed decoder `decodeOrd`.
-- Defines `Order`/`Valid`/`decodeOrd` (per-hypergraph) and the cross-iso
-- boundary identifications + ψ-pullback order `τ`.  The analytic steps
-- (`swap-≈`, `order-invariant`, `iso-transport`, `NoInv-τ`) live downstream
-- in `IsoInvarianceConcrete` / `SwapStep` / `IsoTransport` / `WiringLemmas`.
{-# OPTIONS --safe --without-K #-}

open import Categories.APROP

module Categories.APROP.Hypergraph.Completeness.Discharge.IsoInvarianceWiring
  (sig : APROPSignature) where

open APROP sig

open import Categories.APROP.Hypergraph.Core
  using (Hypergraph; domL; codL)
open import Categories.APROP.Hypergraph.Iso using (_≅ᴴ_)
open import Categories.APROP.Hypergraph.FromAPROP sig using (FlatGen; range)
open import Categories.APROP.Hypergraph.Completeness.Unflatten sig using (unflatten)
open import Categories.APROP.Hypergraph.Completeness.Decode sig
  using (process-edges)
open import Categories.APROP.Hypergraph.Completeness.Permute sig
  using (permute-via-vlab)
open import Categories.APROP.Hypergraph.Completeness.Discharge.EdgeDependency
  using (Dep; ≺⇒ψ≺)
open import Categories.APROP.Hypergraph.Completeness.LinearityIso sig
  using (bij-fin-ℕ-≡; tabulate-bij-↭-via-eq)

import Categories.Combinatorics.LinearExtension as LinExt

open import Data.Fin using (Fin)
import Data.Fin as Fin
open import Data.Nat using (ℕ)
import Data.Nat as Nat
open import Data.List using (List; _∷_; map; tabulate)
open import Data.List.Properties using (map-∘; map-cong; map-tabulate)
import Data.List.Relation.Binary.Permutation.Propositional as Perm
open import Data.Product using (Σ; Σ-syntax; _,_; proj₁; proj₂)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; sym; trans; subst; subst₂)
open import Relation.Binary.Construct.Closure.ReflexiveTransitive
  using (Star; ε; _◅_)

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

tabulate-as-map-range
  : ∀ {n} {A : Set} (f : Fin n → A)
  → tabulate f ≡ map f (range n)
tabulate-as-map-range {n = n} f =
  trans (sym (map-tabulate (λ i → i) f))
        (cong (map f) (sym (range≡tabulate-id n)))

------------------------------------------------------------------------
-- Per-hypergraph: order-indexed decoder and order-invariance.
------------------------------------------------------------------------

module PerHG (H : Hypergraph FlatGen)
             (Dep-irrefl : ∀ {e} → ¬ (Dep H e e)) where
  private module H = Hypergraph H

  -- `Dep-irrefl` (acyclicity) is FALSE for an arbitrary `H`, so it is a
  -- MODULE PARAMETER, supplied at `H = ⟪f⟫`/`⟪g⟫` via the proven
  -- `DepIrrefl.dep-irrefl-⟪⟫`.

  -- The connectivity theorem at the *immediate* dependency relation (needs
  -- only irreflexivity).
  module L = LinExt (Fin H.nE) (Dep H) Dep-irrefl
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
  decodeOrd o p =
    permute-via-vlab H.vlab p ∘ proj₂ (process-edges H o H.dom)

------------------------------------------------------------------------
-- Across an isomorphism: iso-invariance of the decoder.
------------------------------------------------------------------------

module _ {H J : Hypergraph FlatGen} (Φ : H ≅ᴴ J) where
  private
    module H  = Hypergraph H
    module J  = Hypergraph J
  open _≅ᴴ_ Φ
    using (φ; φ⁻¹; ψ; ψ⁻¹; φ-left; φ-rght; ψ-left; ψ-rght
          ; φ-lab; φ-dom; φ-cod)

  -- Lemma A: ψ preserves the dependency relation (justifies `NoInv-τ`: a
  -- linear extension pulls back across the dependency-order iso).
  ψ-pres-dep : ∀ {e e'} → Dep H e e' → Dep J (ψ e) (ψ e')
  ψ-pres-dep = ≺⇒ψ≺ Φ

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

  -- The ψ-pullback of J's natural order onto H's edges.  `ψ-pres-dep`
  -- (Lemma A) makes it a linear extension of `Dep H`.
  τ : List (Fin H.nE)
  τ = map ψ⁻¹ (range J.nE)

  -- `τ ↭ range H.nE`, via the Fin-bijection permutation lemma
  -- `tabulate-bij-↭-via-eq`, bridged from `range` to `tabulate id`.
  τ↭range : τ Perm.↭ range H.nE
  τ↭range = subst (λ xs → xs Perm.↭ range H.nE) bridge step
    where
      nE-eq : H.nE ≡ J.nE
      nE-eq = bij-fin-ℕ-≡ ψ ψ⁻¹ ψ-left ψ-rght

      base : tabulate {n = J.nE} (λ i → ψ⁻¹ i)
               Perm.↭ tabulate {n = H.nE} (λ i → i)
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
