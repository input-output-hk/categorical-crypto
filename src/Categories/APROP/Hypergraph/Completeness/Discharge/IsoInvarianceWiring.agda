-- NOT `--safe`: this is the large-scale *wiring sketch* for §(II) of the
-- informal completeness proof (docs/completeness-proof.typ).  It connects
-- the two finished order-theory modules
--
--   * `Discharge.EdgeDependency`   (Lemma A: iso ⇒ dependency-order iso),
--   * `Combinatorics.LinearExtension` (connectivity of linear extensions),
--
-- into iso-invariance of the CONCRETE order-indexed decoder `decodeOrd`,
-- leaving the *analytic* steps as clearly-marked postulates:
--
--   (N+K)  `swap-≈`     — one adjacent-independent edge swap changes the
--                         decoding only up to ≈Term  (interchange axiom +
--                         permutation coherence);  THE analytic content.
--   (bk)   `swap-validity` — that an adjacent-independent swap preserves
--                         order-validity (the final live-wire multiset is
--                         order-independent);  TRUE, bookkeeping only.
--   (Lem0) `iso-transport` — vertex relabelling is free + ψ re-indexing;
--   (LemC) `fin-order-NoInv` — the Fin order is a linear extension
--                         (= `AllFire-natural-range`);
--   plus boundary/acyclicity bookkeeping (`Dep-irrefl`, `domL-iso`, …).
--
-- The decoder `decodeOrd o (p : Valid o)` is now CONCRETE: it is the body
-- of `decode-attempt` run with `process-edges o` in place of
-- `process-all-edges`, followed by the final `permute-via-vlab` justified
-- by the validity witness `p` (the old `decode-ord` postulate is GONE).
--
-- The CENTRAL step, `order-invariant`, is a *real* proof: it is driven by
-- `connectivity` and the validity-threaded closure-lift `↝*⇒≈`.
-- `ψ-pres-dep` is a real use of Lemma A.
{-# OPTIONS --without-K #-}

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

  -- Acyclicity: no edge depends on itself.  This is FALSE for an arbitrary
  -- `H` (a self-feeding edge), so it is taken as a MODULE PARAMETER and
  -- supplied at the use sites at `H = ⟪f⟫`/`⟪g⟫` via the proven
  -- `DepIrrefl.dep-irrefl-⟪⟫`.  (Previously a false postulate.)

  -- Instantiate the connectivity theorem at the *immediate* dependency
  -- relation (needs only irreflexivity — `LinearExtension` was generalised
  -- to drop the unused transitivity hypothesis).
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

  -- The CONCRETE order-indexed decoder.  This is exactly the body of
  -- `decode-attempt` run with `process-edges o` in place of
  -- `process-all-edges = process-edges (range nE)`:
  --   * `proj₂ (process-edges H o H.dom)`
  --       : HomTerm (unflatten (map vlab dom)) (unflatten (map vlab finalStack))
  --   * `permute-via-vlab vlab p`
  --       : HomTerm (unflatten (map vlab finalStack)) (unflatten (map vlab cod))
  -- and `domL H = map vlab dom`, `codL H = map vlab cod` definitionally,
  -- so the composite has the claimed boundary type.
  decodeOrd : (o : Order) → Valid o
            → HomTerm (unflatten (domL H)) (unflatten (codL H))
  decodeOrd o p =
    permute-via-vlab H.vlab p ∘ proj₂ (process-edges H o H.dom)

  -- (N+K) per-swap analytic step `swap-≈` and its closure-lift `↝*⇒≈` and
  -- the central `order-invariant` are NO LONGER defined here: `swap-≈` is
  -- now PROVEN in `Discharge.SwapStep`, so the swap-dependent assembly has
  -- moved downstream to `Discharge.IsoInvarianceConcrete` (which re-defines
  -- `↝*⇒≈`, `order-invariant`, `decode-ord-resp-iso` feeding the real
  -- `SwapStep.swap-≈` and `WiringLemmas.NoInv-τ`).
  --
  -- The former postulates `swap-validity` and `fin-order-NoInv` are GONE:
  --   * `swap-validity`    is now PROVEN in `Discharge.SwapValidity`
  --                        (modulo `front-swap-stack-↭`);
  --   * `fin-order-NoInv`  is FALSE for arbitrary `H` and is now supplied at
  --                        the call site by `FinOrderNoInv.fin-order-NoInv-⟪⟫`
  --                        (threaded as an explicit hypothesis).

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

  -- A real use of Lemma A: ψ preserves the dependency relation.  This is
  -- the justification for `NoInv-τ` below (a linear extension pulls back
  -- to a linear extension across the dependency-order iso).
  ψ-pres-dep : ∀ {e e'} → Dep H e e' → Dep J (ψ e) (ψ e')
  ψ-pres-dep = ≺⇒ψ≺ Φ

  -- (Lem0, boundary part) the iso identifies the boundaries: `domL`/`codL`
  -- agree because φ preserves vertex labels and the boundary lists.
  --   domL J = map J.vlab J.dom
  --          ≡ map J.vlab (map φ H.dom)   [φ-dom]
  --          ≡ map (J.vlab ∘ φ) H.dom     [sym map-∘]
  --          ≡ map H.vlab H.dom           [map-cong φ-lab]
  --          = domL H
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

  -- The ψ-pullback of J's natural order onto H's edges.  `τ` lists H's
  -- edges in the order ψ⁻¹ induces from J's `Fin` order; it is a
  -- permutation of H's `range`, and `ψ-pres-dep` (Lemma A) makes it a
  -- linear extension of `Dep H`.
  τ : List (Fin H.nE)
  τ = map ψ⁻¹ (range J.nE)

  -- `τ ↭ range H.nE`: the image of J's complete `range` under the
  -- edge-bijection ψ⁻¹ : Fin J.nE → Fin H.nE is a permutation of H's
  -- complete `range`.  Proof via the constructive Fin-bijection
  -- permutation lemma `tabulate-bij-↭-via-eq` (from `LinearityIso`),
  -- bridged from `range` to `tabulate id` by the local lemmas above.
  τ↭range : τ Perm.↭ range H.nE
  τ↭range = subst (λ xs → xs Perm.↭ range H.nE) bridge step
    where
      -- H.nE ≡ J.nE from the edge bijection.
      nE-eq : H.nE ≡ J.nE
      nE-eq = bij-fin-ℕ-≡ ψ ψ⁻¹ ψ-left ψ-rght

      -- tabulate (id ∘ ψ⁻¹) ↭ tabulate id   (over Fin H.nE)
      base : tabulate {n = J.nE} (λ i → ψ⁻¹ i)
               Perm.↭ tabulate {n = H.nE} (λ i → i)
      base = tabulate-bij-↭-via-eq (sym nE-eq) (λ i → i) ψ⁻¹ ψ ψ-rght ψ-left

      -- tabulate id (over Fin H.nE) ≡ range H.nE
      base-range : tabulate {n = J.nE} (λ i → ψ⁻¹ i) Perm.↭ range H.nE
      base-range =
        subst (λ xs → tabulate {n = J.nE} (λ i → ψ⁻¹ i) Perm.↭ xs)
              (sym (range≡tabulate-id H.nE)) base

      -- tabulate ψ⁻¹ ≡ map ψ⁻¹ (range J.nE) = τ
      bridge : tabulate {n = J.nE} (λ i → ψ⁻¹ i) ≡ map ψ⁻¹ (range J.nE)
      bridge = tabulate-as-map-range ψ⁻¹

      step : tabulate {n = J.nE} (λ i → ψ⁻¹ i) Perm.↭ range H.nE
      step = base-range

  -- (`NoInv-τ` is now PROVEN in `Discharge.WiringLemmas` (Lemma 4), so it
  -- is no longer postulated here.  The assembly that consumed it,
  -- `decode-ord-resp-iso`, has moved to `Discharge.IsoInvarianceConcrete`.)

  -- (Lem0) vertex relabelling is free + ψ re-indexing (`iso-transport`)
  -- is now PROVEN in `Discharge.IsoTransport`, consumed directly by
  -- `Discharge.IsoInvarianceConcrete`; the former postulate here is GONE.

  -- (Iso-invariance of the order-indexed decoder, `decode-ord-resp-iso`,
  -- has moved to `Discharge.IsoInvarianceConcrete`: it is the assembly that
  -- consumes the now-downstream `order-invariant` and the now-proven
  -- `NoInv-τ`.)
