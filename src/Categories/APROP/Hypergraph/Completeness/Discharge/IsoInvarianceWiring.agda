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

module PerHG (H : Hypergraph FlatGen) where
  private module H = Hypergraph H

  -- Acyclicity: no edge depends on itself.  TRUE for `⟪f⟫F` (a generator
  -- box's input and output wires are disjoint); postulated here.
  postulate Dep-irrefl : ∀ {e} → ¬ (Dep H e e)

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

  -- (N+K) per-swap analytic step: swapping two adjacent *independent*
  -- (Dep-incomparable) edges changes the decoding only up to ≈Term, by the
  -- interchange axiom σ∘(p⊗q)≈(q⊗p)∘σ on the two opaque boxes plus
  -- permutation coherence on the surrounding wiring.  THE analytic content.
  -- Carries the validity witnesses for both endpoints (the decoder needs
  -- them; the swap relates the two *valid* decodings).
  postulate
    swap-≈ : ∀ {o₁ o₂ : Order} → o₁ ↝ o₂
           → (p₁ : Valid o₁) (p₂ : Valid o₂)
           → decodeOrd o₁ p₁ ≈Term decodeOrd o₂ p₂

  -- Validity is preserved by an adjacent-independent swap.  TRUE: the
  -- live-wire multiset / final stack is order-independent for swaps of
  -- Dep-incomparable adjacent edges, so `finalStack o₁ ↭ cod` transports
  -- to `finalStack o₂ ↭ cod`.  Bookkeeping postulate (no analytic content).
  postulate
    swap-validity : ∀ {o₁ o₂ : Order} → o₁ ↝ o₂ → Valid o₁ → Valid o₂

  -- Lift the per-swap step to the reflexive-transitive closure, threading
  -- the validity witness.  REAL: dependent fold over the `Star`.
  ↝*⇒≈ : ∀ {o₁ o₂ : Order} → o₁ ↝* o₂ → (p₁ : Valid o₁)
       → Σ[ p₂ ∈ Valid o₂ ] decodeOrd o₁ p₁ ≈Term decodeOrd o₂ p₂
  ↝*⇒≈ ε        p₁ = p₁ , ≈-Term-refl
  ↝*⇒≈ (s ◅ ss) p₁ =
    let p-mid          = swap-validity s p₁
        (p₂ , mid≈rec) = ↝*⇒≈ ss p-mid
    in  p₂ , ≈-Term-trans (swap-≈ s p₁ p-mid) mid≈rec

  -- Order-invariance of the decoder, driven by `connectivity`.  REAL:
  -- this is the payoff of the two order-theory modules.
  order-invariant :
    ∀ (o₁ o₂ : Order) → o₁ Perm.↭ o₂ → NoInv o₁ → NoInv o₂ →
    (p₁ : Valid o₁) →
    Σ[ p₂ ∈ Valid o₂ ] decodeOrd o₁ p₁ ≈Term decodeOrd o₂ p₂
  order-invariant o₁ o₂ p n₁ n₂ p₁ = ↝*⇒≈ (connectivity p n₁ n₂) p₁

  -- (LemC) the natural Fin order is a linear extension (= the proven
  -- `AllFire-natural-range`, in `NoInv` form).
  postulate
    fin-order-NoInv : NoInv (range H.nE)

------------------------------------------------------------------------
-- Across an isomorphism: iso-invariance of the decoder.
------------------------------------------------------------------------

module _ {H J : Hypergraph FlatGen} (Φ : H ≅ᴴ J) where
  private
    module PH = PerHG H
    module PJ = PerHG J
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
  τ : PH.Order
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

  postulate
    NoInv-τ : PH.NoInv τ

  -- (Lem0) vertex relabelling is free + ψ re-indexing: decoding J in its
  -- natural order equals decoding H in the pulled-back order τ, after the
  -- boundary transport.  Now validity-threaded: given a validity witness
  -- for J's natural order, it produces a validity witness for the
  -- pulled-back order τ on H together with the transported ≈Term.
  postulate
    iso-transport :
      (vJ : PJ.Valid (range J.nE))
      → Σ[ vτ ∈ PH.Valid τ ]
          ( subst₂ HomTerm (cong unflatten domL-iso) (cong unflatten codL-iso)
                   (PJ.decodeOrd (range J.nE) vJ)
            ≈Term PH.decodeOrd τ vτ )

  -- Iso-invariance of the (order-indexed) decoder.  The CENTRAL step is
  -- `PH.order-invariant` (real, via connectivity); everything else is the
  -- transport/bookkeeping postulated above.  Takes a validity witness for
  -- J's natural order (the caller has it from `decode-attempt-LinearP`) and
  -- returns a validity witness for H's natural order with the ≈Term.
  decode-ord-resp-iso :
      (vJ : PJ.Valid (range J.nE))
      → Σ[ vH ∈ PH.Valid (range H.nE) ]
          ( subst₂ HomTerm (cong unflatten domL-iso) (cong unflatten codL-iso)
                   (PJ.decodeOrd (range J.nE) vJ)
            ≈Term PH.decodeOrd (range H.nE) vH )
  decode-ord-resp-iso vJ =
    let (vτ , transport≈)   = iso-transport vJ
        (vH , invariant≈)   =
          PH.order-invariant τ (range H.nE) τ↭range NoInv-τ
                             PH.fin-order-NoInv vτ
    in  vH , ≈-Term-trans transport≈ invariant≈
