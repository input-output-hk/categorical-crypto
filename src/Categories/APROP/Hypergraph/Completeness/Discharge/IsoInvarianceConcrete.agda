-- NOT `--safe`: this module performs the swap-dependent assembly that used
-- to live (postulate-fed) inside `IsoInvarianceWiring.agda`'s `PerHG` and
-- cross-iso modules.  It now feeds the REAL discharged lemmas:
--
--   * `swap-≈`   — PROVEN in `Discharge.SwapStep` (modulo its own bottom
--                  `front-swap-≈`), here applied at the right `H`.
--   * `NoInv-τ`  — PROVEN in `Discharge.WiringLemmas` (Lemma 4), here fed
--                  J's `fin-order-NoInv` as the explicit hypothesis.
--
-- The remaining inputs (`swap-validity`, `fin-order-NoInv`, `iso-transport`)
-- are still the open postulates kept in `IsoInvarianceWiring`.
--
-- `↝*⇒≈`, `order-invariant`, `decode-ord-resp-iso` below are EXACT copies
-- of the (deleted) `IsoInvarianceWiring` bodies, with `swap-≈`/`NoInv-τ`
-- now sourced from `SwapStep`/`WiringLemmas` instead of IW postulates.
-- `decode-ord-resp-iso`'s type matches `IW`'s former one verbatim so that
-- `DecodeRelRespIsoWired` consumes it as a drop-in.
{-# OPTIONS --without-K #-}

open import Categories.APROP

module Categories.APROP.Hypergraph.Completeness.Discharge.IsoInvarianceConcrete
  (sig : APROPSignature) where

open APROP sig

open import Categories.APROP.Hypergraph.Core using (Hypergraph; domL; codL)
open import Categories.APROP.Hypergraph.Iso using (_≅ᴴ_)
open import Categories.APROP.Hypergraph.FromAPROP sig using (FlatGen; range)
open import Categories.APROP.Hypergraph.Completeness.Unflatten sig using (unflatten)

import Categories.APROP.Hypergraph.Completeness.Discharge.IsoInvarianceWiring sig as IW
import Categories.APROP.Hypergraph.Completeness.Discharge.SwapStep sig as SS
import Categories.APROP.Hypergraph.Completeness.Discharge.SwapValidity sig as SV
import Categories.APROP.Hypergraph.Completeness.Discharge.WiringLemmas sig as WL
import Categories.APROP.Hypergraph.Completeness.Discharge.IsoTransport sig as IT
import Categories.APROP.Hypergraph.Completeness.Discharge.FinOrderNoInv sig as FN
open import Categories.APROP.Hypergraph.Completeness.Discharge.EdgeDependency
  using (Dep)

open import Relation.Nullary using (¬_)
open import Data.Product using (Σ; Σ-syntax; _,_; proj₁; proj₂)
import Data.List.Relation.Binary.Permutation.Propositional as Perm
open import Relation.Binary.PropositionalEquality
  using (_≡_; cong; subst₂)
open import Relation.Binary.Construct.Closure.ReflexiveTransitive
  using (Star; ε; _◅_)

------------------------------------------------------------------------
-- Per-hypergraph: the closure-lift and order-invariance, now fed the real
-- `SwapStep.swap-≈` (applied at `H`) and IW's kept `swap-validity`.
------------------------------------------------------------------------

module PerHG (H : Hypergraph FlatGen)
             (dih : ∀ {e} → ¬ (Dep H e e)) where
  module PH = IW.PerHG H dih
  open PH using (Order; Valid; decodeOrd; _↝_; _↝*_; NoInv; connectivity)

  -- The real per-swap analytic step, proven in `SwapStep`, applied at `H`.
  swap-≈ : ∀ {o₁ o₂ : Order} → o₁ ↝ o₂
         → (p₁ : Valid o₁) (p₂ : Valid o₂)
         → decodeOrd o₁ p₁ ≈Term decodeOrd o₂ p₂
  swap-≈ = SS.swap-≈ H dih

  -- Validity is preserved by an adjacent-independent swap.  Now PROVEN in
  -- `Discharge.SwapValidity` (modulo its own `front-swap-stack-↭`), applied
  -- at `H`; the former `IW.PerHG.swap-validity` postulate is GONE.
  swap-validity : ∀ {o₁ o₂ : Order} → o₁ ↝ o₂ → Valid o₁ → Valid o₂
  swap-validity = SV.PerHG.swap-validity H dih

  -- Lift the per-swap step to the reflexive-transitive closure, threading
  -- the validity witness.  REAL: dependent fold over the `Star`.  (Copy of
  -- the former `IW.PerHG.↝*⇒≈`.)
  ↝*⇒≈ : ∀ {o₁ o₂ : Order} → o₁ ↝* o₂ → (p₁ : Valid o₁)
       → Σ[ p₂ ∈ Valid o₂ ] decodeOrd o₁ p₁ ≈Term decodeOrd o₂ p₂
  ↝*⇒≈ ε        p₁ = p₁ , ≈-Term-refl
  ↝*⇒≈ (s ◅ ss) p₁ =
    let p-mid          = swap-validity s p₁
        (p₂ , mid≈rec) = ↝*⇒≈ ss p-mid
    in  p₂ , ≈-Term-trans (swap-≈ s p₁ p-mid) mid≈rec

  -- Order-invariance of the decoder, driven by `connectivity`.  REAL:
  -- this is the payoff of the two order-theory modules.  (Copy of the
  -- former `IW.PerHG.order-invariant`.)
  order-invariant :
    ∀ (o₁ o₂ : Order) → o₁ Perm.↭ o₂ → NoInv o₁ → NoInv o₂ →
    (p₁ : Valid o₁) →
    Σ[ p₂ ∈ Valid o₂ ] decodeOrd o₁ p₁ ≈Term decodeOrd o₂ p₂
  order-invariant o₁ o₂ p n₁ n₂ p₁ = ↝*⇒≈ (connectivity p n₁ n₂) p₁

------------------------------------------------------------------------
-- Across an isomorphism: iso-invariance of the decoder, now fed the real
-- `WiringLemmas.NoInv-τ` (Lemma 4) and IW's kept `iso-transport`.
------------------------------------------------------------------------

-- The two `Dep`-irreflexivity witnesses (`dihH`, `dihJ`) and the two
-- natural-order no-inversion witnesses (`noInvH`, `noInvJ`) are threaded as
-- explicit hypotheses: they are FALSE for arbitrary `H`/`J`, and supplied at
-- the call site (`H = ⟪f⟫`, `J = ⟪g⟫`) from `DepIrrefl.dep-irrefl-⟪⟫` and
-- `FinOrderNoInv.fin-order-NoInv-⟪⟫`.  `iso-transport` is now sourced from
-- the proven `Discharge.IsoTransport` (was the deleted `IW.iso-transport`).
module _ {H J : Hypergraph FlatGen} (Φ : H ≅ᴴ J)
         (dihH : ∀ {e} → ¬ (Dep H e e))
         (dihJ : ∀ {e} → ¬ (Dep J e e)) where
  private
    module PH  = IW.PerHG H dihH
    module PJ  = IW.PerHG J dihJ
    module CPH = PerHG H dihH
    module H   = Hypergraph H
    module J   = Hypergraph J
    module L4  = WL.Lemma4 Φ dihH dihJ

  -- The real `NoInv-τ` (WiringLemmas Lemma 4), fed J's natural-order
  -- no-inversion `noInvJ` (the explicit hypothesis).
  NoInv-τ : PJ.NoInv (range J.nE) → PH.NoInv (IW.τ Φ)
  NoInv-τ noInvJ = L4.NoInv-τ noInvJ

  -- Iso-invariance of the (order-indexed) decoder.  `order-invariant` is
  -- sourced from `CPH` (= `PerHG H`, the real-swap-fed version), `NoInv-τ`
  -- the proven one above, and `iso-transport` from `Discharge.IsoTransport`;
  -- the two `fin-order-NoInv` facts are explicit hypotheses.
  decode-ord-resp-iso :
      PH.NoInv (range H.nE) → PJ.NoInv (range J.nE)
      → (vJ : PJ.Valid (range J.nE))
      → Σ[ vH ∈ PH.Valid (range H.nE) ]
          ( subst₂ HomTerm (cong unflatten (IW.domL-iso Φ)) (cong unflatten (IW.codL-iso Φ))
                   (PJ.decodeOrd (range J.nE) vJ)
            ≈Term PH.decodeOrd (range H.nE) vH )
  decode-ord-resp-iso noInvH noInvJ vJ =
    let (vτ , transport≈)   = IT.iso-transport Φ dihH dihJ vJ
        (vH , invariant≈)   =
          CPH.order-invariant (IW.τ Φ) (range H.nE) (IW.τ↭range Φ) (NoInv-τ noInvJ)
                              noInvH vτ
    in  vH , ≈-Term-trans transport≈ invariant≈
