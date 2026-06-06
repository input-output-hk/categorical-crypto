-- NOT `--safe`: this module performs the swap-dependent assembly of the
-- decoder's iso-invariance, fed the discharged lemmas:
--
--   * `swap-≈`   — from `Discharge.SwapStep` (modulo its own bottom
--                  `front-swap-≈`), here applied at the right `H`.
--   * `NoInv-τ`  — from `Discharge.WiringLemmas` (Lemma 4), here fed
--                  J's `fin-order-NoInv` as the explicit hypothesis.
--
-- The other inputs are discharged lemmas too: `swap-validity` from
-- `Discharge.SwapValidity`, `iso-transport` from `Discharge.IsoTransport`;
-- `fin-order-NoInv` is supplied as an explicit hypothesis at the call site.
--
-- `↝*⇒≈`, `order-invariant`, `decode-ord-resp-iso` source `swap-≈`/`NoInv-τ`
-- from `SwapStep`/`WiringLemmas`.  `decode-ord-resp-iso`'s type is the one
-- `DecodeRelRespIsoWired` consumes as a drop-in.
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
open import Categories.APROP.Hypergraph.Completeness.Linearity sig using (Linear)

open import Relation.Nullary using (¬_)
open import Data.Fin using (Fin)
open import Data.Product using (Σ; Σ-syntax; _,_; proj₁; proj₂)
open import Data.List using (_∷_; _++_)
open import Data.List.Relation.Unary.Unique.Propositional using (Unique)
import Data.List.Relation.Binary.Permutation.Propositional as Perm
import Data.List.Relation.Binary.Permutation.Propositional.Properties as PermProp
open import Relation.Binary.PropositionalEquality
  using (_≡_; cong; subst₂)
open import Relation.Binary.Construct.Closure.ReflexiveTransitive
  using (Star; ε; _◅_)

-- The Kelly faithfulness residual, threaded from the top of the chain.
open import Categories.PermuteCoherence.Faithfulness asFreeMonoidalData
  using (FaithfulnessResidual)

------------------------------------------------------------------------
-- Per-hypergraph: the closure-lift and order-invariance, now fed the real
-- `SwapStep.swap-≈` (applied at `H`) and IW's kept `swap-validity`.
------------------------------------------------------------------------

-- The per-hypergraph module now threads the analytic-step inputs of
-- `SwapStep.swap-≈`:
--   * `K          : FaithfulnessResidual`     (the Kelly residual),
--   * `uniq-cod    : Unique (cod H)`           (VERTEX-level codomain
--     uniqueness — TRUE; NOT the X-level `Unique (map vlab cod)`),
--   * `run-interchange` — the per-swap `RunInterchange` (N) witness (the
--     genuine interchange-axiom residual).
-- All three are supplied at the call site (`H = ⟪f⟫`) by
-- `DecodeRelRespIsoWired`.
module PerHG (H : Hypergraph FlatGen)
             (dih : ∀ {e} → ¬ (Dep H e e))
             (lin : Linear H)
             (K : FaithfulnessResidual)
             (uniq-cod : Unique (Hypergraph.cod H))
             (run-interchange
               : ∀ (ps qs : SS.PerHG.Order H dih)
                   {e e' : Fin (Hypergraph.nE H)}
                   (inc : SS.PerHG.Incomp H dih e e')
                 → (ps ++ e' ∷ e ∷ qs) Perm.↭ range (Hypergraph.nE H)
               → SS.FrontSwap.RunInterchange H dih K uniq-cod ps qs inc) where
  module PH = IW.PerHG H dih
  open PH using (Order; Valid; decodeOrd; _↝_; _↝*_; NoInv; connectivity)
  open IW.PerHG.L H dih using (swap-step)

  -- The real per-swap analytic step, proven in `SwapStep`, applied at `H`.
  -- Now threaded the SWAP-SITE PROVENANCE `o₁ ↭ range nE`.
  swap-≈ : ∀ {o₁ o₂ : Order} → o₁ ↝ o₂
         → o₁ Perm.↭ range (Hypergraph.nE H)
         → (p₁ : Valid o₁) (p₂ : Valid o₂)
         → decodeOrd o₁ p₁ ≈Term decodeOrd o₂ p₂
  swap-≈ = SS.swap-≈ H dih K uniq-cod run-interchange

  -- Validity is preserved by an adjacent-independent swap, via
  -- `Discharge.SwapValidity` (modulo its own `front-swap-stack-↭`), applied
  -- at `H`.
  swap-validity : ∀ {o₁ o₂ : Order} → o₁ ↝ o₂ → Valid o₁ → Valid o₂
  swap-validity = SV.PerHG.swap-validity H dih lin

  -- An adjacent-independent swap IS a permutation (a transposition under
  -- the prefix `ps`), so it preserves the `↭ range nE` provenance along
  -- the connectivity chase.
  ↝⇒↭ : ∀ {o₁ o₂ : Order} → o₁ ↝ o₂ → o₁ Perm.↭ o₂
  ↝⇒↭ (swap-step ps {x} {y} qs _) =
    PermProp.++⁺ˡ ps (Perm.swap x y Perm.refl)

  -- Lift the per-swap step to the reflexive-transitive closure, threading
  -- BOTH the validity witness AND the `↭ range nE` provenance (preserved
  -- at each swap by `↝⇒↭`).  REAL: dependent fold over the `Star`.
  ↝*⇒≈ : ∀ {o₁ o₂ : Order} → o₁ ↝* o₂
       → o₁ Perm.↭ range (Hypergraph.nE H)
       → (p₁ : Valid o₁)
       → Σ[ p₂ ∈ Valid o₂ ] decodeOrd o₁ p₁ ≈Term decodeOrd o₂ p₂
  ↝*⇒≈ ε        o₁↭range p₁ = p₁ , ≈-Term-refl
  ↝*⇒≈ (s ◅ ss) o₁↭range p₁ =
    let p-mid          = swap-validity s p₁
        o-mid↭range    = Perm.↭-trans (Perm.↭-sym (↝⇒↭ s)) o₁↭range
        (p₂ , mid≈rec) = ↝*⇒≈ ss o-mid↭range p-mid
    in  p₂ , ≈-Term-trans (swap-≈ s o₁↭range p₁ p-mid) mid≈rec

  -- Order-invariance of the decoder, driven by `connectivity`.  REAL:
  -- this is the payoff of the two order-theory modules.  Now threaded the
  -- starting order's `↭ range nE` provenance (supplied at the call site:
  -- the chase starts from `τ ↭ range`).
  order-invariant :
    ∀ (o₁ o₂ : Order) → o₁ Perm.↭ o₂ → NoInv o₁ → NoInv o₂ →
    o₁ Perm.↭ range (Hypergraph.nE H) →
    (p₁ : Valid o₁) →
    Σ[ p₂ ∈ Valid o₂ ] decodeOrd o₁ p₁ ≈Term decodeOrd o₂ p₂
  order-invariant o₁ o₂ p n₁ n₂ o₁↭range p₁ =
    ↝*⇒≈ (connectivity p n₁ n₂) o₁↭range p₁

------------------------------------------------------------------------
-- Across an isomorphism: iso-invariance of the decoder, fed
-- `WiringLemmas.NoInv-τ` (Lemma 4) and `IsoTransport.iso-transport`.
------------------------------------------------------------------------

-- The two `Dep`-irreflexivity witnesses (`dihH`, `dihJ`) and the two
-- natural-order no-inversion witnesses (`noInvH`, `noInvJ`) are threaded as
-- explicit hypotheses: they are FALSE for arbitrary `H`/`J`, and supplied at
-- the call site (`H = ⟪f⟫`, `J = ⟪g⟫`) from `DepIrrefl.dep-irrefl-⟪⟫` and
-- `FinOrderNoInv.fin-order-NoInv-⟪⟫`.  `iso-transport` is sourced from
-- `Discharge.IsoTransport`.
--
-- The analytic-step inputs are also threaded explicitly:
--   * `K            : FaithfulnessResidual`   (the Kelly residual, shared
--     by `SwapStep` (via `PerHG H`) and `IsoTransport`),
--   * `codUniqueH    : Unique (cod H)`, `codUniqueJ : Unique (cod J)`
--     (VERTEX-level codomain uniqueness — TRUE; supplied from
--     `⟪_⟫-cod-unique`),
--   * `run-interchange-H` — H's per-swap `RunInterchange` (N) witness.
module _ {H J : Hypergraph FlatGen} (Φ : H ≅ᴴ J)
         (dihH : ∀ {e} → ¬ (Dep H e e))
         (dihJ : ∀ {e} → ¬ (Dep J e e))
         (linH : Linear H)
         (K : FaithfulnessResidual)
         (codUniqueH : Unique (Hypergraph.cod H))
         (codUniqueJ : Unique (Hypergraph.cod J))
         (objUIP : ∀ {A B : ObjTerm} (p q : A ≡ B) → p ≡ q)
         (run-interchange-H
           : ∀ (ps qs : SS.PerHG.Order H dihH)
               {e e' : Fin (Hypergraph.nE H)}
               (inc : SS.PerHG.Incomp H dihH e e')
             → (ps ++ e' ∷ e ∷ qs) Perm.↭ range (Hypergraph.nE H)
           → SS.FrontSwap.RunInterchange H dihH K codUniqueH ps qs inc) where
  private
    module PH  = IW.PerHG H dihH
    module PJ  = IW.PerHG J dihJ
    module CPH = PerHG H dihH linH K codUniqueH run-interchange-H
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
    let (vτ , transport≈)   = IT.iso-transport Φ dihH dihJ K codUniqueH codUniqueJ objUIP vJ
        (vH , invariant≈)   =
          CPH.order-invariant (IW.τ Φ) (range H.nE) (IW.τ↭range Φ) (NoInv-τ noInvJ)
                              noInvH (IW.τ↭range Φ) vτ
    in  vH , ≈-Term-trans transport≈ invariant≈
