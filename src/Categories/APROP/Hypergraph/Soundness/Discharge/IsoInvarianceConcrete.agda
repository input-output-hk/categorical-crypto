-- The swap-dependent assembly of the decoder's iso-invariance, fed the
-- discharged lemmas `swap-≈` (`SwapStep`), `swap-validity` (`SwapValidity`),
-- `NoInv-τ` (`WiringLemmas` Lemma 4), `iso-transport` (`IsoTransport`).
-- `↝*⇒≈`, `order-invariant`, `decode-ord-resp-iso` assemble these;
-- `decode-ord-resp-iso`'s type is the one `DecodeRelRespIsoWired` consumes.
{-# OPTIONS --safe --without-K #-}

open import Categories.APROP

module Categories.APROP.Hypergraph.Soundness.Discharge.IsoInvarianceConcrete
  (sig : APROPSignature) where

open APROP sig

open import Categories.APROP.Hypergraph.Core using (Hypergraph; domL; codL)
open import Categories.APROP.Hypergraph.Iso using (_≅ᴴ_)
open import Categories.APROP.Hypergraph.FromAPROP sig using (FlatGen; range)
open import Categories.APROP.Hypergraph.Soundness.Unflatten sig using (unflatten)

import Categories.APROP.Hypergraph.Soundness.Discharge.IsoInvarianceWiring sig as IW
import Categories.APROP.Hypergraph.Soundness.Discharge.SwapStep sig as SS
import Categories.APROP.Hypergraph.Soundness.Discharge.SwapValidity sig as SV
import Categories.APROP.Hypergraph.Soundness.Discharge.WiringLemmas sig as WL
import Categories.APROP.Hypergraph.Soundness.Discharge.IsoTransport sig as IT
import Categories.APROP.Hypergraph.Soundness.Discharge.FinOrderNoInv sig as FN
open import Categories.APROP.Hypergraph.Soundness.Discharge.EdgeDependency
  using (Dep)
open import Categories.APROP.Hypergraph.Soundness.Linearity sig using (Linear)

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
-- Per-hypergraph: the closure-lift and order-invariance.
------------------------------------------------------------------------

-- Threads the analytic-step inputs of `SwapStep.swap-≈`, supplied at the
-- call site (`H = ⟪f⟫`) by `DecodeRelRespIsoWired`:
--   * `K : FaithfulnessResidual`  (the Kelly residual),
--   * `uniq-cod : Unique (cod H)`  (VERTEX-level codomain uniqueness — TRUE;
--     NOT the X-level `Unique (map vlab cod)`),
--   * `run-interchange` — the per-swap `RunInterchange` (N) witness.
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

  -- The per-swap analytic step (`SwapStep`), applied at `H`, threaded the
  -- swap-site provenance `o₁ ↭ range nE`.
  swap-≈ : ∀ {o₁ o₂ : Order} → o₁ ↝ o₂
         → o₁ Perm.↭ range (Hypergraph.nE H)
         → (p₁ : Valid o₁) (p₂ : Valid o₂)
         → decodeOrd o₁ p₁ ≈Term decodeOrd o₂ p₂
  swap-≈ = SS.swap-≈ H dih K uniq-cod run-interchange

  -- Validity is preserved by an adjacent-independent swap (`SwapValidity`).
  swap-validity : ∀ {o₁ o₂ : Order} → o₁ ↝ o₂ → Valid o₁ → Valid o₂
  swap-validity = SV.PerHG.swap-validity H dih lin

  -- An adjacent-independent swap IS a permutation (a transposition under the
  -- prefix `ps`), so it preserves the `↭ range nE` provenance.
  ↝⇒↭ : ∀ {o₁ o₂ : Order} → o₁ ↝ o₂ → o₁ Perm.↭ o₂
  ↝⇒↭ (swap-step ps {x} {y} qs _) =
    PermProp.++⁺ˡ ps (Perm.swap x y Perm.refl)

  -- Lift the per-swap step to the reflexive-transitive closure, threading
  -- both the validity witness and the `↭ range nE` provenance.
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

  -- Order-invariance of the decoder, driven by `connectivity`, threaded the
  -- starting order's `↭ range nE` provenance (the chase starts from `τ`).
  order-invariant :
    ∀ (o₁ o₂ : Order) → o₁ Perm.↭ o₂ → NoInv o₁ → NoInv o₂ →
    o₁ Perm.↭ range (Hypergraph.nE H) →
    (p₁ : Valid o₁) →
    Σ[ p₂ ∈ Valid o₂ ] decodeOrd o₁ p₁ ≈Term decodeOrd o₂ p₂
  order-invariant o₁ o₂ p n₁ n₂ o₁↭range p₁ =
    ↝*⇒≈ (connectivity p n₁ n₂) o₁↭range p₁

------------------------------------------------------------------------
-- Across an isomorphism: iso-invariance of the decoder.
------------------------------------------------------------------------

-- `dihH`/`dihJ` (Dep-irreflexivity), `noInvH`/`noInvJ` (natural-order
-- no-inversion), and `codUniqueH`/`codUniqueJ` (VERTEX-level codomain
-- uniqueness — TRUE) are threaded as explicit hypotheses: they are FALSE
-- for arbitrary `H`/`J` and supplied at the `H = ⟪f⟫`, `J = ⟪g⟫` call site.
-- `K` (the Kelly residual) is shared by `SwapStep` and `IsoTransport`;
-- `run-interchange-H` is H's per-swap `RunInterchange` (N) witness.
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

  -- `NoInv-τ` (WiringLemmas Lemma 4), fed J's no-inversion `noInvJ`.
  NoInv-τ : PJ.NoInv (range J.nE) → PH.NoInv (IW.τ Φ)
  NoInv-τ noInvJ = L4.NoInv-τ noInvJ

  -- Iso-invariance of the (order-indexed) decoder, assembling
  -- `order-invariant` (from `CPH`), `NoInv-τ`, and `iso-transport`.
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
