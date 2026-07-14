{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- STRICT swap-dependent assembly of the decoder's order-invariance.
--
-- `↝*⇒≈ˢ` (Star-induction over adjacent-incomparable swaps) and
-- `order-invariantˢ` (driven by `connectivity`) are PURE `≈ˢ`-transitivity
-- plumbing, threading the strict validity witness `Validˢ` and the swap-site
-- `↭ range nE` provenance.  No Mac-Lane content.
--
-- The cross-iso `decode-ordˢ-resp-iso` (the boundary with `IsoTransport`) is
-- provided PARAMETERISED over the strict transport residual (`iso-transportˢ`)
-- and `NoInv-τ`, discharged in `Strict/Iso/IsoTransport` and
-- `IsoInvarianceWiring` (Lemma 4).
--------------------------------------------------------------------------------

open import Categories.APROP
open import Relation.Binary using (DecidableEquality)

module Categories.APROP.Hypergraph.Soundness.Strict.Iso.IsoInvarianceConcrete
  (sig : APROPSignature)
  (_≟X_ : DecidableEquality (APROPSignature.X sig))
  where

open APROP sig using (X)

open import Categories.APROP.Hypergraph.Model.Core using (Hypergraph)
open import Categories.APROP.Hypergraph.Model.FromAPROP sig using (FlatGen; range)
open import Categories.APROP.Hypergraph.Soundness.Linearity.Linearity sig using (Linear)

open import Categories.APROP.Hypergraph.Soundness.Discharge.EdgeDependency using (Dep)

open import Categories.APROP.Hypergraph.Soundness.Strict.Decode.Decoder sig _≟X_
import Categories.APROP.Hypergraph.Soundness.Strict.Interchange.SwapStep sig _≟X_ as SS
open import Categories.APROP.Hypergraph.Soundness.Strict.Interchange.RunInterchangeTail sig _≟X_
  using (RunInterchangeˢ)

open import Data.Fin using (Fin)
open import Data.List using (_∷_; _++_)
open import Data.List.Relation.Unary.Unique.Propositional using (Unique)
open import Data.Product using (Σ-syntax; _,_)
import Data.List.Relation.Binary.Permutation.Propositional as Perm
import Data.List.Relation.Binary.Permutation.Propositional.Properties as PermProp
open import Relation.Nullary using (¬_)
open import Relation.Binary.Construct.Closure.ReflexiveTransitive using (Star; ε; _◅_)

------------------------------------------------------------------------
-- Per-hypergraph: the closure-lift and order-invariance.  Threads the (N)
-- residual `run-interchange` (the strict `RunInterchangeˢ` witness).
------------------------------------------------------------------------

module PerHG (H : Hypergraph FlatGen)
             (dih : ∀ {e} → ¬ (Dep H e e))
             (lin : Linear H)
             (uniq-cod : Unique (Hypergraph.cod H))
             (run-interchange
               : ∀ (ps qs : SS.PerHG.Order H dih lin)
                   {e e' : Fin (Hypergraph.nE H)}
                   (inc : SS.PerHG.Incompˢ H dih lin e e')
                 → (ps ++ e' ∷ e ∷ qs) Perm.↭ range (Hypergraph.nE H)
                 → RunInterchangeˢ H dih lin ps qs inc) where
  open SS.PerHG H dih lin
    using (Order; Validˢ; decodeOrdˢ; _↝_; _↝*_; NoInv; connectivity
          ; swap-step; swap-validityˢ)

  -- The per-swap analytic step (`SwapStep`), threaded the provenance.
  swap-≈ˢ : ∀ {o₁ o₂ : Order} → o₁ ↝ o₂
          → o₁ Perm.↭ range (Hypergraph.nE H)
          → (p₁ : Validˢ o₁) (p₂ : Validˢ o₂)
          → decodeOrdˢ o₁ p₁ ≈ˢ decodeOrdˢ o₂ p₂
  swap-≈ˢ = SS.swap-≈ˢ H dih lin uniq-cod run-interchange

  -- An adjacent-independent swap IS a permutation (a transposition under
  -- the prefix `ps`), so it preserves the `↭ range nE` provenance.
  ↝⇒↭ : ∀ {o₁ o₂ : Order} → o₁ ↝ o₂ → o₁ Perm.↭ o₂
  ↝⇒↭ (swap-step ps {x} {y} qs _) = PermProp.++⁺ˡ ps (Perm.swap x y Perm.refl)

  -- Lift the per-swap step to the reflexive-transitive closure, threading
  -- both the validity witness and the `↭ range nE` provenance.
  ↝*⇒≈ˢ : ∀ {o₁ o₂ : Order} → o₁ ↝* o₂
        → o₁ Perm.↭ range (Hypergraph.nE H)
        → (p₁ : Validˢ o₁)
        → Σ[ p₂ ∈ Validˢ o₂ ] decodeOrdˢ o₁ p₁ ≈ˢ decodeOrdˢ o₂ p₂
  ↝*⇒≈ˢ ε        o₁↭range p₁ = p₁ , ≈-refl
  ↝*⇒≈ˢ (s ◅ ss) o₁↭range p₁ =
    let p-mid          = swap-validityˢ s p₁
        o-mid↭range    = Perm.↭-trans (Perm.↭-sym (↝⇒↭ s)) o₁↭range
        (p₂ , mid≈rec) = ↝*⇒≈ˢ ss o-mid↭range p-mid
    in  p₂ , ≈-trans (swap-≈ˢ s o₁↭range p₁ p-mid) mid≈rec

  -- Order-invariance of the decoder, driven by `connectivity`.
  order-invariantˢ :
    ∀ (o₁ o₂ : Order) → o₁ Perm.↭ o₂ → NoInv o₁ → NoInv o₂ →
    o₁ Perm.↭ range (Hypergraph.nE H) →
    (p₁ : Validˢ o₁) →
    Σ[ p₂ ∈ Validˢ o₂ ] decodeOrdˢ o₁ p₁ ≈ˢ decodeOrdˢ o₂ p₂
  order-invariantˢ o₁ o₂ p n₁ n₂ o₁↭range p₁ = ↝*⇒≈ˢ (connectivity p n₁ n₂) o₁↭range p₁
