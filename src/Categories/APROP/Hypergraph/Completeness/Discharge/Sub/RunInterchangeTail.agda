{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- TAIL-EXTENSION of the run-level interchange.
--
-- The `RunInterchange` record's substantive content sits at the EMPTY tail
-- (the two-edge Mac-Lane interchange); lifting it to an arbitrary suffix
-- `qs` is PURE decoder equivariance under a stack permutation: the
-- `qs`-suffix on the two `↭`-related post-front stacks differs only by an
-- input/output `permute`, with no box / associator content.
--
-- This module proves that lift, `run-interchange-tail`, via
-- `StackEquivariance.process-edges-equivariant`.  Because `e ∷ e' ∷ []` is a
-- CONCRETE 2-prefix, `pe-stack qs A ≡ pe-stack (e ∷ e' ∷ qs) sp` etc. hold
-- DEFINITIONALLY, so `↭-sym ρf` is the `reshuffle` field; the run equation
-- splits both runs at the 2-prefix, feeds `eqv`/`run-eq₀`, telescopes the
-- inner inverse permute, and re-associates.
--------------------------------------------------------------------------------

open import Categories.APROP

module Categories.APROP.Hypergraph.Completeness.Discharge.Sub.RunInterchangeTail
  (sig : APROPSignature) where

open APROP sig

open import Categories.APROP.Hypergraph.Core using (Hypergraph)
open import Categories.APROP.Hypergraph.FromAPROP sig using (FlatGen; range)
open import Categories.APROP.Hypergraph.Completeness.Unflatten sig using (unflatten)
open import Categories.APROP.Hypergraph.Completeness.Permute sig
  using (permute-via-vlab)

import Categories.APROP.Hypergraph.Completeness.Discharge.SwapStep sig as SS
import Categories.APROP.Hypergraph.Completeness.Discharge.Sub.StackEquivariance sig as SE
import Categories.APROP.Hypergraph.Completeness.Discharge.Sub.StackUniqueReach sig as SUR

open import Categories.APROP.Hypergraph.Completeness.Discharge.EdgeDependency
  using (Dep)
open import Categories.APROP.Hypergraph.Completeness.Linearity sig
  using (Linear)

open import Categories.PermuteCoherence.Faithfulness asFreeMonoidalData
  using (FaithfulnessResidual)

open import Data.Fin using (Fin)
open import Data.List using (List; []; _∷_; _++_; map)
open import Data.List.Relation.Unary.Unique.Propositional using (Unique)
import Data.List.Relation.Binary.Permutation.Propositional as Perm
open import Data.Product using (Σ; Σ-syntax; _,_; proj₁; proj₂)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; subst)

------------------------------------------------------------------------
-- Per-hypergraph: fix `H`, `dih`, the Kelly residual `K`, `uniq-cod`,
-- matching `FrontSwap`'s parameters.
------------------------------------------------------------------------

module _ (H : Hypergraph FlatGen)
         (dih : ∀ {e} → ¬ (Dep H e e))
         (K : FaithfulnessResidual)
         (uniq-cod : Unique (Hypergraph.cod H))
         (lin : Linear H)
         where
  private module H = Hypergraph H
  open SS.PerHG H dih
    using (Order; Incomp; pe-stack; pe-term)
  open SS.FrontSwap H dih K uniq-cod using (RunInterchange)

  -- Bind the two StackEquivariance lemmas at the fixed `(H , K)`.
  process-edges-equivariant = SE.process-edges-equivariant H K
  pvv-inverse-left          = SE.pvv-inverse-left H K

  ----------------------------------------------------------------------
  -- ## Sourcing the running-stack freshness invariant `Reservoir≤1`.
  --
  -- `process-edges-equivariant` needs a `Reservoir≤1 qs s'` freshness
  -- invariant on the permuted tail-input stack.  We descend it from a GLOBAL
  -- reservoir on `H.dom` over the combined order, which is the *bound* half
  -- of `Linear H` specialised to that order — TRUE because the order is a
  -- PERMUTATION of `range nE` (`prov`).  NO false-as-stated `∀ o` postulate.
  ----------------------------------------------------------------------

  dom-reservoir-at
    : ∀ (o : Order) → o Perm.↭ range H.nE → SUR.Reservoir≤1 H o H.dom
  dom-reservoir-at o prov =
    SUR.dom-reservoir-prov H (proj₂ lin) o prov

  -- The tail-input reservoir on `B`, descended from the swap-order
  -- reservoir along the prefix `ps` then the concrete 2-prefix `(e' ∷ e ∷ [])`.
  tail-reservoir
    : ∀ (ps qs : Order) (e e' : Fin H.nE)
    → (ps ++ e' ∷ e ∷ qs) Perm.↭ range H.nE
    → SUR.Reservoir≤1 H qs (pe-stack (e' ∷ e ∷ []) (pe-stack ps H.dom))
  tail-reservoir ps qs e e' prov =
    SUR.reservoir-split H (e' ∷ e ∷ []) qs (pe-stack ps H.dom)
      (SUR.reservoir-split H ps (e' ∷ e ∷ qs) H.dom
        (dom-reservoir-at (ps ++ e' ∷ e ∷ qs) prov))

  ----------------------------------------------------------------------
  -- The tail-extension lemma.
  ----------------------------------------------------------------------

  run-interchange-tail
    : ∀ (ps qs : Order) {e e' : Fin H.nE} (inc : Incomp e e')
    → (ps ++ e' ∷ e ∷ qs) Perm.↭ range H.nE
    → RunInterchange ps [] inc
    → RunInterchange ps qs inc
  run-interchange-tail ps qs {e} {e'} inc prov RI₀ =
    record { reshuffle = Perm.↭-sym ρf ; run-eq = run-eq }
    where
      sp : List (Fin H.nV)
      sp = pe-stack ps H.dom

      A : List (Fin H.nV)
      A = pe-stack (e ∷ e' ∷ []) sp
      B : List (Fin H.nV)
      B = pe-stack (e' ∷ e ∷ []) sp

      r₀ : A Perm.↭ B
      r₀ = RunInterchange.reshuffle RI₀

      run-eq₀
        : pe-term (e' ∷ e ∷ []) sp
          ≈Term permute-via-vlab H.vlab r₀ ∘ pe-term (e ∷ e' ∷ []) sp
      run-eq₀ = RunInterchange.run-eq RI₀

      -- Equivariance of the `qs`-tail on the two `↭`-related post-front
      -- stacks `A`, `B` (input permutation `↭-sym r₀ : B ↭ A`).
      equivar
        : Σ[ ρf ∈ pe-stack qs B Perm.↭ pe-stack qs A ]
            pe-term qs B
              ≈Term permute-via-vlab H.vlab (Perm.↭-sym ρf)
                      ∘ ( pe-term qs A
                          ∘ permute-via-vlab H.vlab (Perm.↭-sym r₀) )
      equivar = process-edges-equivariant qs {s = A} {s' = B} (Perm.↭-sym r₀)
                  (tail-reservoir ps qs e e' prov)

      ρf : pe-stack qs B Perm.↭ pe-stack qs A
      ρf = proj₁ equivar

      eqv
        : pe-term qs B
          ≈Term permute-via-vlab H.vlab (Perm.↭-sym ρf)
                  ∘ ( pe-term qs A
                      ∘ permute-via-vlab H.vlab (Perm.↭-sym r₀) )
      eqv = proj₂ equivar

      ----------------------------------------------------------------
      -- Prefix-split of the two runs, by DEFINITIONAL unfolding of
      -- `process-edges` on the concrete 2-edge prefix.  The two runs share
      -- the SAME stuck `edge-step` factors; the split is pure `assoc`/`idˡ`
      -- bookkeeping — NO `coe-cod`, NO `++-stack`.
      ----------------------------------------------------------------

      split₂
        : pe-term (e' ∷ e ∷ qs) sp
          ≈Term pe-term qs B ∘ pe-term (e' ∷ e ∷ []) sp
      split₂ =
        ≈-Term-trans assoc
          (∘-resp-≈ ≈-Term-refl (∘-resp-≈ (≈-Term-sym idˡ) ≈-Term-refl))

      split₁
        : pe-term qs A ∘ pe-term (e ∷ e' ∷ []) sp
          ≈Term pe-term (e ∷ e' ∷ qs) sp
      split₁ =
        ≈-Term-trans
          (∘-resp-≈ ≈-Term-refl (∘-resp-≈ idˡ ≈-Term-refl))
          (≈-Term-sym assoc)

      -- The run equation: split₂, feed eqv/run-eq₀, reassoc, collapse the
      -- inner inverse permute (pvv-inverse-left), re-glue via split₁.
      run-eq
        : pe-term (e' ∷ e ∷ qs) sp
          ≈Term permute-via-vlab H.vlab (Perm.↭-sym ρf)
                  ∘ pe-term (e ∷ e' ∷ qs) sp
      run-eq =
        ≈-Term-trans split₂
          (≈-Term-trans
            (∘-resp-≈ eqv run-eq₀)
            (≈-Term-trans
              reassoc
              (∘-resp-≈ ≈-Term-refl
                (≈-Term-trans
                  (∘-resp-≈ ≈-Term-refl
                    (≈-Term-trans
                      (∘-resp-≈ (pvv-inverse-left r₀) ≈-Term-refl)
                      idˡ))
                  split₁))))
        where
          reassoc
            : ( ( permute-via-vlab H.vlab (Perm.↭-sym ρf)
                    ∘ ( pe-term qs A
                        ∘ permute-via-vlab H.vlab (Perm.↭-sym r₀) ) )
                ∘ ( permute-via-vlab H.vlab r₀
                    ∘ pe-term (e ∷ e' ∷ []) sp ) )
              ≈Term
              ( permute-via-vlab H.vlab (Perm.↭-sym ρf)
                  ∘ ( pe-term qs A
                      ∘ ( ( permute-via-vlab H.vlab (Perm.↭-sym r₀)
                            ∘ permute-via-vlab H.vlab r₀ )
                          ∘ pe-term (e ∷ e' ∷ []) sp ) ) )
          reassoc =
            ≈-Term-trans assoc
              (∘-resp-≈ ≈-Term-refl
                (≈-Term-trans assoc
                  (∘-resp-≈ ≈-Term-refl
                    (≈-Term-sym assoc))))
