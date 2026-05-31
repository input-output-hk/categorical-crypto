{-# OPTIONS --without-K #-}

--------------------------------------------------------------------------------
-- TAIL-EXTENSION of the run-level interchange.
--
-- The `SwapStep.FrontSwap.RunInterchange` record packages the per-swap
-- interchange between the two post-front runs `pe-term (e ∷ e' ∷ qs) sp`
-- and `pe-term (e' ∷ e ∷ qs) sp` for an arbitrary suffix `qs`.  The
-- substantive content sits at the EMPTY tail (`qs := []`) — the genuine
-- two-edge Mac-Lane interchange of the two disjoint edge boxes.  Lifting
-- that empty-tail witness to an arbitrary `qs` is PURE decoder
-- equivariance under a stack permutation: running the (already-proven)
-- `qs`-suffix on the two `↭`-related post-front stacks differs only by an
-- input/output `permute`, with no box / associator content.
--
-- This module proves exactly that lift, `run-interchange-tail`, using
-- `StackEquivariance.process-edges-equivariant` (the decoder
-- stack-equivariance lemma).  It is generator-OPAQUE; its only residuals
-- are the two clearly-flagged StackEquivariance sub-lemmas
-- (`fire-mid-equivariant`, `fire-locate-coherent`), inherited transitively
-- — NOT closed here.
--
-- ## Statement
--
--   run-interchange-tail ps qs inc
--     : RunInterchange ps [] inc → RunInterchange ps qs inc
--
-- ## Derivation
--
-- Let `sp = pe-stack ps dom`, `A = pe-stack (e ∷ e' ∷ []) sp`,
-- `B = pe-stack (e' ∷ e ∷ []) sp`.  From the empty-tail witness:
--   r₀ : A ↭ B
--   run-eq₀ : pe-term (e' ∷ e ∷ []) sp ≈ permute r₀ ∘ pe-term (e ∷ e' ∷ []) sp
-- Apply `process-edges-equivariant qs (↭-sym r₀)` (with `s = A`, `s' = B`)
-- to get `ρf : pe-stack qs B ↭ pe-stack qs A` and
--   eqv : pe-term qs B ≈ permute (↭-sym ρf) ∘ (pe-term qs A ∘ permute (↭-sym r₀))
--
-- Because `e ∷ e' ∷ []` is a CONCRETE 2-prefix, `pe-stack qs A ≡
-- pe-stack (e ∷ e' ∷ qs) sp` and `pe-stack qs B ≡ pe-stack (e' ∷ e ∷ qs) sp`
-- DEFINITIONALLY (process-edges unfolds on the concrete cons prefix and
-- `[] ++ qs = qs`); so `↭-sym ρf : fs₁ ↭ fs₂` is the `reshuffle` field.
--
-- The run equation is assembled by splitting both runs with
-- `process-edges-++-≈` at the concrete 2-prefix, feeding `eqv` on the tail
-- and `run-eq₀` on the head, telescoping the inner inverse permute
-- (`pvv-inverse-right`) and re-associating; the `coe-cod` codomain
-- transports are handled by abstracting the (propositional) `++-stack`
-- equality and matching it at `refl`.
--------------------------------------------------------------------------------

open import Categories.APROP

module Categories.APROP.Hypergraph.Completeness.Discharge.Sub.RunInterchangeTail
  (sig : APROPSignature) where

open APROP sig

open import Categories.APROP.Hypergraph.Core using (Hypergraph)
open import Categories.APROP.Hypergraph.FromAPROP sig using (FlatGen)
open import Categories.APROP.Hypergraph.Completeness.Unflatten sig using (unflatten)
open import Categories.APROP.Hypergraph.Completeness.Permute sig
  using (permute-via-vlab)

import Categories.APROP.Hypergraph.Completeness.Discharge.SwapStep sig as SS
import Categories.APROP.Hypergraph.Completeness.Discharge.Sub.StackEquivariance sig as SE

open import Categories.APROP.Hypergraph.Completeness.Discharge.EdgeDependency
  using (Dep)

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
-- Per-hypergraph: fix `H`, `dih`, the Kelly residual `K`, and the
-- vertex-level codomain uniqueness `uniq-cod`, matching `FrontSwap`'s
-- parameters; open the `PerHG` plumbing and the `RunInterchange` record,
-- and the StackEquivariance lemmas at `(H , K)`.
------------------------------------------------------------------------

module _ (H : Hypergraph FlatGen)
         (dih : ∀ {e} → ¬ (Dep H e e))
         (K : FaithfulnessResidual)
         (uniq-cod : Unique (Hypergraph.cod H))
         where
  private module H = Hypergraph H
  open SS.PerHG H dih
    using (Order; Incomp; pe-stack; pe-term)
  open SS.FrontSwap H dih K uniq-cod using (RunInterchange)

  -- StackEquivariance lives in an ANONYMOUS `module _ (H) (K)`, so its
  -- members are top-level functions taking `H` and `K` explicitly; bind
  -- the two we need at the fixed `(H , K)`.
  process-edges-equivariant = SE.process-edges-equivariant H K
  pvv-inverse-left          = SE.pvv-inverse-left H K

  ----------------------------------------------------------------------
  -- The tail-extension lemma.
  ----------------------------------------------------------------------

  run-interchange-tail
    : ∀ (ps qs : Order) {e e' : Fin H.nE} (inc : Incomp e e')
    → RunInterchange ps [] inc
    → RunInterchange ps qs inc
  run-interchange-tail ps qs {e} {e'} inc RI₀ =
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

      -- run-eq₀ : pe-term (e' ∷ e ∷ []) sp
      --             ≈Term permute-via-vlab vlab r₀ ∘ pe-term (e ∷ e' ∷ []) sp
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
      -- `process-edges` on the concrete 2-edge prefix.  Writing
      -- `P = pe-term qs B`, `ta`/`t1` for the two inner edge terms:
      --
      --   pe-term (e' ∷ e ∷ qs) sp  ≡  (P ∘ ta) ∘ t1
      --   pe-term (e' ∷ e ∷ []) sp  ≡  (id ∘ ta) ∘ t1
      --
      -- with `B ≡ pe-stack (e' ∷ e ∷ []) sp` the post-2-prefix stack
      -- (definitionally `proj₁ (edge-step (proj₁ (edge-step sp e')) e)`).
      -- The two runs share the SAME stuck `edge-step` factors; the split
      -- is pure `assoc`/`idˡ` bookkeeping — NO `coe-cod`, NO `++-stack`.
      ----------------------------------------------------------------

      -- Split `pe-term (e' ∷ e ∷ qs) sp` over the concrete 2-prefix:
      --   (P ∘ ta) ∘ t1 ≈ P ∘ (ta ∘ t1) ≈ P ∘ ((id ∘ ta) ∘ t1).
      split₂
        : pe-term (e' ∷ e ∷ qs) sp
          ≈Term pe-term qs B ∘ pe-term (e' ∷ e ∷ []) sp
      split₂ =
        ≈-Term-trans assoc
          (∘-resp-≈ ≈-Term-refl (∘-resp-≈ (≈-Term-sym idˡ) ≈-Term-refl))

      -- Split `pe-term (e ∷ e' ∷ qs) sp` over the concrete 2-prefix:
      --   P' ∘ ((id ∘ ta') ∘ t1') ≈ P' ∘ (ta' ∘ t1') ≈ (P' ∘ ta') ∘ t1'.
      split₁
        : pe-term qs A ∘ pe-term (e ∷ e' ∷ []) sp
          ≈Term pe-term (e ∷ e' ∷ qs) sp
      split₁ =
        ≈-Term-trans
          (∘-resp-≈ ≈-Term-refl (∘-resp-≈ idˡ ≈-Term-refl))
          (≈-Term-sym assoc)

      ----------------------------------------------------------------
      -- The run equation.  Chain:
      --   pe-term (e' ∷ e ∷ qs) sp
      --     ≈ pe-term qs B ∘ pe-term (e' ∷ e ∷ []) sp                  [split₂]
      --     ≈ (permute(↭-sym ρf) ∘ (pe-term qs A ∘ permute(↭-sym r₀)))
      --         ∘ (permute r₀ ∘ pe-term (e ∷ e' ∷ []) sp)              [eqv, run-eq₀]
      --     ≈ permute(↭-sym ρf)
      --         ∘ (pe-term qs A ∘ ((permute(↭-sym r₀) ∘ permute r₀)
      --             ∘ pe-term (e ∷ e' ∷ []) sp))                       [assoc chase]
      --     ≈ permute(↭-sym ρf)
      --         ∘ (pe-term qs A ∘ pe-term (e ∷ e' ∷ []) sp)            [pvv-inv-right]
      --     ≈ permute(↭-sym ρf) ∘ pe-term (e ∷ e' ∷ qs) sp            [split₁]
      ----------------------------------------------------------------
      run-eq
        : pe-term (e' ∷ e ∷ qs) sp
          ≈Term permute-via-vlab H.vlab (Perm.↭-sym ρf)
                  ∘ pe-term (e ∷ e' ∷ qs) sp
      run-eq =
        ≈-Term-trans split₂
          (≈-Term-trans
            (∘-resp-≈ eqv run-eq₀)
            (≈-Term-trans
              -- ((P ∘ (Q ∘ I)) ∘ (J ∘ Kk)) ≈ P ∘ (Q ∘ ((I ∘ J) ∘ Kk))
              reassoc
              -- collapse the inner inverse permute and re-glue the split:
              --   Q ∘ ((I∘J) ∘ Kk) ≈ Q ∘ Kk ≈ pe-term (e ∷ e' ∷ qs) sp
              (∘-resp-≈ ≈-Term-refl
                (≈-Term-trans
                  (∘-resp-≈ ≈-Term-refl
                    (≈-Term-trans
                      (∘-resp-≈ (pvv-inverse-left r₀) ≈-Term-refl)
                      idˡ))
                  split₁))))
        where
          -- ((P ∘ (Q ∘ I)) ∘ (J ∘ Kk)) ≈Term P ∘ (Q ∘ ((I ∘ J) ∘ Kk))
          -- where P = permute(↭-sym ρf), Q = pe-term qs A,
          --       I = permute(↭-sym r₀), J = permute r₀,
          --       Kk = pe-term (e ∷ e' ∷ []) sp.
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
