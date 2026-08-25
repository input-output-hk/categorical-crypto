{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- STRICT TAIL-EXTENSION of the run-level interchange.
--
-- The substantive content of the `RunInterchangeˢ` record sits at the EMPTY
-- tail (the two-edge interchange, `SwapCoreRun.run-interchange₀ˢ`); lifting
-- it to an arbitrary suffix `qs` is PURE decoder equivariance under a stack
-- permutation: the `qs`-suffix on the two `↭`-related post-front stacks
-- differs only by an input/output `permuteˢ`, with NO box content.
--
-- This module:
--   * defines the strict `RunInterchangeˢ` record (the (N) residual the
--     strict `swap-≈ˢ` consumes);
--   * proves `run-interchange-tailˢ : RunInterchangeˢ ps [] → RunInterchangeˢ
--     ps qs` via `StackEquiv.process-edges-equivariantˢ`.
--
-- Because `e' ∷ e ∷ []` is a CONCRETE 2-prefix, `pe-stackˢ qs A ≡ pe-stackˢ
-- (e ∷ e' ∷ qs) sp` etc. hold DEFINITIONALLY (`process-edgesˢ` recurses on the
-- prefix), so `↭-sym ρf` is the `reshuffle` field; the run equation splits
-- both runs at the 2-prefix, feeds `eqv`/`run-eq₀`, telescopes the inner
-- inverse permute (`pvv-inverse-leftˢ`), and re-associates — a 1:1 port of the
-- non-strict plumbing, the Mac-Lane `permute-via-vlab` collapsing to the
-- vertex-level `permuteˢ`.
--------------------------------------------------------------------------------

open import Categories.APROP
open import Relation.Binary using (DecidableEquality)

module Categories.APROP.Hypergraph.Soundness.Strict.Interchange.RunInterchangeTail
  (sig : APROPSignature)
  (_≟X_ : DecidableEquality (APROPSignature.X sig))
  where

open import Categories.APROP.Hypergraph.Model.Core using (Hypergraph)
open import Categories.APROP.Hypergraph.Model.FromAPROP sig using (FlatGen; range)
open import Categories.APROP.Hypergraph.Soundness.Linearity.Linearity sig using (Linear)

open import Categories.APROP.Hypergraph.Soundness.Strict.Decode.Decoder sig _≟X_
open import Categories.Morphism.Reasoning SCat using (pullʳ)
open import Categories.APROP.Hypergraph.Soundness.Strict.Interchange.StackEquiv sig _≟X_
  using (module EquivStep)
import Categories.APROP.Hypergraph.Soundness.Strict.Interchange.SwapCore sig _≟X_ as SC

import Categories.APROP.Hypergraph.Soundness.Stack.StackUniqueReach sig
  as SUR

open import Data.Fin using (Fin)
open import Data.List using (List; []; _∷_; _++_)
open import Data.Product using (Σ-syntax; proj₁; proj₂)
import Data.List.Relation.Binary.Permutation.Propositional as Perm
open import Relation.Binary.PropositionalEquality
  using (_≡_; sym; trans; cong; subst)

------------------------------------------------------------------------
-- Per-hypergraph: fix `H`, `lin`.
------------------------------------------------------------------------

module _ (H : Hypergraph FlatGen)
         (lin : Linear H)
         where
  private module H = Hypergraph H

  open EquivStep H
    using ( permuteˢ; pe-stackˢ; pe-termˢ; process-edges-equivariantˢ
          ; pvv-inverse-leftˢ; stacks-agree )

  -- `Incomp` from `SwapCore` (so the record matches the `run-interchange₀ˢ`
  -- consumer).
  Incompˢ = SC.Incomp H

  ----------------------------------------------------------------------
  -- The strict (N) residual record — consumed as the `RI` argument of
  -- `SwapStep.FrontSwap`.
  -- `reshuffle` between the two post-front stacks; `run-eq` is the (N)
  -- run-level interchange equation, at the VERTEX-level `permuteˢ`.
  ----------------------------------------------------------------------

  record RunInterchangeˢ (ps qs : List (Fin H.nE)) {e e' : Fin H.nE}
                         (inc : Incompˢ e e') : Set where
    private
      sp  = pe-stackˢ ps H.dom
      fs₁ = pe-stackˢ (e ∷ e' ∷ qs) sp
      fs₂ = pe-stackˢ (e' ∷ e ∷ qs) sp
    field
      reshuffle : fs₁ Perm.↭ fs₂
      run-eq
        : pe-termˢ (e' ∷ e ∷ qs) sp
          ≈ˢ permuteˢ reshuffle ∘ˢ pe-termˢ (e ∷ e' ∷ qs) sp

  ----------------------------------------------------------------------
  -- ## Sourcing the running-stack freshness invariant `Reservoir≤1`.
  --
  -- `process-edges-equivariantˢ` needs a `Reservoir≤1 H qs B` freshness
  -- invariant on the permuted tail-input stack `B = pe-stackˢ (e'∷e∷[]) sp`.
  -- We descend it from the GLOBAL reservoir on `H.dom` over the combined
  -- order — the *bound* half of `Linear H` specialised to that order
  -- (`dom-reservoir-prov`), TRUE because the order is a PERMUTATION of
  -- `range nE`.  `reservoir-split` is term-free; its codomain is the
  -- NON-strict stack `(process-edges …)`, which is propositionally
  -- equal to the strict `pe-stackˢ` (`pe-stackˢ ≡ proj₁ process-edges` by
  -- definition of the strict run — both branch on the same `extract-prefix`).
  ----------------------------------------------------------------------

  -- `pe-stackˢ` IS `(process-edges …)` definitionally?  No — they walk
  -- the same `extract-prefix` calls but the strict `pe-stackˢ` is from
  -- `process-edgesˢ`.  Bridge propositionally via `stacks-agree` (above).

  open import Categories.APROP.Hypergraph.Soundness.Decode.Decode sig using (process-edges)

  tail-reservoir
    : ∀ (ps qs : List (Fin H.nE)) (e e' : Fin H.nE)
    → (ps ++ e' ∷ e ∷ qs) Perm.↭ range H.nE
    → SUR.Reservoir≤1 H qs (pe-stackˢ (e' ∷ e ∷ []) (pe-stackˢ ps H.dom))
  tail-reservoir ps qs e e' prov =
    subst (SUR.Reservoir≤1 H qs) (sym bridge) res-ns
    where
      sp = pe-stackˢ ps H.dom

      -- the non-strict split-reservoir at the non-strict 2-prefix stack
      res-ns
        : SUR.Reservoir≤1 H qs
            ((process-edges H (e' ∷ e ∷ []) ((process-edges H ps H.dom))))
      res-ns =
        SUR.reservoir-split H (e' ∷ e ∷ []) qs ((process-edges H ps H.dom))
          (SUR.reservoir-split H ps (e' ∷ e ∷ qs) H.dom
            (SUR.dom-reservoir-prov H (proj₂ lin) (ps ++ e' ∷ e ∷ qs) prov))

      -- `pe-stackˢ (e'∷e∷[]) sp ≡ (process-edges H (e'∷e∷[]) (proj₁ …))`
      bridge
        : pe-stackˢ (e' ∷ e ∷ []) sp
          ≡ (process-edges H (e' ∷ e ∷ []) ((process-edges H ps H.dom)))
      bridge =
        trans (stacks-agree (e' ∷ e ∷ []) sp)
              (cong (λ z → (process-edges H (e' ∷ e ∷ []) z))
                    (stacks-agree ps H.dom))

  ----------------------------------------------------------------------
  -- The tail-extension lemma.
  ----------------------------------------------------------------------

  run-interchange-tailˢ
    : ∀ (ps qs : List (Fin H.nE)) {e e' : Fin H.nE} (inc : Incompˢ e e')
    → (ps ++ e' ∷ e ∷ qs) Perm.↭ range H.nE
    → RunInterchangeˢ ps [] inc
    → RunInterchangeˢ ps qs inc
  run-interchange-tailˢ ps qs {e} {e'} inc prov RI₀ =
    record { reshuffle = Perm.↭-sym ρf ; run-eq = run-eq }
    where
      sp : List (Fin H.nV)
      sp = pe-stackˢ ps H.dom

      A : List (Fin H.nV)
      A = pe-stackˢ (e ∷ e' ∷ []) sp
      B : List (Fin H.nV)
      B = pe-stackˢ (e' ∷ e ∷ []) sp

      r₀ : A Perm.↭ B
      r₀ = RunInterchangeˢ.reshuffle RI₀

      run-eq₀ : pe-termˢ (e' ∷ e ∷ []) sp ≈ˢ permuteˢ r₀ ∘ˢ pe-termˢ (e ∷ e' ∷ []) sp
      run-eq₀ = RunInterchangeˢ.run-eq RI₀

      equivar
        : Σ[ ρf ∈ pe-stackˢ qs B Perm.↭ pe-stackˢ qs A ]
            pe-termˢ qs B
              ≈ˢ permuteˢ (Perm.↭-sym ρf)
                    ∘ˢ ( pe-termˢ qs A ∘ˢ permuteˢ (Perm.↭-sym r₀) )
      equivar =
        process-edges-equivariantˢ qs {s = A} {s' = B} (Perm.↭-sym r₀)
          (tail-reservoir ps qs e e' prov)

      ρf : pe-stackˢ qs B Perm.↭ pe-stackˢ qs A
      ρf = proj₁ equivar

      eqv
        : pe-termˢ qs B
          ≈ˢ permuteˢ (Perm.↭-sym ρf)
                ∘ˢ ( pe-termˢ qs A ∘ˢ permuteˢ (Perm.↭-sym r₀) )
      eqv = proj₂ equivar

      ----------------------------------------------------------------
      -- Prefix-split of the two runs, by DEFINITIONAL unfolding of
      -- `process-edgesˢ` on the concrete 2-edge prefix.  Both runs share
      -- the SAME 2-prefix `edge-stepˢ` factors; pure `assocˢ`/`idˡ`
      -- bookkeeping.
      ----------------------------------------------------------------

      split₂ : pe-termˢ (e' ∷ e ∷ qs) sp ≈ˢ pe-termˢ qs B ∘ˢ pe-termˢ (e' ∷ e ∷ []) sp
      split₂ = pullʳ (∘-resp (≈-sym idˡ) ≈-refl)

      split₁ : pe-termˢ qs A ∘ˢ pe-termˢ (e ∷ e' ∷ []) sp ≈ˢ pe-termˢ (e ∷ e' ∷ qs) sp
      split₁ = ≈-trans (∘-resp ≈-refl (∘-resp idˡ ≈-refl)) (≈-sym assocˢ)

      run-eq
        : pe-termˢ (e' ∷ e ∷ qs) sp
          ≈ˢ permuteˢ (Perm.↭-sym ρf) ∘ˢ pe-termˢ (e ∷ e' ∷ qs) sp
      run-eq =
        ≈-trans split₂
          (≈-trans
            (∘-resp eqv run-eq₀)
            (≈-trans
              -- reassociate into `… ∘ˢ (… ∘ˢ ((p⁻¹ ∘ˢ p) ∘ˢ …))`; both
              -- endpoints are pinned by the neighbouring steps.
              (pullʳ (pullʳ (≈-sym assocˢ)))
              (∘-resp ≈-refl
                (≈-trans
                  (∘-resp ≈-refl
                    (≈-trans
                      (∘-resp (pvv-inverse-leftˢ r₀) ≈-refl)
                      idˡ))
                  split₁))))
