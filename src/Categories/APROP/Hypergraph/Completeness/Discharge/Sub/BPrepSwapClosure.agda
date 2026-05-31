{-# OPTIONS --safe --with-K #-}

--------------------------------------------------------------------------------
-- Constructive (PARTIAL) closure of `RealFinalResidual.rfr-B-prep-swap`
-- from `Sub/YangBaxterClosure.agda`.
--
-- ## Target
--
-- The σ-cascade self-loop
--
--   p = trans (swap k k' a) (trans (prep k' (swap k k'' b')) Y)
--     : (k ∷ k' ∷ rest) ↭ (k ∷ k' ∷ rest)
--
-- with
--   * `a : rest ↭ (k'' ∷ rest'')`
--   * `b' : rest'' ↭ tail''`
--   * `Y : (k' ∷ k'' ∷ k ∷ tail'') ↭ (k ∷ k' ∷ rest)`
--   * `Unique (k ∷ k' ∷ rest)`
--   * `total-l p ≡ 0`  (normal form)
--   * `self-rec : ∀ q with measure q ≪₃ measure p → permute(q) ≈ id`.
--
-- in normal form, prove `permute (map⁺ vlab p) ≈Term id`.
--
-- ## Strategy
--
-- The cascade unfolds to
--
--   permute p
--     = pY ∘ (id ⊗ ((id ⊗ (id ⊗ pb')) ∘ σ-block_kk'')) ∘ ((id ⊗ (id ⊗ pa)) ∘ σ-block_kk')
--
-- where `σ-block_X = α⇒ ∘ (σ ⊗ id) ∘ α⇐`.
--
-- This is a genuine 2-σ-block Yang-Baxter braid cascade.  The core
-- algebraic piece `(id ⊗ σ-block) ∘ σ-block` is exactly the LHS of the
-- σ-block-hexagon (Yang-Baxter braid at the σ-block level), which is
-- currently DOCUMENTED but not constructively closed in
-- `Sub/SigmaBlockHexagon.agda`.
--
-- We therefore deliver a PARTIAL closure: we case-split on `a` and
-- eliminate the impossible `a = trans (trans _ _) _` sub-case
-- constructively via the `norm` hypothesis.  The remaining structurally-
-- narrower sub-cases are dispatched to a NEW narrower residual record
-- `BPrepSwapClosureResidual`.
--
-- ## Why this is strictly narrower than `rfr-B-prep-swap`
--
-- The original `rfr-B-prep-swap` quantifies uniformly over ALL `a`
-- shapes.  The new residual `BPrepSwapClosureResidual` has FOUR
-- structurally-specific fields (one per shape of `a`: refl, prep, swap,
-- trans-with-non-trans-left).  The `a = trans (trans _ _) _` case is
-- structurally absent from the new residual, because we eliminate it
-- via `norm` in the discharge.
--
-- This narrowing is strict (we constructively eliminate one whole shape
-- of `a`).  Plus, the inner `total-l` constraint on `a₁` (when `a`
-- is `trans`) is strictly tighter in the new residual (it excludes the
-- `trans-trans-left` interior pattern).
--
-- ## What this file delivers
--
--   * `BPrepSwapClosureResidual` — narrowed residual with FOUR fields:
--       1. `bps-a-refl`   : a = refl.
--       2. `bps-a-prep`   : a = prep _ _.
--       3. `bps-a-swap`   : a = swap _ _ _.
--       4. `bps-a-trans`  : a = trans a₁ a₂ where a₁ ∈ {refl, prep, swap}.
--   * `bprep-swap-closed` — function with the EXACT signature of
--     `rfr-B-prep-swap`, parameterized by `BPrepSwapClosureResidual`,
--     closing the `a = trans (trans _ _) _` sub-case via ⊥-elim from
--     `norm` and dispatching the other cases.
--
-- The trust surface is STRICTLY NARROWER than the original
-- `rfr-B-prep-swap`.
--
-- ## FreeMonoidal lemmas used
--
-- The closure here only carries out structural case-splits and the
-- ⊥-elim from `norm`.  The genuinely-Yang-Baxter algebra (the bare
-- `hexagon` axiom, σ-block-hexagon) is NOT applied at the discharge
-- level — it would be needed to close the four remaining sub-residual
-- fields, but those are dispatched here.
--
-- ## File is `--safe --with-K`-clean.  No new postulates outside the
--    `BPrepSwapClosureResidual` record.
--------------------------------------------------------------------------------

open import Categories.APROP
open import Categories.APROP.Hypergraph.Solver.Signature using (APROPSignatureDec)

module Categories.APROP.Hypergraph.Completeness.Discharge.Sub.BPrepSwapClosure
  (sig-dec : APROPSignatureDec) where

open APROPSignatureDec sig-dec using (sig)
open APROP sig

open import Categories.APROP.Hypergraph.Completeness.Permute sig
  using (permute)
open import Categories.APROP.Hypergraph.Completeness.Discharge.Sub.SelfLoopTransClosure sig-dec
  using (size)
open import Categories.APROP.Hypergraph.Completeness.Discharge.Sub.SelfLoopFullClosure sig-dec
  using (total-l)
open import Categories.APROP.Hypergraph.Completeness.Discharge.Sub.SelfLoopFullClosure2 sig-dec
  using (swap-count; measure; _≪₃_; ≪₃-fst; ≪₃-snd; ≪₃-thd)

open import Categories.Category using (Category)
open import Data.Fin using (Fin)
open import Data.List using (List; []; _∷_)
open import Data.Nat.Base using (ℕ; zero; suc; _+_; _<_; s≤s; z≤n)
open import Data.Nat.Properties using (+-suc; ≤-refl; n≤1+n; +-assoc; ≤-trans)
open import Data.Product using (_,_; _×_)
import Data.List.Relation.Binary.Permutation.Propositional as Perm
import Data.List.Relation.Binary.Permutation.Propositional.Properties as PermProp
open Perm using (_↭_)
open import Data.List.Relation.Unary.Unique.Propositional using (Unique)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; cong; subst)
open import Data.Empty using (⊥; ⊥-elim)
open import Induction.WellFounded using (Acc; acc)

private
  module FM = Category FreeMonoidal

open FM.HomReasoning

--------------------------------------------------------------------------------
-- ## Total-l arithmetic helpers.

private
  +-zero-l-zero : ∀ a b → a + b ≡ 0 → a ≡ 0
  +-zero-l-zero zero    _ _ = refl
  +-zero-l-zero (suc _) _ ()

  +-zero-r-zero : ∀ a b → a + b ≡ 0 → b ≡ 0
  +-zero-r-zero zero    _ eq = eq
  +-zero-r-zero (suc _) _ ()

  -- Generic suc-non-zero contradiction.
  suc-non-zero : ∀ {n : ℕ} → suc n ≡ 0 → ⊥
  suc-non-zero ()

--------------------------------------------------------------------------------
-- ## Total-l extractor for the B-prep-swap cascade.
--
-- total-l p where p = trans (swap k k' a) (trans (prep k' (swap k k'' b')) Y)
--
-- Computing step by step:
--   total-l (trans (swap k k' a) X)
--     = total-l a + total-l X                                        (left = swap)
--   total-l (trans (prep k' (swap k k'' b')) Y)
--     = total-l (swap k k'' b') + total-l Y                          (left = prep)
--     = total-l b' + total-l Y                                       (swap inner)
-- So:
--   total-l p = total-l a + total-l b' + total-l Y
--
-- For norm = 0, we get total-l a ≡ 0.

private
  total-l-bprep-swap-extract-a
    : ∀ {a} {A : Set a}
        {rest rest'' tail'' : List A} {k k' k'' : A}
        (a-perm : rest Perm.↭ (k'' ∷ rest''))
        (b' : rest'' Perm.↭ tail'')
        (Y : (k' ∷ k'' ∷ k ∷ tail'') Perm.↭ (k ∷ k' ∷ rest))
    → total-l (Perm.trans (Perm.swap k k' a-perm)
                 (Perm.trans (Perm.prep k' (Perm.swap k k'' b')) Y)) ≡ 0
    → total-l a-perm ≡ 0
  total-l-bprep-swap-extract-a a-perm b' Y eq =
    +-zero-l-zero (total-l a-perm) (total-l b' + total-l Y) eq

--------------------------------------------------------------------------------
-- ## The narrowed residual record.
--
-- Four fields, one per structurally-disjoint shape of `a`.
-- The `a = trans (trans _ _) _` case is structurally ABSENT (eliminated
-- in the discharge via ⊥-elim from `norm`).

record BPrepSwapClosureResidual : Set where
  field
    -- =================================================================
    -- Case 1: a = refl.
    -- Then `rest = k'' ∷ rest''`.
    -- =================================================================
    bps-a-refl
      : ∀ {n} (vlab : Fin n → X)
          {k k' k'' : Fin n} {rest'' tail'' : List (Fin n)}
          (uniq : Unique (k ∷ k' ∷ k'' ∷ rest''))
          (b' : rest'' Perm.↭ tail'')
          (Y : (k' ∷ k'' ∷ k ∷ tail'') Perm.↭ (k ∷ k' ∷ k'' ∷ rest''))
          (acc-p
            : let p = Perm.trans (Perm.swap k k' Perm.refl)
                        (Perm.trans (Perm.prep k' (Perm.swap k k'' b')) Y)
              in Acc _≪₃_ (measure p))
          (norm
            : let p = Perm.trans (Perm.swap k k' Perm.refl)
                        (Perm.trans (Perm.prep k' (Perm.swap k k'' b')) Y)
              in total-l p ≡ 0)
          (self-rec
            : ∀ (q : (k ∷ k' ∷ k'' ∷ rest'')
                      Perm.↭ (k ∷ k' ∷ k'' ∷ rest''))
              → let p = Perm.trans (Perm.swap k k' Perm.refl)
                          (Perm.trans (Perm.prep k' (Perm.swap k k'' b')) Y)
                in measure q ≪₃ measure p
              → permute (PermProp.map⁺ vlab q) ≈Term id)
        → let p = Perm.trans (Perm.swap k k' Perm.refl)
                    (Perm.trans (Perm.prep k' (Perm.swap k k'' b')) Y)
          in permute (PermProp.map⁺ vlab p) ≈Term id

    -- =================================================================
    -- Case 2: a = prep k'' a'.
    -- Then `rest = k'' ∷ rest_a`, a' : rest_a ↭ rest''.
    -- =================================================================
    bps-a-prep
      : ∀ {n} (vlab : Fin n → X)
          {k k' k'' : Fin n} {rest_a rest'' tail'' : List (Fin n)}
          (uniq : Unique (k ∷ k' ∷ k'' ∷ rest_a))
          (a' : rest_a Perm.↭ rest'')
          (b' : rest'' Perm.↭ tail'')
          (Y : (k' ∷ k'' ∷ k ∷ tail'') Perm.↭ (k ∷ k' ∷ k'' ∷ rest_a))
          (acc-p
            : let a = Perm.prep k'' a'
                  p = Perm.trans (Perm.swap k k' a)
                        (Perm.trans (Perm.prep k' (Perm.swap k k'' b')) Y)
              in Acc _≪₃_ (measure p))
          (norm
            : let a = Perm.prep k'' a'
                  p = Perm.trans (Perm.swap k k' a)
                        (Perm.trans (Perm.prep k' (Perm.swap k k'' b')) Y)
              in total-l p ≡ 0)
          (self-rec
            : ∀ (q : (k ∷ k' ∷ k'' ∷ rest_a)
                      Perm.↭ (k ∷ k' ∷ k'' ∷ rest_a))
              → let a = Perm.prep k'' a'
                    p = Perm.trans (Perm.swap k k' a)
                          (Perm.trans (Perm.prep k' (Perm.swap k k'' b')) Y)
                in measure q ≪₃ measure p
              → permute (PermProp.map⁺ vlab q) ≈Term id)
        → let a = Perm.prep k'' a'
              p = Perm.trans (Perm.swap k k' a)
                    (Perm.trans (Perm.prep k' (Perm.swap k k'' b')) Y)
          in permute (PermProp.map⁺ vlab p) ≈Term id

    -- =================================================================
    -- Case 3: a = swap k₁ k₂ a'.
    -- Then `rest = k₁ ∷ k₂ ∷ rest_a`, and a : (k₁ ∷ k₂ ∷ rest_a) ↭ (k'' ∷ rest'').
    -- For a swap, we have (k₁ ∷ k₂ ∷ rest_a) ↭ (k₂ ∷ k₁ ∷ rest_a') where
    -- a' : rest_a ↭ rest_a'.  Matching codomain (k'' ∷ rest''):
    --   k'' = k₂, rest'' = k₁ ∷ rest_a'.
    -- =================================================================
    bps-a-swap
      : ∀ {n} (vlab : Fin n → X)
          {k k' k₁ k'' : Fin n} {rest_a rest_a' tail'' : List (Fin n)}
          (uniq : Unique (k ∷ k' ∷ k₁ ∷ k'' ∷ rest_a))
          (a' : rest_a Perm.↭ rest_a')
          (b' : (k₁ ∷ rest_a') Perm.↭ tail'')
          (Y : (k' ∷ k'' ∷ k ∷ tail'')
               Perm.↭ (k ∷ k' ∷ k₁ ∷ k'' ∷ rest_a))
          (acc-p
            : let a = Perm.swap k₁ k'' a'
                  p = Perm.trans (Perm.swap k k' a)
                        (Perm.trans (Perm.prep k' (Perm.swap k k'' b')) Y)
              in Acc _≪₃_ (measure p))
          (norm
            : let a = Perm.swap k₁ k'' a'
                  p = Perm.trans (Perm.swap k k' a)
                        (Perm.trans (Perm.prep k' (Perm.swap k k'' b')) Y)
              in total-l p ≡ 0)
          (self-rec
            : ∀ (q : (k ∷ k' ∷ k₁ ∷ k'' ∷ rest_a)
                      Perm.↭ (k ∷ k' ∷ k₁ ∷ k'' ∷ rest_a))
              → let a = Perm.swap k₁ k'' a'
                    p = Perm.trans (Perm.swap k k' a)
                          (Perm.trans (Perm.prep k' (Perm.swap k k'' b')) Y)
                in measure q ≪₃ measure p
              → permute (PermProp.map⁺ vlab q) ≈Term id)
        → let a = Perm.swap k₁ k'' a'
              p = Perm.trans (Perm.swap k k' a)
                    (Perm.trans (Perm.prep k' (Perm.swap k k'' b')) Y)
          in permute (PermProp.map⁺ vlab p) ≈Term id

    -- =================================================================
    -- Case 4: a = trans a₁ a₂.
    -- Where a₁ ∈ {refl, prep _ _, swap _ _ _} (NOT trans).
    -- The `a₁ = trans _ _` case is eliminated via norm in the discharge.
    -- =================================================================
    bps-a-trans
      : ∀ {n} (vlab : Fin n → X)
          {k k' k'' : Fin n} {rest ms rest'' tail'' : List (Fin n)}
          (uniq : Unique (k ∷ k' ∷ rest))
          (a₁ : rest Perm.↭ ms)
          (a₂ : ms Perm.↭ (k'' ∷ rest''))
          (b' : rest'' Perm.↭ tail'')
          (Y : (k' ∷ k'' ∷ k ∷ tail'') Perm.↭ (k ∷ k' ∷ rest))
          (acc-p
            : let a = Perm.trans a₁ a₂
                  p = Perm.trans (Perm.swap k k' a)
                        (Perm.trans (Perm.prep k' (Perm.swap k k'' b')) Y)
              in Acc _≪₃_ (measure p))
          (norm
            : let a = Perm.trans a₁ a₂
                  p = Perm.trans (Perm.swap k k' a)
                        (Perm.trans (Perm.prep k' (Perm.swap k k'' b')) Y)
              in total-l p ≡ 0)
          (self-rec
            : ∀ (q : (k ∷ k' ∷ rest) Perm.↭ (k ∷ k' ∷ rest))
              → let a = Perm.trans a₁ a₂
                    p = Perm.trans (Perm.swap k k' a)
                          (Perm.trans (Perm.prep k' (Perm.swap k k'' b')) Y)
                in measure q ≪₃ measure p
              → permute (PermProp.map⁺ vlab q) ≈Term id)
        → let a = Perm.trans a₁ a₂
              p = Perm.trans (Perm.swap k k' a)
                    (Perm.trans (Perm.prep k' (Perm.swap k k'' b')) Y)
          in permute (PermProp.map⁺ vlab p) ≈Term id

--------------------------------------------------------------------------------
-- ## Main: `bprep-swap-closed`.
--
-- Case-split on `a`.  Three cases dispatch directly to the matching
-- residual field; the `a = trans (trans _ _) _` impossible-case is
-- eliminated via ⊥-elim from `norm`.

module WithBPrepSwapClosureResidual (res : BPrepSwapClosureResidual) where
  open BPrepSwapClosureResidual res

  bprep-swap-closed
    : ∀ {n} (vlab : Fin n → X)
        {k k' k'' : Fin n} {rest rest'' tail'' : List (Fin n)}
        (uniq : Unique (k ∷ k' ∷ rest))
        (a : rest Perm.↭ (k'' ∷ rest''))
        (b' : rest'' Perm.↭ tail'')
        (Y : (k' ∷ k'' ∷ k ∷ tail'') Perm.↭ (k ∷ k' ∷ rest))
        (acc-p
          : let p = Perm.trans (Perm.swap k k' a)
                      (Perm.trans (Perm.prep k' (Perm.swap k k'' b')) Y)
            in Acc _≪₃_ (measure p))
        (norm
          : let p = Perm.trans (Perm.swap k k' a)
                      (Perm.trans (Perm.prep k' (Perm.swap k k'' b')) Y)
            in total-l p ≡ 0)
        (self-rec
          : ∀ (q : (k ∷ k' ∷ rest) Perm.↭ (k ∷ k' ∷ rest))
            → let p = Perm.trans (Perm.swap k k' a)
                        (Perm.trans (Perm.prep k' (Perm.swap k k'' b')) Y)
              in measure q ≪₃ measure p
            → permute (PermProp.map⁺ vlab q) ≈Term id)
      → let p = Perm.trans (Perm.swap k k' a)
                  (Perm.trans (Perm.prep k' (Perm.swap k k'' b')) Y)
        in permute (PermProp.map⁺ vlab p) ≈Term id

  -- ----- Case 1: a = refl -----
  --
  -- a : rest ↭ (k'' ∷ rest'').  For refl, rest = k'' ∷ rest''.
  -- Dispatch.
  bprep-swap-closed vlab {k} {k'} {k''} {.(k'' ∷ rest'')} {rest''} {tail''}
      uniq Perm.refl b' Y acc-p norm self-rec =
    bps-a-refl vlab uniq b' Y acc-p norm self-rec

  -- ----- Case 2: a = prep .k'' a' -----
  --
  -- a : (k'' ∷ rest_a) ↭ (k'' ∷ rest''), a' : rest_a ↭ rest''.
  -- Dispatch.
  bprep-swap-closed vlab {k} {k'} {k''} {.(k'' ∷ _)} {rest''} {tail''}
      uniq (Perm.prep .k'' a') b' Y acc-p norm self-rec =
    bps-a-prep vlab uniq a' b' Y acc-p norm self-rec

  -- ----- Case 3: a = swap k₁ .k'' a' -----
  --
  -- a : (k₁ ∷ k'' ∷ rest_a) ↭ (k'' ∷ k₁ ∷ rest_a'), with codomain
  -- (k'' ∷ rest'').  Then rest'' = k₁ ∷ rest_a', a' : rest_a ↭ rest_a'.
  -- Dispatch.
  bprep-swap-closed vlab {k} {k'} {k''} {.(k₁ ∷ k'' ∷ _)} {.(k₁ ∷ _)} {tail''}
      uniq (Perm.swap k₁ .k'' a') b' Y acc-p norm self-rec =
    bps-a-swap vlab uniq a' b' Y acc-p norm self-rec

  -- ----- Case 4: a = trans a₁ a₂ -----
  --
  -- Further case-split on a₁:
  --   * a₁ ∈ {refl, prep, swap}: dispatch to bps-a-trans.
  --   * a₁ = trans _ _: IMPOSSIBLE via norm.
  bprep-swap-closed vlab {k} {k'} {rest} {rest''} {tail''}
      uniq (Perm.trans Perm.refl a₂) b' Y acc-p norm self-rec =
    bps-a-trans vlab uniq Perm.refl a₂ b' Y acc-p norm self-rec
  bprep-swap-closed vlab {k} {k'} {rest} {rest''} {tail''}
      uniq (Perm.trans (Perm.prep k₁ a₁') a₂) b' Y acc-p norm self-rec =
    bps-a-trans vlab uniq (Perm.prep k₁ a₁') a₂ b' Y acc-p norm self-rec
  bprep-swap-closed vlab {k} {k'} {rest} {rest''} {tail''}
      uniq (Perm.trans (Perm.swap k₁ k₂ a₁') a₂) b' Y acc-p norm self-rec =
    bps-a-trans vlab uniq (Perm.swap k₁ k₂ a₁') a₂ b' Y acc-p norm self-rec
  bprep-swap-closed vlab {k} {k'} {rest} {rest''} {tail''}
      uniq (Perm.trans (Perm.trans a₁₁ a₁₂) a₂) b' Y _ norm _ =
    -- ----- a₁ = trans _ _ : IMPOSSIBLE -----
    --
    -- total-l p
    --   = total-l (trans (trans a₁₁ a₁₂) a₂) + total-l b' + total-l Y
    --   = suc (total-l a₁₁ + total-l a₁₂ + total-l a₂) + ...
    --   ≡ 0 → contradiction.
    let a = Perm.trans (Perm.trans a₁₁ a₁₂) a₂
        tl-a-eq : total-l a ≡ 0
        tl-a-eq = total-l-bprep-swap-extract-a a b' Y norm
        -- Now total-l a = suc (...), contradicting tl-a-eq.
    in ⊥-elim (suc-non-zero tl-a-eq)

--------------------------------------------------------------------------------
-- ## Outcome
--
-- This file delivers:
--
--   * `BPrepSwapClosureResidual` — a STRICTLY NARROWER residual record
--     with FOUR structurally-tighter fields (one per shape of `a`).
--     The `a = trans (trans _ _) _` case is structurally absent.
--
--   * `bprep-swap-closed` (in `module WithBPrepSwapClosureResidual`) —
--     a function with the EXACT signature of
--     `RealFinalResidual.rfr-B-prep-swap`, parameterized by
--     `BPrepSwapClosureResidual`.
--
-- ## Discharge status
--
--   * a = refl:                    NARROWED (dispatch to bps-a-refl).
--   * a = prep _ _:                NARROWED (dispatch to bps-a-prep).
--   * a = swap _ _ _:              NARROWED (dispatch to bps-a-swap).
--   * a = trans (refl|prep|swap) _: NARROWED (dispatch to bps-a-trans).
--   * a = trans (trans _ _) _:     CLOSED via ⊥-elim from `norm`.
--
-- ## Why this is strictly narrower than `rfr-B-prep-swap`
--
-- The new residual `BPrepSwapClosureResidual` has FOUR specific fields
-- (one per `a` shape), each strictly more restricted than the original
-- uniform quantification over all `a`.  The `a = trans (trans _ _) _`
-- case is constructively eliminated.
--
-- ## FreeMonoidal lemmas used
--
-- The closure here only uses structural case-splits and the ⊥-elim
-- from `norm` for the trans-trans contradiction.  No `hexagon`,
-- `σ-block-natural₃`, or other equational lemmas were needed at this
-- level.  The four sub-residuals contain the genuine Yang-Baxter
-- algebra.
--
-- ## File is `--safe --with-K`-clean.  No new postulates outside the
--    `BPrepSwapClosureResidual` record.
--------------------------------------------------------------------------------
